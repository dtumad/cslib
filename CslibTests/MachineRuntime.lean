/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Sampling
import Cslib.Computability.PolynomialTime.Sampling.Rejection
import Cslib.Computability.PolynomialTime.Composition
import Cslib.Computability.PolynomialTime.List
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Resumption
import Cslib.Crypto.RandomOracle

/-! Machine-level checks for clock boundaries and shared adaptive communication. -/

open Turing Turing.MultiTapePTM Turing.MultiTapeTM PFunctor

namespace MachineRuntime

local instance : MeasurableSpace Word := ⊤

def savedBits : (op : (effects Empty).A) → StateT Word Id ((effects Empty).B op)
  | .inl _ => fun bits => (bits.headD false, bits.tail)
  | .inr (oracle, _) => oracle.elim

def sample (fuel bits : ℕ) (coins : Word) : Option Word × Word :=
  Id.run (((uniformBitsMachine.run fuel (parameterInput bits [])).liftM savedBits).run coins)

-- Delimiter recognition consumes one transition. Exhaustion does not expose a partial output.
example : sample 0 0 [true] = (none, [true]) := by decide
example : sample 1 0 [true] = (some [], []) := by decide
example : sample 2 2 [true, false, true] = (none, [true]) := by decide
example : sample 3 2 [true, false, true] = (some [true, false], []) := by decide

-- Padding after termination consumes no extra coins.
example : sample 10 2 [true, false, true, false] = (some [true, false], [false]) := by decide

example : IsPPT (Oracle := Empty) parameterEncoding wordEncoding
    (fun input => (List.replicate input.1 ()).mapM (fun _ => coin)) := isPPT_sampleBits

-- The loop certificate supplies one machine across unbounded input lengths.
example : IsPolyTime wordEncoding (fun word => word.reverse ++ word) :=
  (isPolyTime_input wordEncoding).reverse.append (isPolyTime_input wordEncoding)

-- One machine handles binary ranges of unbounded size and every unary retry budget.
example : IsPPT (Oracle := Empty) (pairEncoding binaryEncoding unaryEncoding)
    (optionEncoding binaryEncoding) (fun input => Option.map Fin.val <$>
      FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
        input.1 input.1.size input.2) :=
  isPPT_sampleFin_size (isPolyTime_fst _ _) (isPolyTime_snd _ _)

-- Reject 3, then accept 1; proposal bits are read in sampling order.
example : selectBelow 3 2 2 [true, true, false, true] = some 1 := by decide
example : selectBelow 3 2 1 [true, true, false, true] = none := by decide
-- Successful zero and exhausted rejection have different encodings.
example : selectBelow 1 1 1 [false] = some 0 := by decide
example : selectBelow 1 1 1 [true] = none := by decide
example : optionEncoding binaryEncoding (some 0) ≠ optionEncoding binaryEncoding none := by decide

-- Sampling followed by a bounded deterministic loop receives one uniform machine certificate.
example : IsPPT (Oracle := Empty) parameterEncoding wordEncoding (fun input =>
    (fun bits : Word => bits.reverse ++ bits) <$>
      (List.replicate input.1 ()).mapM (fun _ => coin)) :=
  isPPT_sampleBits.map
    ((isPolyTime_input wordEncoding).reverse.append (isPolyTime_input wordEncoding))

/-- The first answer chooses the payload of the next two calls, through distinct operation names. -/
def adaptiveMachine : MultiTapePTM 0 Bool (Fin 5) Bool where
  initial := 0
  tr state _ _ answers _ := match state.val with
    | 0 => .query false 1
    | 1 => .step ⟨0, Fin.elim0, none, some 2⟩ (fun _ => answers false) (fun _ => 0)
    | 2 => .query true 3
    | 3 => .query false 4
    | _ => .step ⟨0, Fin.elim0, some (answers false == answers true), none⟩
      (fun _ => none) (fun _ => 0)

abbrev Cache := List (Word × Bool)
abbrev Log := List (Bool × Word)

-- Both operation names use exactly the same cache. Misses alternate their deterministic test bit.
def cached (oracle : Bool) (word : Word) : StateT (Cache × Log) Id Word := fun state =>
  let (answer, cache) := Cslib.Crypto.RandomOracle.query
    (pure (state.1.length % 2 == 1) : Id Bool) word state.1
  ([answer], (cache, state.2 ++ [(oracle, word)]))

def adaptiveResult (coins : Word) : Option Word × (Cache × Log) :=
  let (cfg, state) := (adaptiveMachine.runConfigFromCoins cached coins
    (adaptiveMachine.initialConfig [])).run ([], [])
  (output? cfg, state)

example : adaptiveResult [false, true, false, true] =
  (none, ([([false], true), ([], false)],
    [(false, []), (true, [false]), (false, [false])])) := by decide
example : adaptiveResult [false, true, false, true, false] =
  (some [true], ([([false], true), ([], false)],
    [(false, []), (true, [false]), (false, [false])])) := by decide

-- Resuming retains the cache and call log, without repeating calls from the prefix.
example (before after : Word) :
    adaptiveMachine.runConfigFromCoins cached (before ++ after)
        (adaptiveMachine.initialConfig []) =
      (adaptiveMachine.runConfigFromCoins cached before (adaptiveMachine.initialConfig []) >>=
        adaptiveMachine.runConfigFromCoins cached after) :=
  runConfigFromCoins_append _ _ _ _ _

-- Lookup is certified across unbounded encoded caches, including keys with empty encodings.
example : IsPolyTime
    (pairEncoding wordEncoding (listEncoding (pairEncoding wordEncoding boolEncoding)))
    (fun pair => optionEncoding boolEncoding (pair.2.lookup pair.1)) :=
  (isPolyTime_fst _ _).list_lookup (isPolyTime_snd _ _)

-- The source deliberately leaves a pending request when it halts. That buffer must remain
-- separate from the continuation's fresh port, while both calls still share one cache.
def bufferedSource : MultiTapePTM 0 Bool (Fin 2) (Fin 1) where
  initial := 0
  tr state _ _ answer _ := if state = 0 then .query 0 1 else
    .step ⟨0, Fin.elim0, some ((answer 0).getD false), none⟩
      (fun _ => some true) (fun _ => 0)

def bufferedConsumer : MultiTapePTM 0 Bool (Fin 3) (Fin 1) where
  initial := 0
  tr state symbol _ answer _ := match state.val with
    | 0 => .step ⟨0, Fin.elim0, none, some 1⟩ (fun _ => symbol) (fun _ => 0)
    | 1 => .query 0 2
    | _ => .step ⟨0, Fin.elim0, some ((answer 0).getD false), none⟩
      (fun _ => none) (fun _ => 0)

def composedResult (fuel : ℕ) : Option Word × (Cache × Log) :=
  let machine := bufferedSource.comp bufferedConsumer
  let (cfg, state) := (machine.runConfigFromCoins (fun port => cached (port.val == 1))
    (List.replicate fuel false) (machine.initialConfig [])).run ([], [])
  (output? cfg, state)

section

set_option linter.hashCommand false

#guard composedResult 9 ==
  (none, ([([false], true), ([], false)], [(false, []), (true, [false])]))
#guard composedResult 10 ==
  (some [true], ([([false], true), ([], false)], [(false, []), (true, [false])]))

end

end MachineRuntime
