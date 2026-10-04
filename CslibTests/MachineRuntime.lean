/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Sampling
import Cslib.Computability.PolynomialTime.List
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
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

end MachineRuntime
