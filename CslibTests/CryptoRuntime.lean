/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.PolynomialTime
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Signing
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Simulation
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Verification
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Execution
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.TracedExecution
import Cslib.Crypto.RandomOracle.PolynomialTime
import Cslib.Computability.PolynomialTime.Finite
import Cslib.Computability.PolynomialTime.Encoding.Decoding
import Cslib.Computability.PolynomialTime.Realizer.Decoding
import Cslib.Computability.PolynomialTime.Realizer.Encoding
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Order

/-! Instantiate the primitive boundary in a fixed small group, with an unbounded unary retry
budget and binary exponents. Finite tables implement only this fixed group's operations. -/

open Turing.MultiTapeTM Turing.MultiTapePTM PFunctor Cslib.Crypto

namespace CryptoRuntime

-- Mathlib's permissive decoder remains available; interfaces check canonical representations.
example : Computability.encodingBoolBool.decode [true, false] = some true := rfl

example : Computability.encodingBoolBool.decodeChecked [true, false] = none := by decide

-- Pair parsers may ignore malformed tails. Checked decoding rejects these instead of silently
-- turning an invalid oracle message into a valid pair of empty words.
example : ((Computability.encodingList Bool).bitPair
    (Computability.encodingList Bool)).decodeChecked [true] = none := by decide

example : IsPolyTime wordEncoding (fun word =>
    let encoding := (Computability.encodingList Bool).bitPair (Computability.encodingList Bool)
    optionEncoding encoding.toEmbedding (encoding.decodeChecked word)) := by
  apply IsPolyTime.decodeChecked
  exact IsPolyTime.decode_bitPair _ _ (isPolyTime_input wordEncoding).option_some
    (isPolyTime_input wordEncoding).option_some

-- A failed parse differs from a valid optional result whose value is absent.
example : Computability.encodingBoolBool.bitOption.decodeChecked [] = some none := by decide
example : Computability.encodingBoolBool.bitOption.decodeChecked [true, true] =
    some (some true) := by decide
example : Computability.encodingBoolBool.bitOption.decodeChecked [false] = none := by decide
example : Computability.encodingBoolBool.bitOption.decodeChecked [true, true, false] =
    none := by decide

-- Scalar parsing rejects both out-of-range indices and redundant high zero bits.
example : (Computability.Encoding.finEquiv (Equiv.refl (Fin 3))).decodeChecked [true, true] =
    none := by decide
example : (Computability.Encoding.finEquiv (Equiv.refl (Fin 3))).decode [true, false] =
    some 1 := by decide
example : (Computability.Encoding.finEquiv (Equiv.refl (Fin 3))).decodeChecked [true, false] =
    none := by decide

-- There is no fallback value available for an empty represented type.
example : IsPolyTime wordEncoding (fun word => optionEncoding (finBinaryEncoding 0)
    ((Computability.Encoding.finEquiv (Equiv.refl (Fin 0))).decodeChecked word)) := by
  apply IsPolyTime.decodeChecked_indexed (parameter := fun _ => ())
    (fun _ => Computability.Encoding.finEquiv (Equiv.refl (Fin 0)))
    (isPolyTime_input wordEncoding)
  exact IsPolyTime.decode_finEquiv (parameter := fun _ => ())
    (fun _ => Equiv.refl (Fin 0)) (isPolyTime_const _ []) (isPolyTime_input wordEncoding)

namespace TypedOracle

abbrev requests : PFunctor := .mk Bool (fun _ => Bool)

def program : (PFunctor.mk Unit (fun _ => Bool) + requests).FreeM Bool := do
  let bit ← FreeM.lift (P := PFunctor.mk Unit (fun _ => Bool) + requests) (.inl ())
  let answer ← FreeM.lift (P := PFunctor.mk Unit (fun _ => Bool) + requests) (.inr bit)
  FreeM.lift (P := PFunctor.mk Unit (fun _ => Bool) + requests) (.inr answer)

def replies (word : Word) : (op : (effects Unit).A) → StateM ℕ ((effects Unit).B op)
  | .inl _ => pure false
  | .inr _ => do
    modify (· + 1)
    pure word

-- Rejecting a malformed first reply stops the adaptive second query.
example : (((program.liftM (encodeEffects (P := requests) Computability.encodingBoolBool
    (fun _ => Computability.encodingBoolBool))).run).liftM
      (m := StateM ℕ) (replies [true, false])).run 0 = (none, 1) := rfl

example : (((program.liftM (encodeEffects (P := requests) Computability.encodingBoolBool
    (fun _ => Computability.encodingBoolBool))).run).liftM
      (m := StateM ℕ) (replies [true])).run 0 = (some true, 2) := rfl

def typedReply (bit : requests.A) : StateM ℕ (requests.B bit) := do
  modify (· + 1)
  pure (!bit)

-- An invalid request is rejected before it can modify the typed oracle's shared state.
example : ((decodeQuery (P := requests) (m := StateM ℕ) Computability.encodingBoolBool
    (fun _ => Computability.encodingBoolBool) typedReply [true, false]).run).run 0 =
      (none, 0) := rfl

example : ((decodeQuery (P := requests) (m := StateM ℕ) Computability.encodingBoolBool
    (fun _ => Computability.encodingBoolBool) typedReply [true]).run).run 0 =
      (some [false], 1) := rfl

end TypedOracle

abbrev G := Multiplicative (ZMod 2)

noncomputable def code : G ↪ Word := finiteEncoding G

def generator : G := Multiplicative.ofAdd 1

local instance : MeasurableSpace Word := ⊤

theorem mul_poly : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code))
    (fun value => code (value.2.1 * value.2.2)) :=
  (isPolyTime_of_finite (pairEncoding code code) (fun pair => code (pair.1 * pair.2))).comp_encoded
    (isPolyTime_input (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code))).sigma_snd

theorem inv_poly : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => code))
    (fun value => code value.2⁻¹) :=
  (isPolyTime_of_finite code (fun value => code value⁻¹)).comp_encoded
    (isPolyTime_input (sigmaEncoding unaryEncoding (fun _ => code))).sigma_snd

theorem attempts_poly : IsPolyTime unaryEncoding (fun n => unaryEncoding (n + 1)) :=
  (isPolyTime_input unaryEncoding).unary_add (g := fun _ => 1)
    (isPolyTime_const unaryEncoding [true])

example : IsPPT (Oracle := Empty) unaryEncoding wordEncoding (fun parameter =>
    optionEncoding (pairEncoding code (finBinaryEncoding 2)) <$>
      (ElGamal.keygen (m := OptionT (effects Empty).FreeM)
        (OptionT.mk (FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          2 2 (parameter + 1))) generator).run) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPPT_keygen (G := fun _ => G) (fun _ => code) (fun _ => 2)
    (fun parameter => parameter + 1) (fun _ => generator)
    (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    mul_poly (isPolyTime_const _ _) (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

example : IsPPT (Oracle := Empty)
    (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code)) wordEncoding (fun input =>
      optionEncoding (pairEncoding code code) <$>
        (ElGamal.encrypt (m := OptionT (effects Empty).FreeM)
          (OptionT.mk (FreeM.sampleFin
            ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
            2 2 (input.1 + 1))) generator input.2.1 input.2.2).run) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPPT_encrypt (G := fun _ => G) (fun _ => code) (fun _ => 2)
    (fun parameter => parameter + 1) (fun _ => generator)
    (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    mul_poly (isPolyTime_const _ _) (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

example : IsPolyTime (sigmaEncoding unaryEncoding
    (fun _ => pairEncoding (finBinaryEncoding 2) (pairEncoding code code)))
      (fun input => code (ElGamal.decrypt input.2.1 input.2.2)) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPolyTime_decrypt (G := fun _ => G) (fun _ => code) (fun _ => 2)
    mul_poly (isPolyTime_const _ _) inv_poly
    (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

abbrev F := ZMod 2

noncomputable def scalar : F ≃ Fin 2 := (ZMod.finEquiv 2).toEquiv.symm

noncomputable def scalarCode : F ↪ Word := finEquivEncoding scalar

theorem fieldOp_poly (op : F → F → F) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun _ => pairEncoding scalarCode scalarCode))
      (fun value => scalarCode (op value.2.1 value.2.2)) :=
  (isPolyTime_of_finite (pairEncoding scalarCode scalarCode)
    (fun pair => scalarCode (op pair.1 pair.2))).comp_encoded
      (isPolyTime_input
        (sigmaEncoding unaryEncoding (fun _ => pairEncoding scalarCode scalarCode))).sigma_snd

noncomputable def scalarEncoding : Computability.Encoding F Bool :=
  .finEquiv scalar

noncomputable def simulatorStateEncoding :=
  Schnorr.seededSignatureMachineStateEncoding (fun _ => scalarEncoding) (fun _ => scalarCode)

noncomputable def tracedStateEncoding :=
  Schnorr.tracedSignatureMachineStateEncoding (fun _ => scalarEncoding) (fun _ => scalarCode)

-- The log is runtime data too. The certificate covers every source machine and arbitrary
-- input tapes, caches, and previously recorded events, including all rejection paths.
example {State : Type} [Finite State] {k ports : ℕ}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (control : State ↪ Word) :
    IsPolyTime (pairEncoding wordEncoding tracedStateEncoding) (fun arg =>
      optionEncoding (pairEncoding wordEncoding tracedStateEncoding)
        (Schnorr.runCheckedTracedSignatureMachine (fun _ => scalarEncoding)
          (fun _ => scalarEncoding) machine [] arg.1
            (Turing.MultiTapeMachine.Snapshot.initial machine.initial) arg.2)) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (scalarCode value).length)
  apply Schnorr.isPolyTime_runCheckedTracedSignatureMachine
    (F := fun _ => F) (G := fun _ => F) (fun _ => scalarEncoding) (fun _ => scalarEncoding)
    (isPolyTime_const _ _) _ _ (fieldOp_poly (· • ·)) (fieldOp_poly (· + ·))
    (fieldOp_poly (· - ·)) (control := control) machine
    (isPolyTime_const _ _) (isPolyTime_const _ []) (isPolyTime_fst _ _) (isPolyTime_snd _ _)
    (groupSize := fun _ => bound) (scalarSize := fun _ => bound)
    (by fun_prop) (by fun_prop) (fun _ => hbound) (fun _ => hbound)
  all_goals
    exact IsPolyTime.decode_finEquiv (parameter := Sigma.fst) (fun _ => scalar)
      (isPolyTime_const _ _) (isPolyTime_input _).sigma_snd

-- This certificate covers the complete run and its checked result, with unbounded input tapes,
-- cache, and signing log. Only the fixed test field's arithmetic uses finite tables.
example {State : Type} [Finite State] {k ports : ℕ}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (control : State ↪ Word) :
    IsPolyTime (pairEncoding wordEncoding simulatorStateEncoding) (fun arg =>
      optionEncoding (pairEncoding wordEncoding simulatorStateEncoding)
        (Schnorr.runCheckedSeededSignatureMachine (fun _ => scalarEncoding)
          (fun _ => scalarEncoding) machine [] arg.1
            (Turing.MultiTapeMachine.Snapshot.initial machine.initial) arg.2)) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (scalarCode value).length)
  apply Schnorr.isPolyTime_runCheckedSeededSignatureMachine
    (F := fun _ => F) (G := fun _ => F) (fun _ => scalarEncoding) (fun _ => scalarEncoding)
    (isPolyTime_const _ _) _ _ (fieldOp_poly (· • ·)) (fieldOp_poly (· + ·))
    (fieldOp_poly (· - ·)) (control := control) machine
    (isPolyTime_const _ _) (isPolyTime_const _ []) (isPolyTime_fst _ _) (isPolyTime_snd _ _)
    (groupSize := fun _ => bound) (scalarSize := fun _ => bound)
    (by fun_prop) (by fun_prop) (fun _ => hbound) (fun _ => hbound)
  all_goals
    exact IsPolyTime.decode_finEquiv (parameter := Sigma.fst) (fun _ => scalar)
      (isPolyTime_const _ _) (isPolyTime_input _).sigma_snd

-- All saved tapes, logs, caches, keys, and the parameter are runtime inputs. The source machine
-- is arbitrary; three interpreter passes use an adaptive selector and a fresh hash block.
example {State : Type} [Finite State] {k ports : ℕ}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (control : State ↪ Word) :
    IsPolyTime (pairEncoding wordEncoding simulatorStateEncoding) (fun arg =>
      optionEncoding
        (pairEncoding
          (pairEncoding (machineSnapshotEncoding k ports control) simulatorStateEncoding)
          (pairEncoding (machineSnapshotEncoding k ports control) simulatorStateEncoding))
        (machine.rewindSnapshotFromCoins? []
          (fun _ => Schnorr.seededSignatureMachineHandler (fun _ => scalarEncoding)
            (fun _ => scalarCode)) arg.1
          (Turing.MultiTapeMachine.Snapshot.initial machine.initial) arg.2
          (fun first => first.1.output.length) (Schnorr.restartSeededSignatureMachine id))) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (scalarCode value).length)
  apply Schnorr.isPolyTime_rewindSeededSignatureMachine
    (F := fun _ => F) (G := fun _ => F) (fun _ => scalarEncoding) (fun _ => scalarCode)
    (isPolyTime_const _ _) _ (fieldOp_poly (· • ·)) (fieldOp_poly (· - ·)) machine _ _
    (isPolyTime_fst _ _).machineSnapshot_output.unaryLength
    (Schnorr.isPolyTime_restartSeededSignatureMachine _ _ (isPolyTime_input unaryEncoding))
    (isPolyTime_const _ _) (isPolyTime_const _ [])
    (isPolyTime_fst _ _) (isPolyTime_snd _ _)
    (groupSize := fun _ => bound) (scalarSize := fun _ => bound)
    (by fun_prop) (by fun_prop) (fun _ => hbound) (fun _ => hbound)
  exact IsPolyTime.decode_finEquiv (parameter := Sigma.fst) (fun _ => scalar)
    (isPolyTime_const _ _) (isPolyTime_input _).sigma_snd

def adaptiveSimulation : (Schnorr.signatureEffects 0 Word F F).FreeM F := do
  let _ ← FreeM.lift (P := Schnorr.signatureEffects 0 Word F F) (.inr (.inl ([], 1)))
  let _ ← FreeM.lift (P := Schnorr.signatureEffects 0 Word F F) (.inr (.inr [true]))
  FreeM.lift (P := Schnorr.signatureEffects 0 Word F F) (.inr (.inl ([], 1)))

-- Signing leaves the hash tape alone; the repeated hash succeeds after that tape is exhausted.
-- The untouched private suffix is retained for replay, alongside the updated log and cache.
example : (adaptiveSimulation.liftM
    (P := Schnorr.signatureEffects 0 Word F F)
    (m := StateT ((List Word × List ((Word × F) × F)) × (List F × List F)) Option)
    (fun | .inl op => isEmptyElim op
         | .inr op => Schnorr.seededSignatureHandler (1 : F) 0 op)).run
      (([], []), [0, 1, 0], [1]) =
    some (1, ([[true]], [(([true], 1), 0), (([], 1), 1)]), [0], []) := rfl

-- Only the fresh hash is recorded. Signing and the repeated cache hit do not create positions.
example : (adaptiveSimulation.liftM
    (P := Schnorr.signatureEffects 0 Word F F)
    (m := StateT (((List Word × List ((Word × F) × F)) ×
      (List F × List F)) × List ((Word × F) × F)) Option)
    (fun | .inl op => isEmptyElim op
         | .inr op => Schnorr.traceSeededCall (Schnorr.seededSignatureHandler (1 : F) 0 op))).run
      ((([], []), [0, 1, 0], [1]), []) =
    some (1, (([[true]], [(([true], 1), 0), (([], 1), 1)]), [0], []), [(([], 1), 1)]) := rfl

def queryOnce : Turing.MultiTapePTM 0 Bool Bool (Fin 1) where
  initial := false
  tr state _ _ _ _ := if state then
    .step ⟨0, Fin.elim0, none, none⟩ (fun _ => none) (fun _ => 0)
    else .query 0 true

noncomputable def tracedRun (message : Word) (hashes : List F) (coins : Word) :=
  let candidate := ((Computability.encodingList Bool).bitPair
    (scalarEncoding.bitPair scalarEncoding)).bitOption.encode (some ([], (1 : F), (1 : F)))
  let request := (Schnorr.signatureRequestEncoding (Computability.encodingList Bool)
    scalarEncoding).encode (.inl (message, 1))
  let snapshot : Turing.MultiTapeMachine.Snapshot 0 Bool Bool (Fin 1) :=
    { Turing.MultiTapeMachine.Snapshot.initial (Oracle := Fin 1) false with
      output := candidate
      channels := fun _ => ⟨request, Turing.Tape.Snapshot.ofList []⟩ }
  (Schnorr.runCheckedTracedSignatureMachine (fun _ => scalarEncoding) (fun _ => scalarEncoding)
    queryOnce [] coins snapshot ⟨0, ((1 : F), 0, ([], []), [1, 0, 1], hashes), []⟩).map
      (fun out => (out.2.2.1.2.2.2.1, out.2.2.1.2.2.2.2, out.2.2.2))

-- The final verifier reuses an exhausted cached answer and leaves private randomness untouched.
example : tracedRun [] [0] [false, false] = some ([1, 0, 1], [], [(([], 1), 0)]) := rfl

-- A distinct adversary request precedes the verifier's new forkable position.
example : tracedRun [true] [0, 1] [false, false] =
    some ([1, 0, 1], [], [(([true], 1), 0), (([], 1), 1)]) := rfl

-- A live snapshot and an exhausted verifier both reject, even after a successful first query.
example : tracedRun [] [0] [false] = none := by decide
example : tracedRun [true] [0] [false, false] = none := by decide

-- A programming collision remains failure even when both scalar tapes have enough entries.
example : Schnorr.seededSignatureHandler (F := F) (1 : F) 0 (.inr ([] : Word))
    (([], [(([], 1), 0)]), [0, 1], [1]) = none := by decide

-- A forgery whose hash was never requested consumes the verifier's own fresh answer.
example : Schnorr.checkSeededForgery (F := F) (1 : F) 1 (([] : Word), 1, 0)
    (([], []), [0, 1], [1]) =
      some (([], 1, 0), ([], [(([], 1), 1)]), [0, 1], []) := rfl

example : Schnorr.checkSeededForgery (F := F) (1 : F) 1 (([] : Word), 1, 0)
    (([], []), [0, 1], []) = none := by decide

-- Cache hits need no remaining randomness, but freshness is still checked.
example : Schnorr.checkSeededForgery (F := F) (1 : F) 1 (([] : Word), 1, 0)
    (([], [(([], 1), 1)]), [], []) =
      some (([], 1, 0), ([], [(([], 1), 1)]), [], []) := rfl

example : Schnorr.checkSeededForgery (F := F) (1 : F) 1 (([] : Word), 1, 0)
    (([[]], [(([], 1), 1)]), [], []) = none := by decide

-- Failed interfaces and malformed tags are rejected before final hashing.
example : Schnorr.checkSeededForgeryOutput scalarEncoding scalarEncoding (1 : F) 1 (some [])
    (([], []), [0, 1], [1]) = none := rfl

example : Schnorr.checkSeededForgeryOutput scalarEncoding scalarEncoding (1 : F) 1
    (some [false, true]) (([], []), [0, 1], [1]) = none := rfl

-- A live machine cannot make a partial output count as a forgery, even if it is canonical.
example (word : Word) : Schnorr.checkSeededSignatureMachine
    (fun _ => scalarEncoding) (fun _ => scalarEncoding)
    { Turing.MultiTapeMachine.Snapshot.initial (k := 0) (Oracle := Fin 0) () with output := word }
      ⟨0, (1 : F), 1, ([], []), [0, 1], [1]⟩ = none := rfl

example : IsPPT (Oracle := Empty) unaryEncoding wordEncoding (fun parameter =>
    optionEncoding (pairEncoding scalarCode scalarCode) <$>
      (Schnorr.keygen (m := OptionT (effects Empty).FreeM)
        (OptionT.mk (Option.map scalar.symm <$> FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          2 2 (parameter + 1))) (1 : F)).run) :=
  Schnorr.isPPT_keygen (F := fun _ => F) (G := fun _ => F)
    (fun _ => scalarCode) (fun _ => 2) (fun parameter => parameter + 1) (fun _ => scalar)
    (fun _ => 1) (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    (isPolyTime_const _ _) (fieldOp_poly (· • ·))

-- The whole signing simulator is compiled, including bounded draws and its collision check.
example : IsPPT (Oracle := Empty) unaryEncoding wordEncoding (fun parameter =>
    optionEncoding (optionEncoding (pairEncoding (pairEncoding scalarCode scalarCode)
      (listEncoding (pairEncoding (pairEncoding (finiteEncoding Unit) scalarCode) scalarCode)))) <$>
        ((Schnorr.simulateSign (m := OptionT (effects Empty).FreeM)
          (OptionT.mk (Option.map scalar.symm <$> FreeM.sampleFin
            ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
            2 2 (parameter + 1))) (1 : F) (0 : F) ()).run []).run.run) :=
  Schnorr.isPPT_simulateSign (F := fun _ => F) (G := fun _ => F) (M := fun _ => Unit)
    (parameter := id) (fun _ => scalarCode) (fun _ => finiteEncoding Unit) (fun _ => 2)
    (fun parameter => parameter + 1) (fun _ => scalar)
    (isPolyTime_input unaryEncoding) (isPolyTime_const _ _) (isPolyTime_const _ _)
    (isPolyTime_const _ _) (isPolyTime_const _ _) (isPolyTime_const _ _) attempts_poly
    (isPolyTime_const _ _) (fieldOp_poly (· • ·)) (fieldOp_poly (· - ·))

example : IsPolyTime (sigmaEncoding unaryEncoding
    (fun _ => pairEncoding scalarCode (pairEncoding scalarCode scalarCode)))
      (fun input => scalarCode (Schnorr.respond input.2.1 input.2.2.1 input.2.2.2)) :=
  Schnorr.isPolyTime_respond (F := fun _ => F) (fun _ => scalarCode)
    (fieldOp_poly (· + ·)) (fieldOp_poly (· * ·))

example : IsPolyTime (sigmaEncoding unaryEncoding (fun _ =>
    pairEncoding (pairEncoding scalarCode scalarCode) (pairEncoding scalarCode scalarCode)))
      (fun input => scalarCode
        (Schnorr.extract input.2.1.1 input.2.1.2 input.2.2.1 input.2.2.2)) :=
  Schnorr.isPolyTime_extract (F := fun _ => F) (fun _ => scalarCode)
    (fieldOp_poly (· - ·)) (fieldOp_poly (· / ·))

example : IsPolyTime (sigmaEncoding unaryEncoding (fun _ =>
    pairEncoding scalarCode (pairEncoding scalarCode
      (pairEncoding scalarCode (pairEncoding scalarCode scalarCode)))))
      (fun input => boolEncoding (decide (Schnorr.Accepts input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2))) :=
  Schnorr.isPolyTime_accepts (F := fun _ => F) (G := fun _ => F)
    (fun _ => scalarCode) (fun _ => scalarCode) (fieldOp_poly (· • ·)) (fieldOp_poly (· + ·))

/- The key and value types grow with the parameter; lookup cannot use a fixed finite table. -/
def cacheInput := sigmaEncoding unaryEncoding (fun n =>
  pairEncoding (finBinaryEncoding (n + 1))
    (pairEncoding (optionEncoding (finBinaryEncoding (n + 2)))
      (listEncoding (pairEncoding (finBinaryEncoding (n + 1)) (finBinaryEncoding (n + 2))))))

example : IsPolyTime cacheInput (fun arg =>
    optionEncoding (pairEncoding (finBinaryEncoding (arg.1 + 2))
      (listEncoding (pairEncoding (finBinaryEncoding (arg.1 + 1))
        (finBinaryEncoding (arg.1 + 2)))))
      (RandomOracle.query arg.2.2.1 arg.2.1 arg.2.2.2)) := by
  have hd := (isPolyTime_input cacheInput).sigma_snd
  apply RandomOracle.isPolyTime_query_option (parameter := Sigma.fst)
    (key := fun n => finBinaryEncoding (n + 1)) (value := fun n => finBinaryEncoding (n + 2))
  · simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hd.bitPair_fst
  · simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hd.bitPair_snd.bitPair_snd
  · simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      hd.bitPair_snd.bitPair_fst

/- Exhaustion on a hit retains the first answer and all duplicate entries. -/
example : RandomOracle.query (none : Option ℕ) 1 [(1, 4), (1, 5)] =
    some (4, [(1, 4), (1, 5)]) := rfl

example : RandomOracle.query (none : Option ℕ) 2 [(1, 4)] = none := rfl

/- The range is supplied in binary, including zero and arbitrarily large finite types. -/
example : IsPPT (Oracle := Empty) binaryEncoding
    (sigmaEncoding binaryEncoding (fun n => optionEncoding
      (finEquivEncoding (Equiv.refl (Fin n))))) (fun n =>
      (fun result => ⟨n, result⟩) <$> FreeM.sampleFin
        ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin) n n.size 2) := by
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Option.map_id, id_eq] using
    isPPT_sampleFin_equiv (Oracle := Empty) (fun n => Equiv.refl (Fin n))
      (isPolyTime_input binaryEncoding) (isPolyTime_const binaryEncoding [true, true])

noncomputable def hashCacheCode :=
  listEncoding (pairEncoding (pairEncoding wordEncoding scalarCode) scalarCode)

noncomputable def signingInput := sigmaEncoding unaryEncoding
  (fun _ => pairEncoding scalarCode (pairEncoding wordEncoding hashCacheCode))

/- The message, secret, and complete cache are runtime inputs, with an unbounded retry budget. -/
example : IsPPT (Oracle := Empty) signingInput wordEncoding (fun arg =>
    let sample : OptionT (effects Empty).FreeM F := OptionT.mk
      (Option.map scalar.symm <$> FreeM.sampleFin
        ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin) 2 2 (arg.1 + 1))
    optionEncoding (pairEncoding (pairEncoding scalarCode scalarCode) hashCacheCode) <$>
      (Schnorr.sign (monadLift sample) (RandomOracle.query sample)
        (1 : F) arg.2.1 arg.2.2.1 arg.2.2.2).run) := by
  have hi := isPolyTime_input signingInput
  apply Schnorr.isPPT_sign (F := fun _ => F) (G := fun _ => F) (M := fun _ => Word)
    (parameter := Sigma.fst) (fun _ => scalarCode) (fun _ => wordEncoding)
    (fun _ => 2) (fun arg => arg.1 + 1) (fun _ => scalar)
  · exact hi.sigma_fst
  · exact isPolyTime_const _ _
  · exact hi.sigma_snd.fst
  · exact hi.sigma_snd.snd.fst
  · exact hi.sigma_snd.snd.snd
  · exact isPolyTime_const _ _
  · exact attempts_poly.comp_encoded hi.sigma_fst
  · exact isPolyTime_const _ _
  · exact fieldOp_poly (· • ·)
  · exact fieldOp_poly (· + ·)
  · exact fieldOp_poly (· * ·)

noncomputable def verificationInput := sigmaEncoding unaryEncoding (fun _ =>
  pairEncoding scalarCode (pairEncoding wordEncoding
    (pairEncoding (pairEncoding scalarCode scalarCode) hashCacheCode)))

example : IsPPT (Oracle := Empty) verificationInput wordEncoding (fun arg =>
    let sample : OptionT (effects Empty).FreeM F := OptionT.mk
      (Option.map scalar.symm <$> FreeM.sampleFin
        ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin) 2 2 (arg.1 + 1))
    optionEncoding (pairEncoding boolEncoding hashCacheCode) <$>
      (Schnorr.verify (RandomOracle.query sample) (1 : F) arg.2.1
        arg.2.2.1 arg.2.2.2.1 arg.2.2.2.2).run) := by
  have hi := isPolyTime_input verificationInput
  apply Schnorr.isPPT_verify (F := fun _ => F) (G := fun _ => F) (M := fun _ => Word)
    (parameter := Sigma.fst) (fun _ => scalarCode) (fun _ => wordEncoding)
    (fun _ => 2) (fun arg => arg.1 + 1) (fun _ => scalar)
  · exact hi.sigma_fst
  · exact isPolyTime_const _ _
  · exact hi.sigma_snd.fst
  · exact hi.sigma_snd.snd.fst
  · exact hi.sigma_snd.snd.snd.fst
  · exact hi.sigma_snd.snd.snd.snd
  · exact isPolyTime_const _ _
  · exact attempts_poly.comp_encoded hi.sigma_fst
  · exact isPolyTime_const _ _
  · exact fieldOp_poly (· • ·)
  · exact fieldOp_poly (· + ·)

end CryptoRuntime
