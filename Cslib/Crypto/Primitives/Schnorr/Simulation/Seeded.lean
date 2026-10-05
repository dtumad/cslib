/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation
public import Cslib.Foundations.Control.Monad.IsMonadHom.Transformers
public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape

/-!
# Schnorr simulation with saved scalar tapes

Private simulator randomness and fresh hash answers have separate cursors. The ordinary signing
simulator runs in `StateT` with these tapes; exhaustion and programming collisions both reject
the execution. Replaying a prefix restores the private cursor together with the log and cache.
A fork may then replace the remaining hash answers without resampling private randomness.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq M] [DecidableEq G]

/-- Read a private simulator scalar, leaving the fresh-hash tape untouched. -/
def readPrivateScalar : StateT (List F × List F) Option F := fun tapes =>
  (fun out => (out.1, out.2, tapes.2)) <$> FreeM.readAnswer tapes.1

/-- Read a fresh hash answer, leaving the simulator's private tape untouched. -/
def readHashScalar : StateT (List F × List F) Option F := fun tapes =>
  (fun out => (out.1, tapes.1, out.2)) <$> FreeM.readAnswer tapes.2

/-- The signing simulator with explicit saved tapes. The first state component is its ordinary
signing log and cache; the second is the private-scalar tape and fresh-hash tape. -/
def seededSignatureHandler (g pk : G) (op : (M × G) ⊕ M) :
    StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option
      ((signatureEffects 0 M G F).B (.inr op)) := fun (state, tapes) => do
  let (out, tapes') ← ((simulatedSignatureHandler (P := 0)
    (fun op => isEmptyElim op) readPrivateScalar (fun _ => readHashScalar)
      g pk (.inr op) state).run).run tapes
  let (answer, state') ← out
  pure (answer, state', tapes')

/-- Check a candidate against the shared cache and signed-message log. The verifier makes its
own hash query, consuming a fresh answer only when the candidate's hash input is absent. -/
def checkSeededForgery (g pk : G) (candidate : M × G × F) :
    StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option (M × G × F) :=
  fun state => do
    let (challenge, state') ← seededSignatureHandler g pk (.inl (candidate.1, candidate.2.1)) state
    if decide (Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2) &&
        decide (candidate.1 ∉ state.1.1) then
      some (candidate, state')
    else none

/-- Saved tapes implement the original simulator for an entire adaptive program. The equality
retains both tape cursors, the signed-message log, and the cache, and rejects either failure. -/
theorem liftM_seededSignatureHandler {α : Type} (g pk : G)
    (program : (signatureEffects 0 M G F).FreeM α)
    (state : List M × List ((M × G) × F)) (tapes : List F × List F) :
    (program.liftM (P := signatureEffects 0 M G F)
      (m := StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option) (fun
      | .inl op => isEmptyElim op
      | .inr op => seededSignatureHandler g pk op)).run (state, tapes) = (do
        let (out, tapes') ← (((program.liftM (simulatedSignatureHandler (P := 0)
          (m := StateT (List F × List F) Option)
          (fun op => isEmptyElim op) readPrivateScalar (fun _ => readHashScalar)
            g pk)).run state).run).run tapes
        let (value, state') ← out
        pure (value, state', tapes')) := by
  have h := (isMonadHom_stateT_optionT_stateT
    (List M × List ((M × G) × F)) (List F × List F)).map_pfunctorFreeMLiftM
      (simulatedSignatureHandler (P := 0) (fun op => isEmptyElim op)
        readPrivateScalar (fun _ => readHashScalar) g pk) program
  have hhandler : (fun (op : (signatureEffects 0 M G F).A)
      (state, tapes) => do
      let (out, tapes') ← (simulatedSignatureHandler (P := 0)
        (m := StateT (List F × List F) Option) (fun op => isEmptyElim op)
        readPrivateScalar (fun _ => readHashScalar) g pk op state).run tapes
      let (value, state') ← out
      pure (value, state', tapes')) = (fun
        | .inl op => isEmptyElim op
        | .inr op => seededSignatureHandler g pk op) := by
    funext op
    cases op with
    | inl op => exact isEmptyElim op
    | inr op => rfl
  rw [hhandler] at h
  exact (congrFun h (state, tapes)).symm

/-- Saved-tape execution followed by the final checker is the complete simulated-forgery
program. The equality retains both tape cursors and propagates every simulator or sampler abort. -/
theorem simulatedForgery_seeded (g pk : G)
    (adversary : G → (signatureEffects 0 M G F).FreeM (M × G × F))
    (tapes : List F × List F) :
    (do
      let (candidate, state) ← ((adversary pk).liftM (P := signatureEffects 0 M G F)
        (m := StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option) (fun
          | .inl op => isEmptyElim op
          | .inr op => seededSignatureHandler g pk op)).run (([], []), tapes)
      let (candidate, state) ← checkSeededForgery g pk candidate state
      pure (candidate, state.2)) = (do
        let (candidate, tapes') ← (simulatedForgery (P := 0) (m := StateT (List F × List F) Option)
          (fun op => isEmptyElim op) readPrivateScalar (fun _ => readHashScalar)
            g pk adversary).run tapes
        let candidate ← candidate
        pure (candidate, tapes')) := by
  rw [liftM_seededSignatureHandler]
  simp only [simulatedForgery, checkSeededForgery, StateT.run, OptionT.run, OptionT.mk,
    Bind.bind, StateT.bind, OptionT.bind, Pure.pure, OptionT.pure, Option.bind_assoc]
  congr 1
  funext out
  rcases out with ⟨candidate, tapes'⟩
  cases candidate with
  | none => rfl
  | some out =>
    rcases out with ⟨⟨message, commitment, response⟩, messages, cache⟩
    simp only [Option.bind_some, seededSignatureHandler, simulatedSignatureHandler,
      StateT.run, OptionT.run, OptionT.mk, verify, monadLift, MonadLift.monadLift,
      OptionT.lift, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Option.bind_assoc]
    congr 1
    funext out
    split <;> rfl

/-- A cached hash consumes no tape, even when both tapes are exhausted. -/
theorem seededSignatureHandler_hash_hit (g pk : G) (input : M × G)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (answer : F) (h : cache.lookup input = some answer) :
    seededSignatureHandler g pk (.inl input) ((messages, cache), privateScalars, hashScalars) =
      some (answer, (messages, cache), privateScalars, hashScalars) := by
  simp [seededSignatureHandler, simulatedSignatureHandler, RandomOracle.query, h,
    StateT.run, OptionT.run, OptionT.mk]
  rfl

/-- A fresh hash consumes exactly one hash answer and retains all private scalars. -/
theorem seededSignatureHandler_hash_miss (g pk : G) (input : M × G)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (answer : F) (h : cache.lookup input = none) :
    seededSignatureHandler g pk (.inl input)
        ((messages, cache), privateScalars, answer :: hashScalars) =
      some (answer, (messages, (input, answer) :: cache), privateScalars, hashScalars) := by
  simp only [seededSignatureHandler, simulatedSignatureHandler, RandomOracle.query, h,
    StateT.run, OptionT.run, OptionT.mk, bind_assoc, pure_bind]
  rfl

/-- A cache miss with no fresh hash answer rejects the run. -/
theorem seededSignatureHandler_hash_exhausted (g pk : G) (input : M × G)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars : List F)
    (h : cache.lookup input = none) :
    seededSignatureHandler g pk (.inl input) ((messages, cache), privateScalars, []) = none := by
  simp only [seededSignatureHandler, simulatedSignatureHandler, RandomOracle.query, h,
    StateT.run, OptionT.run, OptionT.mk, bind_assoc, pure_bind]
  rfl

/-- A successful hash retains the signing log and private tape, and records the returned answer. -/
theorem seededSignatureHandler_hash_spec (g pk : G) (input : M × G)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    {answer : F} {state' : (List M × List ((M × G) × F)) × (List F × List F)}
    (h : seededSignatureHandler g pk (.inl input) state = some (answer, state')) :
    state'.1.1 = state.1.1 ∧ state'.2.1 = state.2.1 ∧
      state'.1.2.lookup input = some answer := by
  rcases state with ⟨⟨messages, cache⟩, privateScalars, hashScalars⟩
  cases hlookup : cache.lookup input with
  | some value =>
    rw [seededSignatureHandler_hash_hit _ _ _ _ _ _ _ _ hlookup] at h
    cases h
    exact ⟨rfl, rfl, hlookup⟩
  | none =>
    cases hashScalars with
    | nil =>
      rw [seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup] at h
      cases h
    | cons value rest =>
      rw [seededSignatureHandler_hash_miss _ _ _ _ _ _ _ _ hlookup] at h
      cases h
      exact ⟨rfl, rfl, by simp⟩

/-- Every successful checked output is the supplied candidate, is fresh, and verifies against
the retained cache. Verification preserves the signing log and all private simulator randomness. -/
theorem checkSeededForgery_sound (g pk : G) (candidate : M × G × F)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    {result : (M × G × F) × ((List M × List ((M × G) × F)) × (List F × List F))}
    (h : checkSeededForgery g pk candidate state = some result) :
    result.1 = candidate ∧ candidate.1 ∉ state.1.1 ∧
      result.2.1.1 = state.1.1 ∧ result.2.2.1 = state.2.1 ∧
        ∃ challenge, result.2.1.2.lookup (candidate.1, candidate.2.1) = some challenge ∧
          Accepts g pk candidate.2.1 challenge candidate.2.2 := by
  dsimp +instances only [checkSeededForgery] at h
  obtain ⟨⟨challenge, state'⟩, hquery, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hvalid =>
    cases h
    have hvalid : Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2 ∧
        candidate.1 ∉ state.1.1 := by simpa using hvalid
    obtain ⟨hlog, hprivate, hcache⟩ :=
      seededSignatureHandler_hash_spec g pk _ state hquery
    exact ⟨rfl, hvalid.2, hlog, hprivate, challenge, hcache, hvalid.1⟩
  next => cases h

/-- Signing uses two private scalars and does not consume a fresh hash answer. -/
theorem seededSignatureHandler_sign (g pk : G) (message : M)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (challenge response : F) :
    seededSignatureHandler g pk (.inr message)
        ((messages, cache), challenge :: response :: privateScalars, hashScalars) =
      (simulateSign.finish message cache
        (response • g - challenge • pk, challenge, response)).map
          (fun out => (out.1, (message :: messages, out.2), privateScalars, hashScalars)) := by
  dsimp [seededSignatureHandler, simulatedSignatureHandler, simulateSign, simulateTranscript,
    StateT.run, OptionT.run, OptionT.mk, Bind.bind, StateT.bind, OptionT.bind,
    Pure.pure, StateT.pure, OptionT.pure, readPrivateScalar, FreeM.readAnswer]
  unfold simulateSign.finish
  split <;> rfl

/-- Signing rejects a private tape with fewer than two scalars. -/
theorem seededSignatureHandler_sign_exhausted (g pk : G) (message : M)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (h : privateScalars.length < 2) :
    seededSignatureHandler g pk (.inr message)
      ((messages, cache), privateScalars, hashScalars) = none := by
  cases privateScalars with
  | nil => rfl
  | cons challenge rest =>
    cases rest with
    | nil => rfl
    | cons response rest => simp at h

end Cslib.Crypto.Schnorr
