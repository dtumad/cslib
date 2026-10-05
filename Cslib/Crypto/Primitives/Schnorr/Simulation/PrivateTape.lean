/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation.Trace
public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape

/-!
# Schnorr simulation after fixing private randomness

Only fresh hash inputs remain visible operations. Signing draws from the saved private tape,
uses the existing transcript simulator, and rejects programming collisions as before.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {F G M : Type}

private def interpretPrivateSignature {α : Type}
    (action : StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) α) :
    StateT (((List M × List ((M × G) × F)) × (List F × List F)) ×
      List ((M × G) × F)) Option α := fun ((state, privateScalars, hashScalars), events) =>
  (FreeM.runTracedFromAnswers (action (state, privateScalars))
    (hashScalars, events.map (fun event => ⟨event.1, event.2⟩))).map
      (fun out => (out.1.1, (out.1.2.1, out.1.2.2, out.2.1),
        out.2.2.map (fun event => (event.1, event.2))))

private theorem isMonadHom_interpretPrivateSignature :
    IsMonadHom (StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
      (StateT (((List M × List ((M × G) × F)) × (List F × List F)) ×
        List ((M × G) × F)) Option) interpretPrivateSignature := by
  let repr : (((List M × List ((M × G) × F)) × (List F × List F)) ×
      List ((M × G) × F)) ≃
        (((List M × List ((M × G) × F)) × List F) ×
          (List F × List (Sigma (PFunctor.mk (M × G) (fun _ => F)).B))) :=
    { toFun := fun ((state, privateScalars, hashScalars), events) =>
        ((state, privateScalars), hashScalars, events.map (fun event => ⟨event.1, event.2⟩))
      invFun := fun ((state, privateScalars), hashScalars, events) =>
        ((state, privateScalars, hashScalars), events.map (fun event => (event.1, event.2)))
      left_inv := by
        rintro ⟨⟨state, privateScalars, hashScalars⟩, events⟩
        simp [List.map_map, Function.comp_def]
      right_inv := by
        rintro ⟨⟨state, privateScalars⟩, hashScalars, events⟩
        simp [List.map_map, Function.comp_def] }
  have hf := (isMonadHom_stateT_equiv (m := Option) repr).comp
    ((isMonadHom_stateT_stateT (m := Option) _ _).comp
      ((FreeM.isMonadHom_runTracedFromAnswers (Operation := M × G) (Answer := F)).stateT _))
  convert hf using 1
  funext α action state
  simp [interpretPrivateSignature, repr, Option.map_map, Function.comp_def, StateT.run]

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq M] [DecidableEq G]

/-- The simulator with fixed private scalars and fresh hash operations. The state contains the
ordinary signing log and cache together with the unused private-scalar suffix. -/
def privateSignatureHandler (g pk : G) (op : (M × G) ⊕ M) :
    StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM)
        ((signatureEffects 0 M G F).B (.inr op)) := fun ((messages, cache), privateScalars) =>
  match op with
  | .inl input => OptionT.mk do
      let (answer, cache') ← RandomOracle.query (FreeM.lift input) input cache
      pure (some (answer, (messages, cache'), privateScalars))
  | .inr message => OptionT.mk (pure (do
      let (challenge, privateScalars) ← FreeM.readAnswer privateScalars
      let (response, privateScalars) ← FreeM.readAnswer privateScalars
      let (signature, cache') ← simulateSign.finish message cache
        (response • g - challenge • pk, challenge, response)
      pure (signature, (message :: messages, cache'), privateScalars)))

/-- Final verification after fixing private randomness. Its hash query uses the same cache
and remains visible precisely when the candidate's input is fresh. -/
def checkPrivateForgery (g pk : G) (candidate : M × G × F) :
    StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) (M × G × F) := fun state => do
  let (challenge, state') ← privateSignatureHandler g pk
    (.inl (candidate.1, candidate.2.1)) state
  if decide (Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2) &&
      decide (candidate.1 ∉ state.1.1) then pure (candidate, state') else failure

/-- Final verification is independent of the remaining private scalar tape. -/
theorem run'_checkPrivateForgery (g pk : G) (candidate : M × G × F)
    (state : List M × List ((M × G) × F)) (tape : List F) :
    ((checkPrivateForgery g pk candidate).run' (state, tape)).run = (do
      let (valid, _) ← (verify (fun input => RandomOracle.query
        (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F)) input) input)
        g pk candidate.1 candidate.2).run state.2
      pure (if valid && decide (candidate.1 ∉ state.1) then some candidate else none)) := by
  rcases state with ⟨messages, cache⟩
  simp only [checkPrivateForgery, privateSignatureHandler, verify, StateT.run',
    StateT.run_bind, StateT.run_pure, OptionT.run_map, OptionT.run_bind,
    OptionT.run_mk]
  dsimp +instances only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, OptionT.run,
    OptionT.bind, OptionT.pure, OptionT.mk]
  simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, Option.elimM, Option.elim_some,
    StateT.run, bind_assoc, pure_bind, map_bind]
  congr 1
  funext out
  split <;> rfl


/-- Interpreting the visible hash operations gives exactly the existing saved-tape recorder.
The equality retains the signing log, cache, both tape cursors, trace, and all failures. -/
theorem privateSignatureHandler_traced (g pk : G) (op : (M × G) ⊕ M)
    (state : List M × List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) :
    (FreeM.runTracedFromAnswers (privateSignatureHandler g pk op (state, privateScalars))
      (hashScalars, events.map (fun event => ⟨event.1, event.2⟩))).map
        (fun out => (out.1.1, (out.1.2.1, out.1.2.2, out.2.1),
          out.2.2.map (fun event => (event.1, event.2)))) =
      traceSeededCall (seededSignatureHandler g pk op) ((state, privateScalars, hashScalars),
        events) := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl input =>
    cases hlookup : cache.lookup input with
    | some answer =>
      rw [traceSeededCall_hash_hit _ _ _ _ _ _ _ _ _ hlookup]
      simp [privateSignatureHandler, RandomOracle.query, hlookup,
        FreeM.runTracedFromAnswers_mk_pure, List.map_map, Function.comp_def]
    | none =>
      simp only [privateSignatureHandler, RandomOracle.query, hlookup, bind_assoc, pure_bind]
      rw [FreeM.runTracedFromAnswers_mk_lift_bind]
      cases hashScalars with
      | nil =>
        simp [FreeM.readAnswerTrace, traceSeededCall,
          seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup]
      | cons answer rest =>
        rw [traceSeededCall_hash_miss _ _ _ _ _ _ _ _ _ hlookup]
        simp [FreeM.readAnswerTrace, List.map_map, Function.comp_def]
  | inr message =>
    cases privateScalars with
    | nil =>
      simp [privateSignatureHandler, FreeM.readAnswer, traceSeededCall,
        seededSignatureHandler_sign_exhausted g pk message messages cache [] hashScalars (by simp)]
    | cons challenge rest =>
      cases rest with
      | nil =>
        simp [privateSignatureHandler, FreeM.readAnswer, traceSeededCall,
          seededSignatureHandler_sign_exhausted g pk message messages cache [challenge]
            hashScalars (by simp)]
      | cons response privateScalars =>
        rw [traceSeededCall_sign]
        simp only [privateSignatureHandler, FreeM.readAnswer,
          FreeM.runTracedFromAnswers_mk_pure]
        cases hfinish : simulateSign.finish message cache
          (response • g - challenge • pk, challenge, response) <;>
          simp [hfinish, List.map_map, Function.comp_def]

/-- The correspondence holds for every adaptive typed program. The private tape is fixed
before interpreting the program; only fresh hash operations contribute to its visible trace. -/
theorem liftM_privateSignatureHandler_traced {α : Type} (g pk : G)
    (program : (signatureEffects 0 M G F).FreeM α)
    (state : List M × List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) :
    (FreeM.runTracedFromAnswers
      ((program.liftM (P := signatureEffects 0 M G F)
        (m := StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM)) (fun
          | .inl op => isEmptyElim op
          | .inr op => privateSignatureHandler g pk op)) (state, privateScalars))
      (hashScalars, events.map (fun event => ⟨event.1, event.2⟩))).map
        (fun out => (out.1.1, (out.1.2.1, out.1.2.2, out.2.1),
          out.2.2.map (fun event => (event.1, event.2)))) =
      (program.liftM (P := signatureEffects 0 M G F) (m := StateT
        (((List M × List ((M × G) × F)) × (List F × List F)) × List ((M × G) × F)) Option)
          (fun | .inl op => isEmptyElim op
               | .inr op => traceSeededCall (seededSignatureHandler g pk op)))
        ((state, privateScalars, hashScalars), events) := by
  let handler : (op : (signatureEffects 0 M G F).A) →
      StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) ((signatureEffects 0 M G F).B op)
    | .inl op => isEmptyElim op
    | .inr op => privateSignatureHandler g pk op
  have h := isMonadHom_interpretPrivateSignature.map_pfunctorFreeMLiftM
    (P := signatureEffects 0 M G F) handler program
  have hhandler : (fun op => interpretPrivateSignature (handler op)) =
      (fun | .inl op => isEmptyElim op
           | .inr op => traceSeededCall (seededSignatureHandler g pk op)) := by
    funext op ⟨⟨state, privateScalars, hashScalars⟩, events⟩
    cases op with
    | inl op => exact isEmptyElim op
    | inr op => exact privateSignatureHandler_traced g pk op state privateScalars hashScalars events
  rw [hhandler] at h
  exact congrFun h ((state, privateScalars, hashScalars), events)

/-- The final verifier has the same successful trace and abort behavior in the hash-only
source program and the saved-tape implementation. -/
theorem checkPrivateForgery_traced (g pk : G) (candidate : M × G × F)
    (state : List M × List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) :
    (FreeM.runTracedFromAnswers (checkPrivateForgery g pk candidate (state, privateScalars))
      (hashScalars, events.map (fun event => ⟨event.1, event.2⟩))).map
        (fun out => (out.1.1, (out.1.2.1, out.1.2.2, out.2.1),
          out.2.2.map (fun event => (event.1, event.2)))) =
      traceSeededCall (checkSeededForgery g pk candidate)
        ((state, privateScalars, hashScalars), events) := by
  rw [traceSeededCall_check, ← privateSignatureHandler_traced]
  unfold checkPrivateForgery
  rw [FreeM.isMonadHom_runTracedFromAnswers.map_bind]
  dsimp +instances only [Bind.bind, StateT.bind]
  rw [Option.map_bind, Option.bind_map]
  congr 1
  funext out
  dsimp only [Function.comp_apply]
  split <;> rfl

/-- Complete adaptive execution and final checking after fixing all private simulator scalars.
Only fresh hash draws remain as source operations; rejected runs return no candidate. -/
def privateForgery (g pk : G)
    (program : OptionT (signatureEffects 0 M G F).FreeM (M × G × F)) (privateScalars : List F) :
    (PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)) :=
  ((do
    let candidate ← program.run.liftM (P := signatureEffects 0 M G F)
      (m := StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
        (fun | .inl op => isEmptyElim op | .inr op => privateSignatureHandler g pk op)
    match candidate with
    | none => failure
    | some candidate => checkPrivateForgery g pk candidate).run' (([], []), privateScalars)).run

/-- Fixing private signing randomness leaves at most one visible hash call per request. -/
theorem queryBound_privateSignatureHandler_le (g pk : G) (op : (M × G) ⊕ M)
    (state : (List M × List ((M × G) × F)) × List F) :
    FreeM.queryBound (privateSignatureHandler g pk op state).run ≤ 1 := by
  rcases state with ⟨⟨messages, cache⟩, privateScalars⟩
  cases op with
  | inl input =>
    cases h : cache.lookup input <;>
      simp [privateSignatureHandler, RandomOracle.query, h,
        FreeM.queryBound_lift (P := PFunctor.mk (M × G) (fun _ => F))]
  | inr message => exact zero_le

/-- Final verification uses at most one fresh hash answer, including a cache miss. -/
theorem queryBound_checkPrivateForgery_le (g pk : G) (candidate : M × G × F)
    (state : (List M × List ((M × G) × F)) × List F) :
    FreeM.queryBound (checkPrivateForgery g pk candidate state).run ≤ 1 := by
  unfold checkPrivateForgery
  apply (FreeM.queryBound_optionT_bind_le _ _ 0 ?_).trans
  · simpa only [add_zero] using queryBound_privateSignatureHandler_le g pk _ state
  · rintro ⟨challenge, state'⟩
    dsimp only
    split <;> simp

/-- The hash-only source needs at most one answer per source request and one for its final
verifier. This bound holds for every private tape, including insufficient ones. -/
theorem queryBound_privateForgery_le (g pk : G)
    (program : OptionT (signatureEffects 0 M G F).FreeM (M × G × F))
    (privateScalars : List F) :
    FreeM.queryBound (privateForgery g pk program privateScalars) ≤
      FreeM.queryBound program.run + 1 := by
  let handler : (op : (signatureEffects 0 M G F).A) →
      StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM)
          ((signatureEffects 0 M G F).B op)
    | .inl op => isEmptyElim op
    | .inr op => privateSignatureHandler g pk op
  have hcost := FreeM.queryBoundP_liftM_stateT_le (fun _ => true) (fun _ => true)
    handler (fun op state => by
      cases op with
      | inl op => exact isEmptyElim op
      | inr op => simpa only [handler, StateT.run, FreeM.queryBoundP_true, ↓reduceIte] using
          queryBound_privateSignatureHandler_le g pk op state)
    program.run (([], []), privateScalars)
  simp only [FreeM.queryBoundP_true] at hcost
  change FreeM.queryBound (Prod.fst <$> ((program.run.liftM handler >>= fun candidate =>
    match candidate with
    | none => failure
    | some candidate => checkPrivateForgery g pk candidate) (([], []), privateScalars))).run ≤ _
  rw [OptionT.run_map, FreeM.queryBound_map]
  apply (FreeM.queryBound_optionT_bind_le _ _ 1 ?_).trans
  · exact add_le_add hcost le_rfl
  · rintro ⟨candidate, state⟩
    cases candidate with
    | none =>
      change FreeM.queryBound ((failure : StateT _
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) (M × G × F)).run state).run ≤ 1
      rw [StateT.run_failure]
      exact zero_le
    | some candidate => exact queryBound_checkPrivateForgery_le g pk candidate state

private abbrev privateEffects (M G F : Type) : PFunctor :=
  PFunctor.mk (M × G) (fun _ => F) + PFunctor.mk Unit (fun _ => F)

private def interpretPrivateRandomness {α : Type}
    (action : StateT (List M × List ((M × G) × F))
      (OptionT (privateEffects M G F).FreeM) α) :
    StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) α := fun (state, tape) => do
  let (out, tape') ← FreeM.withAnswerTape (action state).run tape
  let (value, state') ← OptionT.mk (pure out)
  pure (value, state', tape')

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
private theorem isMonadHom_interpretPrivateRandomness :
    IsMonadHom (StateT (List M × List ((M × G) × F))
      (OptionT (privateEffects M G F).FreeM))
      (StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM)) interpretPrivateRandomness :=
  (isMonadHom_stateT_optionT_stateT_optionT _ _).comp
    (FreeM.isMonadHom_withAnswerTape.optionT.stateT _)

private theorem interpretPrivateRandomness_call (g pk : G) (op : (M × G) ⊕ M)
    (state : List M × List ((M × G) × F)) (tape : List F) :
    interpretPrivateRandomness (simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
      (fun op => isEmptyElim op) (FreeM.lift (P := privateEffects M G F) (.inr ()))
      (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk (.inr op))
      (state, tape) = privateSignatureHandler g pk op (state, tape) := by
  have hpure {α : Type} (value : α) (tape : List F) :
      (pure value : StateT (List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) α) tape =
        pure (some (value, tape)) := rfl
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl input =>
    cases h : cache.lookup input <;>
      simp only [interpretPrivateRandomness, simulatedSignatureHandler, privateSignatureHandler,
        RandomOracle.query, h, OptionT.run_mk, bind_assoc, pure_bind]
    all_goals
      dsimp +instances only [Bind.bind, OptionT.bind, OptionT.run, OptionT.mk,
        Pure.pure, OptionT.pure]
      simp only [FreeM.bind_eq_bind, FreeM.withAnswerTape,
        FreeM.liftM_bind, FreeM.liftM_lift (P := privateEffects M G F)]
      dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run, OptionT.mk,
        Pure.pure, StateT.pure, OptionT.pure]
      simp [hpure]
  | inr message =>
    dsimp +instances only [interpretPrivateRandomness, simulatedSignatureHandler,
      privateSignatureHandler, simulateSign, simulateTranscript, StateT.run,
      Bind.bind, OptionT.bind, Pure.pure, OptionT.pure, OptionT.mk, OptionT.run]
    simp only [FreeM.bind_eq_bind, bind_assoc, FreeM.withAnswerTape,
      FreeM.liftM_bind, FreeM.liftM_lift (P := privateEffects M G F)]
    dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run, OptionT.mk,
      Pure.pure, StateT.pure, OptionT.pure]
    cases tape with
    | nil => simp [FreeM.readAnswer]
    | cons challenge tape =>
      cases tape with
      | nil => simp [FreeM.readAnswer]
      | cons response tape =>
        cases h : simulateSign.finish message cache
            (response • g - challenge • pk, challenge, response) <;>
          simp [FreeM.readAnswer, h, hpure, FreeM.liftM_pure]

private theorem interpretPrivateRandomness_liftM {α : Type} (g pk : G)
    (program : (signatureEffects 0 M G F).FreeM α) :
    interpretPrivateRandomness (program.liftM
      (simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
        (fun op => isEmptyElim op) (FreeM.lift (P := privateEffects M G F) (.inr ()))
        (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk)) =
      program.liftM (P := signatureEffects 0 M G F)
        (m := StateT ((List M × List ((M × G) × F)) × List F)
          (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
        (fun | .inl op => isEmptyElim op | .inr op => privateSignatureHandler g pk op) := by
  rw [isMonadHom_interpretPrivateRandomness.map_pfunctorFreeMLiftM]
  congr 1
  funext op ⟨state, tape⟩
  cases op with
  | inl op => exact isEmptyElim op
  | inr op => exact interpretPrivateRandomness_call g pk op state tape

private theorem queryBoundP_privateRandomness_le {α : Type} (g pk : G)
    (program : (signatureEffects 0 M G F).FreeM α)
    (state : List M × List ((M × G) × F)) :
    FreeM.queryBoundP Sum.isRight
      ((program.liftM (simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
        (fun op => isEmptyElim op) (FreeM.lift (P := privateEffects M G F) (.inr ()))
        (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk))
        state).run ≤ FreeM.queryBound program * 2 := by
  apply (FreeM.queryBoundP_liftM_stateT_optionT_le_mul
    (Q := privateEffects M G F) (fun _ => true)
    Sum.isRight _ 2 ?_ program state).trans_eq
    (by rw [FreeM.queryBoundP_true])
  rintro (op | (input | message)) ⟨messages, cache⟩
  · exact isEmptyElim op
  · cases h : cache.lookup input <;>
      simp [simulatedSignatureHandler, RandomOracle.query, h, StateT.run, OptionT.run,
        OptionT.mk,
        FreeM.queryBoundP_lift (P := privateEffects M G F)]
  · dsimp +instances only [simulatedSignatureHandler, simulateSign, simulateTranscript,
      StateT.run, OptionT.run, OptionT.mk, Bind.bind, OptionT.bind, Pure.pure, OptionT.pure]
    simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, bind_assoc, pure_bind, ↓reduceIte]
    apply (FreeM.queryBoundP_bind_le (P := privateEffects M G F) Sum.isRight _ _ 1 ?_).trans
    · norm_num [FreeM.queryBoundP_lift (P := privateEffects M G F)]
    · intro challenge
      apply (FreeM.queryBoundP_bind_le (P := privateEffects M G F) Sum.isRight _ _ 0 ?_).trans
      · simp [FreeM.queryBoundP_lift (P := privateEffects M G F)]
      · intro response
        cases simulateSign.finish message cache
          (response • g - challenge • pk, challenge, response) <;> exact le_rfl

/-- Sampling a sufficiently long private scalar tape before the adversary preserves the
joint output, signing log, and cache. Only hash operations remain visible to the environment. -/
theorem toMeasure_liftM_privateSignatureHandler {α : Type}
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] [Countable M] [Countable G]
    [MeasurableSpace (List M × List ((M × G) × F))]
    [DiscreteMeasurableSpace (List M × List ((M × G) × F))]
    (μ : OutputMeasure (PFunctor.mk (M × G) (fun _ => F)))
    [∀ op, MeasureTheory.IsProbabilityMeasure (μ op)]
    (sample : (PFunctor.mk (M × G) (fun _ => F)).FreeM F) (g pk : G)
    (program : (signatureEffects 0 M G F).FreeM α)
    (state : List M × List ((M × G) × F)) (count : ℕ)
    (hcount : FreeM.queryBound program * 2 ≤ count) :
    (do
      let tape ← (List.replicate count ()).mapM (fun _ => sample)
      Option.map (fun out : α × ((List M × List ((M × G) × F)) × List F) =>
        (out.1, out.2.1)) <$>
        ((program.liftM (P := signatureEffects 0 M G F)
          (m := StateT ((List M × List ((M × G) × F)) × List F)
            (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
          (fun | .inl op => isEmptyElim op | .inr op => privateSignatureHandler g pk op))
          (state, tape)).run).toMeasure μ =
      ((program.liftM (simulatedSignatureHandler (P := 0)
        (fun op => isEmptyElim op) sample
        (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F))) g pk)) state).run.toMeasure μ := by
  let : MeasurableSpace (List F) := ⊤
  let action := program.liftM (simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
    (fun op => isEmptyElim op) (FreeM.lift (P := privateEffects M G F) (.inr ()))
    (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk)
  have hpoint (tape : List F) :
      Option.join <$> ((FreeM.withAnswerTape (action state).run).run' tape).run =
        Option.map (fun out : α × ((List M × List ((M × G) × F)) × List F) =>
          (out.1, out.2.1)) <$>
          ((program.liftM (P := signatureEffects 0 M G F)
            (m := StateT ((List M × List ((M × G) × F)) × List F)
              (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
            (fun | .inl op => isEmptyElim op | .inr op => privateSignatureHandler g pk op))
            (state, tape)).run := by
    rw [← interpretPrivateRandomness_liftM g pk program]
    simp only [StateT.run', OptionT.run_map]
    dsimp +instances only [interpretPrivateRandomness, StateT.run', OptionT.run,
      OptionT.mk, Bind.bind, OptionT.bind, Pure.pure, OptionT.pure]
    simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, map_eq_pure_bind, bind_assoc, pure_bind]
    congr 1
    funext out
    cases out with
    | none => rfl
    | some out =>
      rcases out with ⟨out, tape⟩
      cases out <;> rfl
  have hcost := (queryBoundP_privateRandomness_le g pk program state).trans hcount
  have hμ := FreeM.denote_withAnswerTape μ sample (action state).run count hcost
  have hμ' := congrArg (fun measure => measure.map
    (Option.join : Option (Option (α × (List M × List ((M × G) × F)))) → _)) hμ
  rw [← FreeM.denote_map _ _ _ Measurable.of_discrete,
    ← FreeM.denote_map _ _ _ Measurable.of_discrete] at hμ'
  simp only [FreeM.map_eq_map, map_bind, hpoint, Functor.map_map,
    Option.join_some, id_map'] at hμ'
  change FreeM.denote μ _ = FreeM.denote μ _
  rw [hμ']
  let merge : (op : (privateEffects M G F).A) →
      (PFunctor.mk (M × G) (fun _ => F)).FreeM ((privateEffects M G F).B op)
    | .inl input => FreeM.lift input
    | .inr _ => sample
  let handler := simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
    (fun op => isEmptyElim op) (FreeM.lift (P := privateEffects M G F) (.inr ()))
    (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk
  have hhandler : (fun op state => OptionT.mk (((handler op) state).run.liftM merge)) =
      simulatedSignatureHandler (P := 0) (fun op => isEmptyElim op) sample
        (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F))) g pk := by
    funext op state
    have h := map_simulatedSignatureHandler (FreeM.isMonadHom_liftM merge)
      (P := 0) (F := F) (G := G) (M := M) (fun op => isEmptyElim op)
      (FreeM.lift (P := privateEffects M G F) (.inr ()))
      (fun input => FreeM.lift (P := privateEffects M G F) (.inl input)) g pk op state
    cases op with
    | inl op => exact isEmptyElim op
    | inr op =>
      cases op <;>
      simpa only [FreeM.liftM_lift (P := privateEffects M G F), merge, handler,
        simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk] using h
  have h := congrFun (((FreeM.isMonadHom_liftM merge).optionT.stateT
    (List M × List ((M × G) × F))).map_pfunctorFreeMLiftM handler program) state
  change ((action state).run.liftM merge) = _ at h
  simp only [StateT.run] at h
  rw [hhandler] at h
  apply congrArg (FreeM.denote μ)
  convert h using 1
  · congr 1
    funext op
    cases op <;> rfl
  · rfl

/-- The first saved-seed forgery experiment has the simulator's complete optional result
law, including its final cache lookup and rejection of previously signed messages. -/
theorem toMeasure_privateForgery
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    [MeasurableSpace G] [DiscreteMeasurableSpace G] [Countable G]
    [MeasurableSpace M] [DiscreteMeasurableSpace M] [Countable M]
    [MeasurableSpace (List M × List ((M × G) × F))]
    [DiscreteMeasurableSpace (List M × List ((M × G) × F))]
    (μ : OutputMeasure (PFunctor.mk (M × G) (fun _ => F)))
    [∀ op, MeasureTheory.IsProbabilityMeasure (μ op)]
    (sample : (PFunctor.mk (M × G) (fun _ => F)).FreeM F) (g pk : G)
    (program : OptionT (signatureEffects 0 M G F).FreeM (M × G × F))
    (count : ℕ) (hcount : FreeM.queryBound program.run * 2 ≤ count) :
    (do
      let tape ← (List.replicate count ()).mapM (fun _ => sample)
      privateForgery g pk program tape).toMeasure μ =
    (do
      let out ← ((program.run.liftM (P := signatureEffects 0 M G F)
        (simulatedSignatureHandler (P := 0) (F := F) (G := G) (M := M)
        (m := (PFunctor.mk (M × G) (fun _ => F)).FreeM)
        (fun op => isEmptyElim op) sample
        (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F))) g pk)) ([], [])).run
      match out with
      | none | some (none, _) => pure (none : Option (M × G × F))
      | some (some candidate, messages, cache) => do
        let (valid, _) ← (verify (fun input => RandomOracle.query
          (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F)) input) input)
          g pk candidate.1 candidate.2).run cache
        pure (if valid && decide (candidate.1 ∉ messages) then some candidate else none)
      ).toMeasure μ := by
  let finish : Option (Option (M × G × F) × (List M × List ((M × G) × F))) →
      (PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F))
    | none | some (none, _) => pure none
    | some (some candidate, messages, cache) => do
      let (valid, _) ← (verify (fun input => RandomOracle.query
        (FreeM.lift (P := PFunctor.mk (M × G) (fun _ => F)) input) input)
        g pk candidate.1 candidate.2).run cache
      pure (if valid && decide (candidate.1 ∉ messages) then some candidate else none)
  let run tape := Option.map
    (fun out : Option (M × G × F) × ((List M × List ((M × G) × F)) × List F) =>
      (out.1, out.2.1)) <$>
    ((program.run.liftM (P := signatureEffects 0 M G F)
      (m := StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM))
      (fun | .inl op => isEmptyElim op | .inr op => privateSignatureHandler g pk op))
      (([], []), tape)).run
  have hpoint tape : privateForgery g pk program tape = run tape >>= finish := by
    have hfailure {State α : Type} {m : Type → Type} [Monad m] [Alternative m] :
        (failure : StateT State m α) = fun _ => failure := funext StateT.run_failure
    simp only [privateForgery, run, StateT.run', OptionT.run_map, bind_map_left]
    dsimp +instances only [Bind.bind, StateT.bind, OptionT.run, OptionT.bind, OptionT.mk]
    simp only [FreeM.bind_eq_bind, map_bind]
    congr 1
    funext out
    rcases out with _ | ⟨candidate, state, tape⟩
    · rfl
    · rcases state with ⟨messages, cache⟩
      cases candidate with
      | none => simp only [hfailure, Option.map_some, finish]; rfl
      | some candidate =>
        have h := run'_checkPrivateForgery g pk candidate (messages, cache) tape
        simp only [StateT.run', OptionT.run_map] at h
        dsimp only [OptionT.run] at h
        simpa only [finish, Option.map_some] using h
  have h := toMeasure_liftM_privateSignatureHandler μ sample g pk program.run ([], [])
    count hcount
  change FreeM.denote μ _ = FreeM.denote μ _
  simp only [hpoint, ← bind_assoc]
  conv_lhs => rw [FreeM.denote_bind_of_discrete]
  conv_rhs => rw [FreeM.denote_bind_of_discrete]
  exact congrArg (fun measure => measure.bind (fun out => FreeM.denote μ (finish out))) h


/-- The successful transcript of the entire saved-tape forgery experiment is the trace of
the hash-only source program. This is the pointwise premise needed by partial replay forking. -/
theorem privateForgery_traced (g pk : G)
    (program : OptionT (signatureEffects 0 M G F).FreeM (M × G × F))
    (privateScalars hashScalars : List F) :
    (do
      let (candidate, state) ← (program.run.liftM (P := signatureEffects 0 M G F)
        (m := StateT (((List M × List ((M × G) × F)) × (List F × List F)) ×
          List ((M × G) × F)) Option)
        (fun | .inl op => isEmptyElim op
             | .inr op => traceSeededCall (seededSignatureHandler g pk op)))
          ((([], []), privateScalars, hashScalars), [])
      let candidate ← candidate
      let (candidate, state) ← traceSeededCall (checkSeededForgery g pk candidate) state
      pure (candidate, state.2.map (fun event => (⟨event.1, event.2⟩ :
        Sigma (PFunctor.mk (M × G) (fun _ => F)).B)))) =
      (FreeM.runFromAnswers (FreeM.trace (privateForgery g pk program privateScalars))
        hashScalars).bind (fun out => out.1.map (fun candidate => (candidate, out.2))) := by
  have hfailure {State α : Type} {m : Type → Type} [Monad m] [Alternative m] :
      (failure : StateT State m α) = fun _ => failure := funext StateT.run_failure
  let handler : (op : (signatureEffects 0 M G F).A) →
      StateT ((List M × List ((M × G) × F)) × List F)
        (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) ((signatureEffects 0 M G F).B op)
    | .inl op => isEmptyElim op
    | .inr op => privateSignatureHandler g pk op
  let check : Option (M × G × F) → StateT ((List M × List ((M × G) × F)) × List F)
      (OptionT (PFunctor.mk (M × G) (fun _ => F)).FreeM) (M × G × F) := fun candidate =>
    match candidate with
    | none => failure
    | some candidate => checkPrivateForgery g pk candidate
  let source := program.run.liftM handler >>= check
  have hfull : interpretPrivateSignature source =
      (do
        let candidate ← program.run.liftM (P := signatureEffects 0 M G F)
          (m := StateT (((List M × List ((M × G) × F)) × (List F × List F)) ×
            List ((M × G) × F)) Option)
          (fun | .inl op => isEmptyElim op
               | .inr op => traceSeededCall (seededSignatureHandler g pk op))
        match candidate with
        | none => failure
        | some candidate => traceSeededCall (checkSeededForgery g pk candidate)) := by
    rw [show source = program.run.liftM handler >>= check from rfl,
      isMonadHom_interpretPrivateSignature.map_bind]
    congr 1
    · funext ⟨⟨state, privateScalars, hashScalars⟩, events⟩
      exact liftM_privateSignatureHandler_traced g pk program.run state
        privateScalars hashScalars events
    · funext candidate ⟨⟨state, privateScalars, hashScalars⟩, events⟩
      cases candidate with
      | none =>
        simp only [check, hfailure, interpretPrivateSignature]
        rfl
      | some candidate =>
        exact checkPrivateForgery_traced g pk candidate state privateScalars hashScalars events
  have h := congrArg (fun out => out.map (fun out =>
      (out.1, out.2.2.map (fun event => (⟨event.1, event.2⟩ :
        Sigma (PFunctor.mk (M × G) (fun _ => F)).B)))))
    (congrFun hfull ((([], []), privateScalars, hashScalars), []))
  rw [← FreeM.runTracedFromAnswers_eq]
  change _ = (FreeM.runTracedFromAnswers (Prod.fst <$> source (([], []), privateScalars))
    (hashScalars, [])).map (fun out => (out.1, out.2.2))
  rw [FreeM.isMonadHom_runTracedFromAnswers.map_map]
  dsimp +instances only [Bind.bind, StateT.bind, Functor.map, StateT.map] at h ⊢
  simp only [interpretPrivateSignature, hfailure, List.map_nil, Option.map_map,
    List.map_map, Function.comp_def, Sigma.eta, Option.map_bind] at h
  convert h.symm using 1
  · congr 1
    funext out
    rcases out with ⟨candidate, state⟩
    cases candidate <;> simp [Option.map_eq_bind]
  · simp [Option.map_eq_bind, Option.bind_assoc]

end Cslib.Crypto.Schnorr
