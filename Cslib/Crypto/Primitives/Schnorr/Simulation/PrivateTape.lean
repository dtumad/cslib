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
