/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Fork
public import Cslib.Crypto.RandomOracle.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Cost.StateT

/-! # The signing simulator preserves the adversary's hash-query budget -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G] [DecidableEq M]

private theorem queryBoundP_simulateSign_eq_zero (select : P.A → Bool) (sample : P.FreeM F)
    (hsample : FreeM.queryBoundP select sample = 0) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) :
    FreeM.queryBoundP select ((simulateSign sample g pk message).run cache).run = 0 := by
  simp only [simulateSign, simulateTranscript, StateT.run, OptionT.run, OptionT.mk,
    bind_assoc, pure_bind]
  apply le_antisymm _ bot_le
  apply (FreeM.queryBoundP_bind_le select sample _ 0 ?_).trans
  · simp [hsample]
  · intro challenge
    simp only [← map_eq_pure_bind, FreeM.queryBoundP_map, hsample, le_refl]

/-- Fresh hash draws in the compiled signing experiment are bounded by the source adversary's
hash requests plus the final verifier query. Sampling coins and signing requests do not count. -/
theorem queryBoundP_simulatedForgery (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    let ambient := fun op : P.A =>
      FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
    let program := (simulatedForgery ambient (sample.liftM ambient)
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run
    FreeM.queryBoundP (fun op : (P + PFunctor.mk (M × G) (fun _ => F)).A => op.isRight)
      program ≤
      FreeM.queryBoundP (fun op : (signatureEffects P M G F).A => match op with
        | .inr (.inl _) => true | _ => false) (adversary pk) + 1 := by
  let ambient := fun op : P.A =>
    FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
  let hashSample := fun input =>
    FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input)
  let select := fun op : (P + PFunctor.mk (M × G) (fun _ => F)).A => op.isRight
  let source := fun op : (signatureEffects P M G F).A => match op with
    | .inr (.inl _) => true | _ => false
  let handler := simulatedSignatureHandler ambient (sample.liftM ambient) hashSample g pk
  have hsample : FreeM.queryBoundP select (sample.liftM ambient) = 0 := by
    apply le_antisymm _ bot_le
    simpa using FreeM.queryBoundP_liftM_le (fun _ => false) select ambient
      (fun op => by simp [ambient, select]) sample
  have hhandler (op : (signatureEffects P M G F).A) (state) :
      FreeM.queryBoundP select ((handler op).run state).run ≤ if source op then 1 else 0 := by
    rcases state with ⟨messages, cache⟩
    cases op with
    | inl op =>
      simp [handler, simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        ambient, select, source]
    | inr op =>
      cases op with
      | inl input =>
        dsimp only [handler, simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk]
        rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
        exact (RandomOracle.queryBoundP_query_le select _ input cache).trans (by
          simpa only [hashSample, select, source, Sum.isRight, Bool.true_eq, ↓reduceIte] using
            (FreeM.queryBoundP_lift (P := P + PFunctor.mk (M × G) (fun _ => F))
              select (.inr input)).le)
      | inr message =>
        dsimp only [handler, simulatedSignatureHandler, StateT.run, OptionT.run,
          Bind.bind, OptionT.instMonad, OptionT.bind, OptionT.mk]
        rw [FreeM.bind_eq_bind]
        apply (FreeM.queryBoundP_bind_le select _ _ 0 ?_).trans
        · have hzero := queryBoundP_simulateSign_eq_zero select _ hsample g pk message cache
          simpa only [StateT.run, OptionT.run, add_zero, source, Bool.false_eq_true, ↓reduceIte]
            using hzero.le
        · intro out
          cases out <;> exact le_rfl
  have hadversary := FreeM.queryBoundP_liftM_stateT_le source select handler hhandler
    (adversary pk) ([], [])
  dsimp only
  simp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk]
  rw [FreeM.bind_eq_bind]
  apply (FreeM.queryBoundP_bind_le select _ _ 1 ?_).trans
  · exact add_le_add hadversary le_rfl
  · intro out
    cases out with
    | none => exact zero_le
    | some out =>
      rcases out with ⟨⟨message, commitment, response⟩, messages, cache⟩
      simp only [verify, StateT.run_bind, StateT.run_pure, monadLift, MonadLift.monadLift,
        OptionT.lift, OptionT.mk, FreeM.bind_eq_bind, bind_assoc, pure_bind]
      apply (FreeM.queryBoundP_bind_le select _ _ 0 ?_).trans
      · rw [add_zero]
        exact (RandomOracle.queryBoundP_query_le select _ _ cache).trans (by
          simpa only [select, Sum.isRight, Bool.true_eq, ↓reduceIte] using
            (FreeM.queryBoundP_lift (P := P + PFunctor.mk (M × G) (fun _ => F))
              select (.inr (message, commitment))).le)
      · rintro ⟨challenge, cache'⟩
        split <;> exact le_rfl

end Cslib.Crypto.Schnorr
