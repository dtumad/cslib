/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Reduction
public import Cslib.Crypto.RandomOracle.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Crypto.Primitives.Schnorr.Fork

/-!
# Sampling budgets for Schnorr experiments

Selected ambient operations and all hash and signing requests count toward the source budget.
A signing request uses at most two scalar draws. The bounds include key generation, final
verification, and both executions of the discrete-logarithm reduction.
-/

public section

namespace Cslib.Crypto.Schnorr

section Sampling

open PFunctor

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G] [DecidableEq M]

/-- Signing samples a nonce and, on a cache miss, one challenge. -/
theorem queryBoundP_sign_le (select : P.A → Bool) (sample : P.FreeM F) (g : G)
    (secret : F) (message : M) (cache : List ((M × G) × F)) :
    FreeM.queryBoundP select ((sign (monadLift sample) (RandomOracle.query sample)
      g secret message).run cache) ≤ 2 * FreeM.queryBoundP select sample := by
  simp only [sign, StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self,
    bind_assoc, pure_bind]
  apply (FreeM.queryBoundP_bind_le select _ _ (FreeM.queryBoundP select sample) ?_).trans
  · rw [two_mul]
  · intro nonce
    rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
    exact RandomOracle.queryBoundP_query_le select sample _ cache

/-- Verification needs at most one fresh cache entry. -/
theorem queryBoundP_verify_le (select : P.A → Bool) (sample : P.FreeM F) (g pk : G)
    (message : M) (signature : G × F) (cache : List ((M × G) × F)) :
    FreeM.queryBoundP select ((verify (RandomOracle.query sample)
      g pk message signature).run cache) ≤ FreeM.queryBoundP select sample := by
  simp only [verify, StateT.run_map, ← map_eq_pure_bind,
    FreeM.queryBoundP_map]
  exact RandomOracle.queryBoundP_query_le select sample _ cache

/-- The honest game charges for all adaptive requests, key generation, and final verification.
The factor two pays for the two draws of a signing request. -/
theorem queryBoundP_unforgeabilityExperiment (select : P.A → Bool) (sample : P.FreeM F)
    (hsample : FreeM.queryBoundP select sample ≤ 1) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (q : ℕ)
    (hqueries : ∀ pk, FreeM.queryBoundP (fun op : (signatureEffects P M G F).A =>
      match op with | .inl op => select op | .inr _ => true) (adversary pk) ≤ q) :
    FreeM.queryBoundP select (unforgeabilityExperiment sample g adversary) ≤ 2 * q + 2 := by
  let source := fun op : (signatureEffects P M G F).A =>
    match op with | .inl op => select op | .inr _ => true
  have hhandler secret (op : (signatureEffects P M G F).A) state :
      FreeM.queryBoundP select ((signatureHandler sample g secret op).run state) ≤
        if source op then 2 else 0 := by
    rcases state with ⟨messages, cache⟩
    rcases op with op | (input | message)
    · simp only [signatureHandler, StateT.run, ← map_eq_pure_bind, FreeM.queryBoundP_map,
        FreeM.queryBoundP_lift, source]
      split <;> norm_num
    · simp only [signatureHandler, StateT.run, ← map_eq_pure_bind, FreeM.queryBoundP_map,
        source, ↓reduceIte]
      exact (RandomOracle.queryBoundP_query_le select sample input cache).trans
        (hsample.trans (by norm_num))
    · simp only [signatureHandler, StateT.run, ← map_eq_pure_bind, FreeM.queryBoundP_map,
        source, ↓reduceIte]
      exact (queryBoundP_sign_le select sample g secret message cache).trans (by
        calc
          _ ≤ (2 : ℕ∞) * 1 := by gcongr
          _ = 2 := mul_one _)
  have hadversary pk secret : FreeM.queryBoundP select
      (((adversary pk).liftM (signatureHandler sample g secret)).run ([], [])) ≤ 2 * q := by
    exact (FreeM.queryBoundP_liftM_stateT_le_mul source select _ 2 (hhandler secret)
      (adversary pk) ([], [])).trans (by rw [mul_comm]; gcongr; exact hqueries pk)
  simp only [unforgeabilityExperiment, keygen, bind_assoc, pure_bind]
  apply (FreeM.queryBoundP_bind_le select _ _ (2 * q + 1) ?_).trans
  · exact (add_le_add hsample le_rfl).trans_eq (by ring)
  · intro secret
    apply (FreeM.queryBoundP_bind_le select _ _ 1 ?_).trans
    · exact add_le_add (hadversary _ secret) le_rfl
    · rintro ⟨⟨message, signature⟩, messages, cache⟩
      rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
      exact (queryBoundP_verify_le select sample g _ message signature cache).trans hsample

/-- Simulated signing samples one challenge and one response, even when programming fails. -/
theorem queryBoundP_simulateSign_le (select : P.A → Bool) (sample : P.FreeM F) (g pk : G)
    (message : M) (cache : List ((M × G) × F)) :
    FreeM.queryBoundP select ((simulateSign sample g pk message).run cache).run ≤
      2 * FreeM.queryBoundP select sample := by
  simp only [simulateSign, simulateTranscript, StateT.run, OptionT.run, OptionT.mk,
    bind_assoc, pure_bind]
  apply (FreeM.queryBoundP_bind_le select sample _ (FreeM.queryBoundP select sample) ?_).trans
  · rw [two_mul]
  · intro challenge
    simp only [← map_eq_pure_bind, FreeM.queryBoundP_map, le_refl]

/-- The signing simulator and final verification use at most two draws per source request,
plus the verifier's last draw. Ambient operations may include the adversary's own sampling. -/
theorem queryBoundP_simulatedForgery_le {Q : PFunctor.{0, 0}}
    (select : P.A → Bool) (target : Q.A → Bool)
    (ambient : (op : P.A) → Q.FreeM (P.B op))
    (hambient : ∀ op, FreeM.queryBoundP target (ambient op) ≤ if select op then 1 else 0)
    (sample : Q.FreeM F) (hsample : FreeM.queryBoundP target sample ≤ 1)
    (hashSample : M × G → Q.FreeM F)
    (hhash : ∀ input, FreeM.queryBoundP target (hashSample input) ≤ 1) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (q : ℕ)
    (hqueries : FreeM.queryBoundP (fun op : (signatureEffects P M G F).A =>
      match op with | .inl op => select op | .inr _ => true) (adversary pk) ≤ q) :
    FreeM.queryBoundP target
      (simulatedForgery ambient sample hashSample g pk adversary).run ≤ 2 * q + 1 := by
  let source := fun op : (signatureEffects P M G F).A =>
    match op with | .inl op => select op | .inr _ => true
  let handler := simulatedSignatureHandler ambient sample hashSample g pk
  have hhandler (op : (signatureEffects P M G F).A) state :
      FreeM.queryBoundP target ((handler op).run state).run ≤ if source op then 2 else 0 := by
    rcases state with ⟨messages, cache⟩
    rcases op with op | (input | message)
    · simp only [handler, simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        ← map_eq_pure_bind, FreeM.queryBoundP_map, source]
      exact (hambient op).trans (by split <;> norm_num)
    · simp only [handler, simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        ← map_eq_pure_bind, FreeM.queryBoundP_map, source, ↓reduceIte]
      exact (RandomOracle.queryBoundP_query_le target _ input cache).trans
        ((hhash input).trans (by norm_num))
    · simp only [handler, simulatedSignatureHandler, StateT.run, OptionT.run,
        Bind.bind, OptionT.bind, OptionT.mk]
      rw [FreeM.bind_eq_bind]
      apply (FreeM.queryBoundP_bind_le target _ _ 0 ?_).trans
      · simp only [add_zero, source, ↓reduceIte]
        exact (queryBoundP_simulateSign_le target sample g pk message cache).trans (by
          calc
            _ ≤ (2 : ℕ∞) * 1 := by gcongr
            _ = 2 := mul_one _)
      · intro out
        cases out <;> exact le_rfl
  have hadversary := FreeM.queryBoundP_liftM_stateT_optionT_le_mul source target handler 2
    hhandler (adversary pk) ([], [])
  simp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk]
  rw [FreeM.bind_eq_bind]
  apply (FreeM.queryBoundP_bind_le target _ _ 1 ?_).trans
  · apply add_le_add (hadversary.trans ?_) le_rfl
    rw [mul_comm]
    gcongr
  · intro out
    cases out with
    | none => exact zero_le
    | some out =>
      rcases out with ⟨⟨message, signature⟩, messages, cache⟩
      simp only [verify, StateT.run_bind, StateT.run_pure, monadLift, MonadLift.monadLift,
        OptionT.lift, OptionT.mk, FreeM.bind_eq_bind, bind_assoc, pure_bind]
      apply (FreeM.queryBoundP_bind_le target _ _ 0 ?_).trans
      · rw [add_zero]
        exact (RandomOracle.queryBoundP_query_le target _ _ cache).trans (hhash _)
      · rintro ⟨challenge, cache'⟩
        split <;> exact le_rfl

variable [DecidableEq F]

/-- Closing all hash effects after forking pays for both executions. This counts simulator
draws as well as fresh hash answers, including the final verifier queries. -/
theorem queryBoundP_dlogReduction (select : P.A → Bool) (sample : P.FreeM F)
    (hsample : FreeM.queryBoundP select sample ≤ 1) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (q : ℕ)
    (hqueries : FreeM.queryBoundP (fun op : (signatureEffects P M G F).A =>
      match op with | .inl op => select op | .inr _ => true) (adversary pk) ≤ q) :
    FreeM.queryBoundP select (dlogReduction sample g adversary pk) ≤ 4 * q + 2 := by
  let target := fun op : (P + PFunctor.mk (M × G) (fun _ => F)).A =>
    match op with | .inl op => select op | .inr _ => true
  let ambient := fun op : P.A =>
    FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
  have hambient op : FreeM.queryBoundP target (ambient op) ≤ if select op then 1 else 0 := by
    simp [ambient, target]
  have hdraw : FreeM.queryBoundP target (sample.liftM ambient) ≤ 1 :=
    (FreeM.queryBoundP_liftM_le select target ambient hambient sample).trans hsample
  have hsim := queryBoundP_simulatedForgery_le select target ambient hambient
    (sample.liftM ambient) hdraw
    (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
    (fun input => by
      simp [FreeM.queryBoundP_lift (P := P + PFunctor.mk (M × G) (fun _ => F)), target])
    g pk adversary q hqueries
  unfold dlogReduction
  apply (FreeM.queryBoundP_liftM_le target select _ ?_ _).trans
  · simp only [signatureExtractor, forkExtractor, FreeM.queryBoundP_map]
    apply (FreeM.queryBoundP_fork_le target _ _ _).trans
    rw [FreeM.queryBoundP_trace]
    calc
      _ ≤ 2 * (2 * (q : ℕ∞) + 1) := by gcongr
      _ = _ := by ring
  · rintro (op | input)
    · simp [target]
    · exact hsample

/-- The complete discrete-logarithm experiment also samples its challenge secret. -/
theorem queryBoundP_dlogExperiment (select : P.A → Bool) (sample : P.FreeM F)
    (hsample : FreeM.queryBoundP select sample ≤ 1) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (q : ℕ)
    (hqueries : ∀ pk, FreeM.queryBoundP (fun op : (signatureEffects P M G F).A =>
      match op with | .inl op => select op | .inr _ => true) (adversary pk) ≤ q) :
    FreeM.queryBoundP select
      (DiscreteLog.experiment sample g (dlogReduction sample g adversary)) ≤ 4 * q + 3 := by
  unfold DiscreteLog.experiment
  apply (FreeM.queryBoundP_bind_le select _ _ (4 * q + 2) ?_).trans
  · exact (add_le_add hsample le_rfl).trans_eq (by ring)
  · intro secret
    rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
    exact queryBoundP_dlogReduction select sample hsample g _ adversary q (hqueries _)

end Sampling

section HashQueries

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

end HashQueries

end Cslib.Crypto.Schnorr
