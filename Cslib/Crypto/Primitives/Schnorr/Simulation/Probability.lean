/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation
public import Cslib.Foundations.MeasureTheory.Abort
public import Cslib.Foundations.Data.PFunctor.Free.Measure.StateT

/-! # The cumulative error of simulating adaptive Schnorr signing queries -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory MonadAttach
open scoped ENNReal

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq M] [DecidableEq G]

/-- The honest handler adds at most one entry to the random-oracle cache per operation, and only for
hash and signing queries. -/
theorem signatureHandler_cache_length (sample : P.FreeM F) (g : G) (secret : F)
    (op : (signatureEffects P M G F).A) (state : List M × List ((M × G) × F))
    (out : (signatureEffects P M G F).B op × (List M × List ((M × G) × F)))
    (h : CanReturn ((signatureHandler sample g secret op).run state) out) :
    out.2.2.length ≤ state.2.length + op.isRight.toNat := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl op =>
    obtain ⟨answer, _, rfl⟩ := (FreeM.canReturn_bind _ _ _).mp h
    exact le_rfl
  | inr op =>
    cases op with
    | inl input =>
      obtain ⟨result, hquery, rfl⟩ := (FreeM.canReturn_bind _ _ _).mp h
      exact RandomOracle.length_le_of_canReturn sample input cache hquery
    | inr message =>
      obtain ⟨signature, hsign, rfl⟩ := (FreeM.canReturn_bind _ _ _).mp h
      change CanReturn ((sign (monadLift sample) (RandomOracle.query sample)
        g secret message).run cache) signature at hsign
      simp only [sign, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind] at hsign
      obtain ⟨nonce, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp hsign
      obtain ⟨result, hquery, rfl⟩ := (FreeM.canReturn_bind _ _ _).mp h
      exact RandomOracle.length_le_of_canReturn sample (message, nonce • g) cache hquery

variable
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]
  [MeasurableSpace (List ((M × G) × F))] [DiscreteMeasurableSpace (List ((M × G) × F))]

/-- The one-query simulation error also bounds any continuation whose success probability is
at most one, including continuations depending on the entire signature/cache pair. -/
theorem lintegral_sign_le_simulateSign_add (sample : P.FreeM F) (g : G) (secret : F)
    (message : M) (cache : List ((M × G) × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ)
    (post : (G × F) × List ((M × G) × F) → ℝ≥0∞) (hpost : ∀ out, post out ≤ 1) :
    (∫⁻ out, post out ∂FreeM.toMeasure
      ((sign (monadLift sample) (RandomOracle.query sample) g secret message).run cache) μ) ≤
    (∫⁻ out, out.elim 0 post ∂FreeM.toMeasure
      ((simulateSign sample g (secret • g) message).run cache).run μ) +
      cache.length / (Nat.card F : ℝ≥0∞) := by
  have hbad := toMeasure_simulateSign_none_le μ sample g (secret • g) message cache hg hsample
  rw [toMeasure_simulateSign μ sample g secret message cache hsample,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)] at hbad
  rw [toMeasure_simulateSign μ sample g secret message cache hsample]
  have h := lintegral_le_lintegral_abort_add
    (FreeM.toMeasure ((sign (monadLift sample) (RandomOracle.query sample)
      g secret message).run cache) μ)
    (fun out => decide (cache.lookup (message, out.1.1) = none)) post hpost
  simp only [Bool.decide_iff, decide_eq_false_iff_not] at h
  apply h.trans
  apply add_le_add le_rfl
  convert hbad using 1
  congr 1
  ext out
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  split <;> simp_all [-List.lookup_eq_none_iff]

variable [∀ op, IsProbabilityMeasure (μ op)] [∀ op, Countable (P.B op)]
  [MeasurableSpace (List M)] [DiscreteMeasurableSpace (List M)]

/-- Simulating an adaptive program loses at most `qS` times the maximum cache-occupancy
fraction. The total query bound `q` counts hash and signing requests, excluding ambient effects. -/
theorem lintegral_liftM_signatureHandler_le {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α]
    (sample : P.FreeM F) (g : G) (secret : F)
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ)
    (x : (signatureEffects P M G F).FreeM α)
    (messages : List M) (cache : List ((M × G) × F)) (qS q : ℕ)
    (hsign : FreeM.queryBoundP isSignQuery x ≤ qS)
    (hqueries : FreeM.queryBoundP (fun op : (signatureEffects P M G F).A => op.isRight) x ≤ q)
    (post : α × (List M × List ((M × G) × F)) → ℝ≥0∞) (hpost : ∀ out, post out ≤ 1) :
    (∫⁻ out, post out ∂FreeM.toMeasure ((x.liftM (signatureHandler sample g secret)).run
      (messages, cache)) μ) ≤
    (∫⁻ out, out.elim 0 post ∂FreeM.toMeasure
      ((x.liftM (simulatedSignatureHandler FreeM.lift sample (fun _ => sample)
        g (secret • g))).run (messages, cache)).run μ) +
      qS * (((cache.length + q : ℕ) : ℝ≥0∞) / Nat.card F) := by
  let : ∀ op, MeasurableSpace ((signatureEffects P M G F).B op) := by
    rintro (op | (input | message))
    · exact inferInstanceAs (MeasurableSpace (P.B op))
    · exact inferInstanceAs (MeasurableSpace F)
    · exact inferInstanceAs (MeasurableSpace (G × F))
  let : ∀ op, DiscreteMeasurableSpace ((signatureEffects P M G F).B op) := by
    rintro (op | (input | message))
    · exact inferInstanceAs (DiscreteMeasurableSpace (P.B op))
    · exact inferInstanceAs (DiscreteMeasurableSpace F)
    · exact inferInstanceAs (DiscreteMeasurableSpace (G × F))
  let : ∀ op, Countable ((signatureEffects P M G F).B op) := by
    rintro (op | (input | message))
    · exact inferInstanceAs (Countable (P.B op))
    · exact inferInstanceAs (Countable F)
    · exact inferInstanceAs (Countable (G × F))
  apply FreeM.lintegral_liftM_stateT_le_add μ (signatureHandler sample g secret)
    (simulatedSignatureHandler FreeM.lift sample (fun _ => sample) g (secret • g))
    isSignQuery (fun op => op.isRight) (fun state => state.2.length) (cache.length + q)
    (((cache.length + q : ℕ) : ℝ≥0∞) / Nat.card F)
    (signatureHandler_cache_length sample g secret) _ x (messages, cache) qS _ hsign post hpost
  · intro op state hstate f hf
    rcases state with ⟨messages', cache'⟩
    cases op with
    | inl op =>
      simp only [signatureHandler, simulatedSignatureHandler, StateT.run, OptionT.run,
        OptionT.mk, isSignQuery, Bool.false_eq_true, ↓reduceIte, add_zero,
        FreeM.toMeasure_bind_of_discrete', FreeM.toMeasure_pure,
        Measure.lintegral_bind Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable, lintegral_dirac' _ Measurable.of_discrete,
        Option.elim_some, le_refl]
    | inr op =>
      cases op with
      | inl input =>
        simp only [signatureHandler, simulatedSignatureHandler, StateT.run, OptionT.run,
          OptionT.mk, isSignQuery, Bool.false_eq_true, ↓reduceIte, add_zero,
          FreeM.toMeasure_bind_of_discrete', FreeM.toMeasure_pure,
          Measure.lintegral_bind Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aemeasurable, lintegral_dirac' _ Measurable.of_discrete,
          Option.elim_some, le_refl]
      | inr message =>
        have h := lintegral_sign_le_simulateSign_add μ sample g secret message cache' hg hsample
          (fun out => f (out.1, message :: messages', out.2)) (fun out => hf _)
        dsimp only [signatureHandler, simulatedSignatureHandler, StateT.run, OptionT.run,
          Bind.bind, OptionT.instMonad, OptionT.bind, OptionT.mk]
        simp only [FreeM.toMeasure_bind _ _ Measurable.of_discrete, FreeM.toMeasure_pure,
          Measure.lintegral_bind Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aemeasurable, lintegral_dirac' _ Measurable.of_discrete]
        apply h.trans
        apply add_le_add
        · apply le_of_eq
          apply lintegral_congr
          intro out
          cases out with
          | none => simp [lintegral_dirac' _ Measurable.of_discrete]
          | some out =>
            change f (out.1, message :: messages', out.2) =
              ∫⁻ result, result.elim 0 f
                ∂FreeM.toMeasure (pure (some (out.1, message :: messages', out.2))) μ
            simp [lintegral_dirac' _ Measurable.of_discrete]
        · dsimp only [isSignQuery]
          simp only [↓reduceIte]
          gcongr
  · simpa only [Nat.cast_add] using add_le_add (le_rfl : (cache.length : ℕ∞) ≤ _) hqueries

/-- Honest EUF-CMA success is at most simulated success plus the cumulative programming error.
The simulator receives only the public key; final verification uses the same cache in both games. -/
theorem toMeasure_unforgeabilityExperiment_le_simulatedForgery_add
    (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ) (qS qH : ℕ)
    (hsign : ∀ pk, FreeM.queryBoundP isSignQuery (adversary pk) ≤ qS)
    (hhash : ∀ pk, FreeM.queryBoundP isHashQuery (adversary pk) ≤ qH) :
    FreeM.toMeasure (unforgeabilityExperiment sample g adversary) μ {true} ≤
      (∫⁻ secret, FreeM.toMeasure
          (simulatedForgery FreeM.lift sample (fun _ => sample) g (secret • g) adversary).run μ
          {candidate : Option (M × G × F) | candidate.isSome} ∂FreeM.toMeasure sample μ) +
        qS * (qH + qS) / (Nat.card F : ℝ≥0∞) := by
  let finish := fun (pk : G) (out : (M × G × F) × (List M × List ((M × G) × F))) => do
    let (valid, _) ← (verify (RandomOracle.query sample) g pk out.1.1 out.1.2).run out.2.2
    pure (valid && decide (out.1.1 ∉ out.2.1))
  let post := fun pk out => FreeM.toMeasure (finish pk out) μ {true}
  have hpost pk out : post pk out ≤ 1 := prob_le_one
  have hqueries pk : FreeM.queryBoundP
      (fun op : (signatureEffects P M G F).A => op.isRight) (adversary pk) ≤
        ((qH + qS : ℕ) : ℕ∞) := by
    have heq : (fun op : (signatureEffects P M G F).A => op.isRight) =
        fun op => isHashQuery op || isSignQuery op := by
      funext op
      rcases op with op | (input | message) <;> rfl
    rw [heq, Nat.cast_add]
    exact (FreeM.queryBoundP_or_le isHashQuery isSignQuery _).trans
      (add_le_add (hhash pk) (hsign pk))
  have hsim (secret : F) :
      FreeM.toMeasure
          (simulatedForgery FreeM.lift sample (fun _ => sample) g (secret • g) adversary).run μ
          {candidate : Option (M × G × F) | candidate.isSome} =
        ∫⁻ out, out.elim 0 (post (secret • g)) ∂FreeM.toMeasure (((adversary (secret • g)).liftM
            (simulatedSignatureHandler FreeM.lift sample (fun _ => sample) g (secret • g))).run
              ([], [])).run μ := by
    simp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk,
      FreeM.toMeasure_bind _ _ Measurable.of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro out
    cases out with
    | none => simp
    | some out =>
      rcases out with ⟨⟨message, signature⟩, messages, cache⟩
      simp only [post, finish, Option.elim_some, monadLift, MonadLift.monadLift,
        OptionT.lift, OptionT.mk, FreeM.bind_eq_bind, bind_assoc, pure_bind,
        FreeM.toMeasure_bind_of_discrete',
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      apply lintegral_congr
      rintro ⟨valid, cache'⟩
      cases valid <;> by_cases hfresh : message ∈ messages <;>
        simp only [hfresh, not_true_eq_false, not_false_eq_true, decide_true, decide_false,
          Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;>
        change (FreeM.toMeasure (pure _) μ)
          {candidate : Option (M × G × F) | candidate.isSome} = _ <;>
        simp
  have hlocal (secret : F) := lintegral_liftM_signatureHandler_le μ sample g secret hg hsample
    (adversary (secret • g)) [] [] qS (qH + qS) (hsign _) (hqueries _)
      (post (secret • g)) (hpost _)
  simp only [List.length_nil, Nat.zero_add, Nat.cast_add, ← mul_div_assoc] at hlocal
  simp_rw [← hsim] at hlocal
  calc
    _ = ∫⁻ secret, ∫⁻ out, post (secret • g) out ∂FreeM.toMeasure
          (((adversary (secret • g)).liftM (signatureHandler sample g secret)).run ([], [])) μ
          ∂FreeM.toMeasure sample μ := by
      simp only [unforgeabilityExperiment, keygen, bind_assoc, pure_bind, post, finish,
        FreeM.toMeasure_bind_of_discrete',
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      simp only [StateT.run]
    _ ≤ ∫⁻ secret, FreeM.toMeasure
          (simulatedForgery FreeM.lift sample (fun _ => sample) g (secret • g) adversary).run μ
          {candidate : Option (M × G × F) | candidate.isSome} +
        qS * (qH + qS) / (Nat.card F : ℝ≥0∞) ∂FreeM.toMeasure sample μ :=
      lintegral_mono hlocal
    _ = _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

end Cslib.Crypto.Schnorr
