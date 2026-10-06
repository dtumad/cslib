/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Reduction
public import Cslib.Crypto.Primitives.Schnorr.Fork.Measure
public import Cslib.Crypto.Primitives.Schnorr.Simulation.Probability

/-!
# Concrete EUF-CMA security of Schnorr signatures

An adaptive adversary making at most `qS` signing and `qH` hash requests gives a concrete
discrete-logarithm reduction. Signing simulation loses at most `qS * (qH + qS) / |F|`.
Forking includes the verifier's last hash query, so its denominator is `qH + 1`.

These are finite probability bounds for the actual programs; `Schnorr.Asymptotic` turns them into
security against admissible forgers.
-/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]

/-- The closed reduction has the adaptive forking bound with independent uniform hash answers. -/
theorem le_toMeasure_dlogReduction (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (qH : ℕ)
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ)
    (hhash : FreeM.queryBoundP isHashQuery (adversary pk) ≤ qH) :
    let ε := FreeM.toMeasure
      (simulatedForgery FreeM.lift sample (fun _ => sample) g pk adversary).run μ
        {candidate : Option (M × G × F) | candidate.isSome}
    ε * (ε / (qH + 1) - 1 / Nat.card F) ≤
      FreeM.toMeasure (dlogReduction sample g adversary pk) μ
        {result : Option F | result.isSome} := by
  let : ∀ op, MeasurableSpace ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := by
    rintro (op | input)
    · exact inferInstanceAs (MeasurableSpace (P.B op))
    · exact inferInstanceAs (MeasurableSpace F)
  let : ∀ op, MeasurableSingletonClass ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := by
    rintro (op | input)
    · exact inferInstanceAs (MeasurableSingletonClass (P.B op))
    · exact inferInstanceAs (MeasurableSingletonClass F)
  let : ∀ op, Countable ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := by
    rintro (op | input)
    · exact inferInstanceAs (Countable (P.B op))
    · exact inferInstanceAs (Countable F)
  let close : (op : (P + PFunctor.mk (M × G) (fun _ => F)).A) →
      P.FreeM ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := fun
    | .inl op => FreeM.lift op
    | .inr _ => sample
  let ν := fun op => FreeM.toMeasure (close op) μ
  have hanswer input challenge : ν (.inr input) {challenge} ≤ 1 / (Nat.card F : ℝ≥0∞) := by
    let := Fintype.ofFinite F
    simp [ν, close, hsample, uniformOn_univ, Nat.card_eq_fintype_card]
  have hbound := le_toMeasure_signatureExtractor_of_queryBoundP ν sample g pk adversary qH
    (1 / Nat.card F) hanswer hhash
  dsimp only at hbound ⊢
  have hsim := congrArg (FreeM.toMeasure · μ) (liftM_simulatedForgery_hash sample g pk adversary)
  dsimp only at hsim
  rw [FreeM.toMeasure_liftM] at hsim
  change FreeM.toMeasure _ ν = _ at hsim
  rw [hsim] at hbound
  rw [dlogReduction, FreeM.toMeasure_liftM]
  exact hbound

omit [Countable P.A] [∀ op, IsProbabilityMeasure (μ op)]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] in
/-- The reduction never returns an incorrect logarithm, so explicit success is exactly success
in the ordinary discrete-logarithm experiment. -/
theorem toMeasure_dlogReduction_experiment (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    FreeM.toMeasure (DiscreteLog.experiment sample g (dlogReduction sample g adversary)) μ {true} =
      ∫⁻ secret, FreeM.toMeasure (dlogReduction sample g adversary (secret • g)) μ
        {result : Option F | result.isSome} ∂FreeM.toMeasure sample μ := by
  rw [DiscreteLog.experiment, FreeM.toMeasure_bind_of_discrete',
    Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro secret
  rw [← map_eq_pure_bind, ← FreeM.map_eq_map,
    FreeM.toMeasure_map _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  apply measure_congr
  filter_upwards [FreeM.ae_canReturn μ (dlogReduction sample g adversary (secret • g))]
    with result hresult
  apply propext
  cases result with
  | none => simp
  | some answer => simp [dlogReduction_sound sample g adversary (secret • g) hresult]

/-- Concrete EUF-CMA reduction for Schnorr in the random-oracle model. The only loss before
forking is the proved cumulative signing-collision bound; no simulation or forking conclusion
is assumed. The truncated subtraction also covers adversaries below the collision threshold. -/
theorem euf_cma_bound (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ) (qS qH : ℕ)
    (hsign : ∀ pk, FreeM.queryBoundP isSignQuery (adversary pk) ≤ qS)
    (hhash : ∀ pk, FreeM.queryBoundP isHashQuery (adversary pk) ≤ qH) :
    let ε := FreeM.toMeasure (unforgeabilityExperiment sample g adversary) μ {true}
    let ε' := ε - qS * (qH + qS) / (Nat.card F : ℝ≥0∞)
    ε' * (ε' / (qH + 1) - 1 / Nat.card F) ≤
      FreeM.toMeasure (DiscreteLog.experiment sample g (dlogReduction sample g adversary)) μ
        {true} := by
  let : MeasurableSpace (List M) := ⊤
  let : MeasurableSpace (List ((M × G) × F)) := ⊤
  let success := fun secret : F => FreeM.toMeasure
    (simulatedForgery FreeM.lift sample (fun _ => sample) g (secret • g) adversary).run μ
      {candidate : Option (M × G × F) | candidate.isSome}
  have hsimulation :=
    toMeasure_unforgeabilityExperiment_le_simulatedForgery_add μ sample g adversary
    hg hsample qS qH hsign hhash
  have hε := tsub_le_iff_right.mpr hsimulation
  have haverage := ENNReal.mul_sub_lintegral_le (μ := FreeM.toMeasure sample μ)
    (f := success) Measurable.of_discrete.aemeasurable (fun _ => prob_le_one)
    (qH + 1) (1 / Nat.card F)
  dsimp only
  calc
    _ ≤ (∫⁻ secret, success secret ∂FreeM.toMeasure sample μ) *
        ((∫⁻ secret, success secret ∂FreeM.toMeasure sample μ) / (qH + 1) - 1 / Nat.card F) := by
      gcongr
    _ ≤ ∫⁻ secret, success secret * (success secret / (qH + 1) - 1 / Nat.card F)
        ∂FreeM.toMeasure sample μ := haverage
    _ ≤ ∫⁻ secret, FreeM.toMeasure (dlogReduction sample g adversary (secret • g)) μ
        {result : Option F | result.isSome} ∂FreeM.toMeasure sample μ :=
      lintegral_mono fun secret => le_toMeasure_dlogReduction μ sample g (secret • g) adversary
        qH hsample (hhash _)
    _ = _ := (toMeasure_dlogReduction_experiment μ sample g adversary).symm

/-- The concrete EUF-CMA bound in its square-root form. The hash budget includes final
verification, and the signing term accounts for all adaptive programming collisions. -/
theorem euf_cma_bound_sqrt (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.toMeasure sample μ = uniformOn Set.univ) (qS qH : ℕ)
    (hsign : ∀ pk, FreeM.queryBoundP isSignQuery (adversary pk) ≤ qS)
    (hhash : ∀ pk, FreeM.queryBoundP isHashQuery (adversary pk) ≤ qH) :
    (FreeM.toMeasure (unforgeabilityExperiment sample g adversary) μ {true}).toReal ≤
      (qS : ℝ) * (qH + qS) / Nat.card F + (qH + 1) / Nat.card F +
        Real.sqrt ((qH + 1) *
          (FreeM.toMeasure (DiscreteLog.experiment sample g
            (dlogReduction sample g adversary)) μ {true}).toReal) := by
  have hcard : (Nat.card F : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F)).ne'
  have hbound := ENNReal.toReal_le_mul_add_sqrt_of_mul_sub_le
    (by positivity) (by simp) (by finiteness) (measure_ne_top _ _)
    (euf_cma_bound μ sample g adversary hg hsample qS qH hsign hhash)
  have hsub := ENNReal.le_toReal_sub
    (a := FreeM.toMeasure (unforgeabilityExperiment sample g adversary) μ {true})
    (b := qS * (qH + qS) / (Nat.card F : ℝ≥0∞)) (by finiteness)
  simp [ENNReal.toReal_add, ENNReal.toReal_mul, div_eq_mul_inv] at hbound hsub ⊢
  linarith

end Cslib.Crypto.Schnorr
