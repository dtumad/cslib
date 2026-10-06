/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.MeasureTheory.Quadratic
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Independent successful samples with distinct challenges -/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Two independent successful runs have probability at least `p² - p*r` of carrying different
challenges, when every challenge fiber has measure at most `r`. -/
theorem sq_sub_mul_le_prod (μ : Measure α) (challenge : α → F)
    (s : Set α) (r : ℝ≥0∞) (h : ∀ c, μ {a | challenge a = c} ≤ r) :
    μ s ^ 2 - μ s * r ≤ (μ.prod μ) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ challenge p.1 ≠ challenge p.2} := by
  classical
  have hcollision : (μ.prod μ) {p | p.1 ∈ s ∧ challenge p.1 = challenge p.2} ≤ μ s * r := by
    rw [prod_apply MeasurableSet.of_discrete]
    calc
      _ ≤ ∫⁻ a, s.indicator (fun _ => r) a ∂μ := by
        apply lintegral_mono
        intro a
        by_cases ha : a ∈ s
        · simpa [Set.preimage, ha, Set.indicator, eq_comm] using h (challenge a)
        · simp [Set.preimage, ha, Set.indicator]
      _ = _ := by rw [lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]
  apply tsub_le_iff_right.mpr
  calc
    _ = (μ.prod μ) (s ×ˢ s) := by rw [prod_prod, pow_two]
    _ ≤ (μ.prod μ) ({p | p.1 ∈ s ∧ p.2 ∈ s ∧ challenge p.1 ≠ challenge p.2} ∪
        {p | p.1 ∈ s ∧ challenge p.1 = challenge p.2}) := by
      apply measure_mono
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      by_cases hab : challenge a = challenge b
      · exact Or.inr ⟨ha, hab⟩
      · exact Or.inl ⟨ha, hb, hab⟩
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hcollision)

/-- Reusing a random prefix and sampling two independent suffixes gives the same quadratic
bound. The prefix is shared inside the product, not sampled independently for the two runs. -/
theorem sq_lintegral_sub_mul_le_prod {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : S → Measure α)
    (challenge : α → F) (good : S → Set α) (r : ℝ≥0∞)
    (h : ∀ state c, ν state {a | challenge a = c} ≤ r) :
    (∫⁻ state, ν state (good state) ∂μ) ^ 2 - (∫⁻ state, ν state (good state) ∂μ) * r ≤
      ∫⁻ state, ((ν state).prod (ν state))
        {p | p.1 ∈ good state ∧ p.2 ∈ good state ∧ challenge p.1 ≠ challenge p.2} ∂μ :=
  (ENNReal.sq_lintegral_sub_mul_le Measurable.of_discrete.aemeasurable r).trans
    (lintegral_mono fun state => sq_sub_mul_le_prod _ challenge _ r (h state))

end MeasureTheory.Measure
