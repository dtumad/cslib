/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Real.Sqrt

/-! # Quadratic bounds for nonnegative integrals

Adapted from VCVio's `ToMathlib.MeasureTheory.Integral.Quadratic`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ENNReal

/-- Inverting a divided quadratic bound gives the usual square-root loss. Truncated
subtraction needs no separate assumption that the success probability exceeds the loss. -/
theorem toReal_le_mul_add_sqrt_of_mul_sub_le {ε q r p : ℝ≥0∞}
    (hq : q ≠ 0) (hq_top : q ≠ ∞) (hr : r ≠ ∞) (hp : p ≠ ∞)
    (h : ε * (ε / q - r) ≤ p) :
    ε.toReal ≤ q.toReal * r.toReal + Real.sqrt (q.toReal * p.toReal) := by
  have hq_pos := ENNReal.toReal_pos hq hq_top
  have hreal : ε.toReal * (ε.toReal / q.toReal - r.toReal) ≤ p.toReal := by
    calc
      _ ≤ ε.toReal * (ε / q - r).toReal := by
        simpa only [toReal_div] using
          mul_le_mul_of_nonneg_left (le_toReal_sub (a := ε / q) hr) ε.toReal_nonneg
      _ ≤ _ := by simpa only [toReal_mul] using toReal_mono hp h
  have hquad : ε.toReal * (ε.toReal - q.toReal * r.toReal) ≤ q.toReal * p.toReal := by
    calc
      _ = q.toReal * (ε.toReal * (ε.toReal / q.toReal - r.toReal)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hreal hq_pos.le
  by_cases hsmall : ε.toReal ≤ q.toReal * r.toReal
  · exact hsmall.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hnonneg := mul_nonneg (mul_nonneg hq_pos.le r.toReal_nonneg)
    (sub_nonneg.mpr (le_of_not_ge hsmall))
  have hsquare : (ε.toReal - q.toReal * r.toReal) ^ 2 ≤ q.toReal * p.toReal := by
    nlinarith
  linarith [Real.le_sqrt_of_sq_le hsquare]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy--Schwarz bounds the square of the first moment by the second moment times total mass. -/
theorem sq_lintegral_le_lintegral_sq_mul {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * μ Set.univ := by
  have h := pow_le_pow_left' (lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))) 2
  simpa only [Pi.mul_apply, mul_one, one_rpow, lintegral_one, one_div, mul_pow,
    ← rpow_two, rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)] using h

/-- A quadratic lower bound survives averaging over a shared random prefix. -/
theorem sq_lintegral_sub_mul_le [IsProbabilityMeasure μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (r : ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) ^ 2 - (∫⁻ a, f a ∂μ) * r ≤
      ∫⁻ a, f a ^ 2 - f a * r ∂μ := by
  calc
    _ ≤ (∫⁻ a, f a ^ 2 ∂μ) - (∫⁻ a, f a ∂μ) * r := by
      gcongr
      simpa using sq_lintegral_le_lintegral_sq_mul hf
    _ = (∫⁻ a, f a ^ 2 ∂μ) - ∫⁻ a, f a * r ∂μ := by
      rw [lintegral_mul_const'' _ hf]
    _ ≤ _ := lintegral_sub_le' _ _ (hf.mul_const r)

/-- Averaging a bounded success probability preserves the divided quadratic forking bound. -/
theorem mul_sub_lintegral_le [IsProbabilityMeasure μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_one : ∀ a, f a ≤ 1) (q r : ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) * ((∫⁻ a, f a ∂μ) / q - r) ≤
      ∫⁻ a, f a * (f a / q - r) ∂μ := by
  have hfin : (∫⁻ a, f a ∂μ) ≠ ⊤ := ne_top_of_le_ne_top (by simp)
    (lintegral_le_const (Filter.Eventually.of_forall hf_one))
  calc
    _ = (∫⁻ a, f a ∂μ) ^ 2 / q - (∫⁻ a, f a ∂μ) * r := by
      rw [ENNReal.mul_sub (fun _ _ => hfin)]
      simp only [pow_two, div_eq_mul_inv, mul_assoc]
    _ ≤ (∫⁻ a, f a ^ 2 ∂μ) / q - (∫⁻ a, f a ∂μ) * r := by
      gcongr
      simpa using sq_lintegral_le_lintegral_sq_mul hf
    _ = (∫⁻ a, f a ^ 2 / q ∂μ) - ∫⁻ a, f a * r ∂μ := by
      simp only [div_eq_mul_inv, lintegral_mul_const'' _ (hf.pow_const 2),
        lintegral_mul_const'' _ hf]
    _ ≤ ∫⁻ a, f a ^ 2 / q - f a * r ∂μ :=
      lintegral_sub_le' _ _ (hf.mul_const r)
    _ = _ := by
      apply lintegral_congr
      intro a
      rw [ENNReal.mul_sub (fun _ _ => ne_top_of_le_ne_top (by simp) (hf_one a))]
      simp only [pow_two, div_eq_mul_inv, mul_assoc]

/-- Finite Cauchy--Schwarz for extended nonnegative reals, including infinite summands. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  let : MeasurableSpace ι := ⊤
  simpa [lintegral_finsetSum_measure, lintegral_dirac, Measure.finsetSum_apply, mul_comm] using
    (sq_lintegral_le_lintegral_sq_mul (μ := ∑ i ∈ s, Measure.dirac i)
      (f := f) Measurable.of_discrete.aemeasurable)

/-- Divided Cauchy--Schwarz, also valid for the empty sum since `0 / 0 = 0`. -/
theorem sq_sum_div_card_le_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 / (s.card : ℝ≥0∞) ≤ ∑ i ∈ s, f i ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hcard : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs.card_ne_zero
    calc
      _ ≤ (s.card * ∑ i ∈ s, f i ^ 2) / s.card := by
        gcongr
        exact sq_sum_le_card_mul_sum_sq s f
      _ = _ := by
        rw [mul_comm, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hcard (by simp), mul_one]

/-- Aggregate quadratic bounds over finitely many disjoint success classes. -/
theorem mul_sub_le_sum_sq_sub_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (r : ℝ≥0∞)
    (hsum : (∑ i ∈ s, f i) ≠ ⊤) :
    (∑ i ∈ s, f i) * ((∑ i ∈ s, f i) / (s.card : ℝ≥0∞) - r) ≤
      ∑ i ∈ s, (f i ^ 2 - f i * r) := by
  calc
    _ = (∑ i ∈ s, f i) ^ 2 / s.card - (∑ i ∈ s, f i) * r := by
      rw [ENNReal.mul_sub (fun _ _ => hsum)]
      simp only [pow_two, div_eq_mul_inv, mul_assoc]
    _ ≤ (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) * r := by
      gcongr
      exact sq_sum_div_card_le_sum_sq s f
    _ = (∑ i ∈ s, f i ^ 2) - ∑ i ∈ s, f i * r := by rw [Finset.sum_mul]
    _ ≤ _ := by
      rw [tsub_le_iff_right, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun _ _ => le_tsub_add

end ENNReal
