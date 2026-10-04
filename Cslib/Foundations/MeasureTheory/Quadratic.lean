/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Quadratic bounds for nonnegative integrals

Adapted from VCVio's `ToMathlib.MeasureTheory.Integral.Quadratic`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ENNReal

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

end ENNReal
