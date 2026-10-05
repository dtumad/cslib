/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Repeat
public import Cslib.Foundations.Data.PFunctor.Resumption.Measure.Cost

/-! # Exact laws for rejection sampling -/

public section

open MeasureTheory
open scoped ENNReal

namespace PFunctor.Resumption

universe uA uB v

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  [∀ op, DiscreteMeasurableSpace (P.B op)] {α : Type v} [MeasurableSpace α]
  (μ : (op : P.A) → Measure (P.B op)) (op : P.A) (accept : P.B op → Option α)

theorem outputMeasure_repeatUntil_succ_apply (k : ℕ) (s : Set α) (hs : MeasurableSet s) :
    outputMeasure μ (k + 1) (repeatUntil op accept) s =
      μ op {b | ∃ a ∈ s, accept b = some a} +
        μ op {b | accept b = none} * outputMeasure μ k (repeatUntil op accept) s := by
  classical
  rw [outputMeasure_repeatUntil_succ,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  let success := {b | ∃ a ∈ s, accept b = some a}
  let reject := {b | accept b = none}
  let p := outputMeasure μ k (repeatUntil op accept) s
  calc
    _ = ∫⁻ b, success.indicator (fun _ => 1) b + reject.indicator (fun _ => p) b ∂μ op := by
      apply lintegral_congr
      intro b
      cases h : accept b <;> simp [success, reject, h, Set.indicator, p,
        Measure.dirac_apply' _ hs]
    _ = _ := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_indicator_const MeasurableSet.of_discrete,
        lintegral_indicator_const MeasurableSet.of_discrete, one_mul, mul_comm p]

/-- Finite observation sums the disjoint possibilities for the first accepted attempt. -/
theorem outputMeasure_repeatUntil_apply (k : ℕ) (s : Set α) (hs : MeasurableSet s) :
    outputMeasure μ k (repeatUntil op accept) s =
      (∑ j ∈ Finset.range k, (μ op {b | accept b = none}) ^ j) *
        μ op {b | ∃ a ∈ s, accept b = some a} := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [outputMeasure_repeatUntil_succ_apply μ op accept k s hs, ih,
      Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', add_mul, one_mul]
    rw [← Finset.mul_sum, mul_assoc, add_comm]

/-- The returned-output law of rejection sampling; divergence remains missing mass. -/
theorem returnedMeasure_repeatUntil_apply (s : Set α) (hs : MeasurableSet s) :
    returnedMeasure μ (repeatUntil op accept) s =
      (1 - μ op {b | accept b = none})⁻¹ * μ op {b | ∃ a ∈ s, accept b = some a} := by
  rw [returnedMeasure_apply _ _ _ hs]
  simp_rw [outputMeasure_repeatUntil_apply μ op accept _ s hs, Finset.sum_mul]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- Exact timeout probability after a fixed number of attempts. -/
theorem denote_truncate_repeatUntil_none (k : ℕ) :
    FreeM.denote μ (truncate k (repeatUntil op accept)) {none} =
      (μ op {b | accept b = none}) ^ k := by
  classical
  induction k with
  | zero =>
    rw [repeatUntil_eq_query, truncate_query_zero]
    simp
  | succ k ih =>
    conv_lhs => rw [repeatUntil_eq_query, truncate_query_succ]
    change FreeM.denote μ ((FreeM.lift (P := P) op).bind
      (fun b => truncate k ((accept b).elim (repeatUntil op accept) pure))) {none} = _
    rw [FreeM.denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.bind_apply Option.measurableSet_none Measurable.of_discrete.aemeasurable]
    calc
      _ = ∫⁻ b, {b | accept b = none}.indicator
          (fun _ => (μ op {b | accept b = none}) ^ k) b ∂μ op := by
        apply lintegral_congr
        intro b
        cases h : accept b <;> simp [h, ih, Set.indicator,
          Measure.dirac_apply' _ Option.measurableSet_none]
      _ = _ := by rw [lintegral_indicator_const MeasurableSet.of_discrete, pow_succ]

/-- Geometric rejection tails give the exact expected number of attempts. -/
theorem expectedQueries_repeatUntil :
    expectedQueries μ (repeatUntil op accept) = (1 - μ op {b | accept b = none})⁻¹ := by
  simp only [expectedQueries, denote_truncate_repeatUntil_none, ENNReal.tsum_geometric]

end PFunctor.Resumption
