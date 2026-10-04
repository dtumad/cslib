/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Measure.Truncate
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Expected number of operations

The tail-sum formula counts operations in a resumption, including paths that never return.
It charges one per operation; it does not charge local computation or an operation handler's
implementation. A machine runtime bound must supply those costs separately.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PFunctor.Resumption

universe uA uB v

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  {α : Type v} [MeasurableSpace α]
  (μ : (op : P.A) → Measure (P.B op))

/-- Expected operation count, as the sum of probabilities of reaching each next operation. -/
noncomputable def expectedQueries (x : Resumption P α) : ℝ≥0∞ :=
  ∑' k, FreeM.denote μ (truncate k x) {none}

@[simp]
theorem expectedQueries_pure (a : α) : expectedQueries μ (pure a) = 0 := by
  classical
  simp [expectedQueries, Measure.dirac_apply' _ Option.measurableSet_none]

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

/-- Performing an operation costs one plus the expected cost of its continuation. -/
theorem expectedQueries_query (op : P.A) (cont : P.B op → Resumption P α) :
    expectedQueries μ (query op cont) = 1 + ∫⁻ b, expectedQueries μ (cont b) ∂μ op := by
  have hsucc (k : ℕ) : FreeM.denote μ (truncate (k + 1) (query op cont)) {none} =
      ∫⁻ b, FreeM.denote μ (truncate k (cont b)) {none} ∂μ op := by
    change FreeM.denote μ ((FreeM.lift op).bind (fun b => truncate k (cont b))) {none} = _
    rw [FreeM.denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.bind_apply Option.measurableSet_none Measurable.of_discrete.aemeasurable]
  rw [expectedQueries, tsum_eq_zero_add' ENNReal.summable]
  simp only [truncate_query_zero, FreeM.denote,
    Measure.dirac_apply' _ Option.measurableSet_none, Set.indicator_of_mem (Set.mem_singleton _),
    Pi.one_apply, hsucc]
  rw [← lintegral_tsum (fun _ => Measurable.of_discrete.aemeasurable)]
  rfl

/-- For lossless operations, the tail at each depth is the mass not yet returned. -/
theorem expectedQueries_eq_tsum [∀ op, IsProbabilityMeasure (μ op)] (x : Resumption P α) :
    expectedQueries μ x = ∑' k, (1 - outputMeasure μ k x Set.univ) := by
  simp only [expectedQueries, denote_truncate_none]

omit [∀ op, DiscreteMeasurableSpace (P.B op)] in
/-- A geometric timeout bound gives the usual geometric bound on expected work. -/
theorem expectedQueries_le_of_geometric (x : Resumption P α) (r : ℝ≥0∞)
    (h : ∀ k, FreeM.denote μ (truncate k x) {none} ≤ r ^ k) :
    expectedQueries μ x ≤ (1 - r)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  exact ENNReal.tsum_le_tsum h

/-- Finite expected operation count implies almost-sure termination for lossless operations. -/
theorem isProbabilityMeasure_returnedMeasure_of_expectedQueries_ne_top
    [∀ op, IsProbabilityMeasure (μ op)] (x : Resumption P α)
    (hcost : expectedQueries μ x ≠ ⊤) : IsProbabilityMeasure (returnedMeasure μ x) := by
  refine ⟨le_antisymm (returnedMeasure_apply_univ_le_one μ x) ?_⟩
  by_contra hmass
  have hdelta : 1 - returnedMeasure μ x Set.univ ≠ 0 :=
    fun h => hmass (tsub_eq_zero_iff_le.mp h)
  have hlower : (∑' _ : ℕ, (1 - returnedMeasure μ x Set.univ)) ≤ expectedQueries μ x := by
    rw [expectedQueries_eq_tsum]
    exact ENNReal.tsum_le_tsum fun k =>
      tsub_le_tsub_left ((le_iSup (outputMeasure μ · x) k) Set.univ) 1
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hdelta] at hlower
  exact hcost (top_le_iff.mp hlower)

end PFunctor.Resumption
