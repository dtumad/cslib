/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.Comap

/-! # The expectation lost by aborting an experiment -/

public section

open scoped ENNReal

namespace MeasureTheory

/-- Pulling an optional measure back along `some` gives zero weight to failure. -/
theorem lintegral_comap_some {α : Type*} [MeasurableSpace α]
    (μ : Measure (Option α)) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ.comap some = ∫⁻ out, out.elim 0 f ∂μ := by
  calc
    _ = ∫⁻ out : Option α, out.elim 0 f ∂(μ.comap some).map some :=
      (Option.measurableEmbedding_some.lintegral_map _).symm
    _ = _ := by
      rw [Option.measurableEmbedding_some.map_comap,
        ← lintegral_indicator Option.measurableEmbedding_some.measurableSet_range]
      apply lintegral_congr
      intro out
      cases out <;> simp

/-- For probability measures on optional countable outcomes, the successful law determines
the failure mass as well. This restores the whole law after an aborting-kernel comparison. -/
theorem Measure.ext_of_comap_some {α : Type*} [MeasurableSpace α] [Countable α]
    {μ ν : Measure (Option α)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ.comap some = ν.comap some) : μ = ν := by
  apply Measure.ext_of_singleton
  intro out
  cases out with
  | none =>
    have hmass := congrArg (fun measure => measure Set.univ) h
    simp only [Option.measurableEmbedding_some.comap_apply, Set.image_univ] at hmass
    have hnone : ({none} : Set (Option α)) = (Set.range some)ᶜ := by
      ext value
      cases value <;> simp
    rw [hnone, measure_compl Option.measurableEmbedding_some.measurableSet_range
      (measure_ne_top μ _), measure_compl Option.measurableEmbedding_some.measurableSet_range
      (measure_ne_top ν _), measure_univ, measure_univ, hmass]
  | some value =>
    simpa only [Option.measurableEmbedding_some.comap_apply, Set.image_singleton] using
      congrArg (fun measure => measure {value}) h

/-- Removing mass from a finite measure loses at most that mass for a postcondition in `[0, 1]`.
The removed event need not be identified explicitly. -/
theorem lintegral_le_lintegral_add_of_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] (h : ν ≤ μ)
    (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    ∫⁻ a, f a ∂μ ≤ (∫⁻ a, f a ∂ν) + (μ Set.univ - ν Set.univ) := by
  let := isFiniteMeasure_of_le μ h
  calc
    _ = (∫⁻ a, f a ∂(μ - ν)) + ∫⁻ a, f a ∂ν := by
      rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le h]
    _ ≤ (μ - ν) Set.univ + ∫⁻ a, f a ∂ν := by
      refine add_le_add ?_ le_rfl
      simpa using (lintegral_mono hf : (∫⁻ a, f a ∂(μ - ν)) ≤ ∫⁻ _, 1 ∂(μ - ν))
    _ = _ := by rw [Measure.sub_apply MeasurableSet.univ h, add_comm]

/-- A lossless optional approximation dominated by the ideal measure on successful outcomes
loses at most its failure probability. No conditioning or renormalization is used. -/
theorem lintegral_le_lintegral_option_add {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ν : Measure (Option α)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ν.comap some ≤ μ) (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    ∫⁻ a, f a ∂μ ≤ (∫⁻ out, out.elim 0 f ∂ν) + ν {none} := by
  have hnone : ({none} : Set (Option α)) = (Set.range some)ᶜ := by
    ext out
    cases out <;> simp
  have hmass : μ Set.univ - ν.comap some Set.univ = ν {none} := by
    rw [measure_univ, Option.measurableEmbedding_some.comap_apply, Set.image_univ, hnone,
      measure_compl Option.measurableEmbedding_some.measurableSet_range (measure_ne_top _ _),
      measure_univ]
  simpa only [lintegral_comap_some, hmass] using
    lintegral_le_lintegral_add_of_le μ (ν.comap some) h f hf

/-- Discarding an event loses at most its measure for any postcondition bounded by one. -/
theorem lintegral_le_lintegral_abort_add {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (μ : Measure α) (keep : α → Bool)
    (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    ∫⁻ a, f a ∂μ ≤
      (∫⁻ out : Option α, out.elim 0 f ∂μ.map (fun a => if keep a then some a else none)) +
        μ {a | keep a = false} := by
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  calc
    _ ≤ ∫⁻ a, (if keep a then some a else none).elim 0 f +
        {a | keep a = false}.indicator (fun _ => 1) a ∂μ := by
      apply lintegral_mono
      intro a
      cases h : keep a with
      | false => simpa [h] using hf a
      | true => simp [h]
    _ = _ := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

end MeasureTheory
