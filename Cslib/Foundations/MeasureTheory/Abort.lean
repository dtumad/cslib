/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # The expectation lost by aborting an experiment -/

public section

open scoped ENNReal

namespace MeasureTheory

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
