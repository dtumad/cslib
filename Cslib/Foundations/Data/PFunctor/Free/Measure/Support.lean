/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-! # Measure semantics are supported on structurally reachable results -/

public section

namespace PFunctor.FreeM

open MeasureTheory

universe uA uB v

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))
  {α : Type v} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- Structural partial correctness holds almost everywhere under any answer measures. -/
theorem ae_canReturn (x : P.FreeM α) : ∀ᵐ a ∂denote μ x, MonadAttach.CanReturn x a := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [ae_iff, denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro answer
    apply measure_mono_null _ ((ae_iff.mp (ih answer)))
    intro a ha hreturn
    exact ha ⟨answer, hreturn⟩

end PFunctor.FreeM
