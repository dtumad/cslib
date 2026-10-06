/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-!
# Output measures are carried by possible outputs

Whatever measures answer the operations, the output measure of a free program is carried by the
values the program can return (`ae_canReturn`), so facts about every possible output hold almost
everywhere.
-/

@[expose] public section

open MeasureTheory

universe uA uB v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  [∀ op, DiscreteMeasurableSpace (P.B op)] (μ : (op : P.A) → Measure (P.B op))
  {α : Type v} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The output measure of a program is carried by the values it can return. -/
theorem ae_canReturn (x : P.FreeM α) : ∀ᵐ a ∂x.toMeasure μ, MonadAttach.CanReturn x a := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [ae_iff, toMeasure_lift_bind,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro answer
    apply measure_mono_null _ (ae_iff.mp (ih answer))
    intro a ha hreturn
    exact ha ((canReturn_lift_bind op cont a).mpr ⟨answer, hreturn⟩)

end PFunctor.FreeM
