/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Kernel

/-! # Reachability and the support of joint kernel semantics -/

public section

namespace PFunctor.FreeM

open MeasureTheory

variable {P : PFunctor} [∀ op, MeasurableSpace (P.B op)]
  [∀ op, DiscreteMeasurableSpace (P.B op)] [∀ op, Countable (P.B op)]
  {S α : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (impl : (op : P.A) → ProbabilityTheory.Kernel S (P.B op × S))

/-- A kernel interpretation returns structurally reachable results almost everywhere. -/
theorem runKernel_ae_canReturn (program : P.FreeM α) (state : S) :
    ∀ᵐ out ∂runKernel impl program state, MonadAttach.CanReturn program out.1 := by
  induction program generalizing state with
  | pure value => simp
  | lift_bind op cont ih =>
    rw [ae_iff, runKernel_bind, runKernel_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro out
    apply measure_mono_null _ (ae_iff.mp (ih out.1 out.2))
    intro result hresult hreturn
    exact hresult ⟨out.1, hreturn⟩

/-- If every answer has positive mass while keeping a fixed state, every reachable result
has positive mass at that state. This applies to a full-support test interpretation. -/
theorem runKernel_singleton_ne_zero_of_canReturn (state : S)
    (himpl : ∀ op answer, impl op state {(answer, state)} ≠ 0)
    (program : P.FreeM α) (value : α) (hvalue : MonadAttach.CanReturn program value) :
    runKernel impl program state {(value, state)} ≠ 0 := by
  induction program with
  | pure result =>
    have heq : value = result := hvalue
    simp [heq]
  | lift_bind op cont ih =>
    obtain ⟨answer, hanswer⟩ := hvalue
    rw [runKernel_bind, runKernel_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    intro hzero
    have hae := (lintegral_eq_zero_iff Measurable.of_discrete).mp hzero
    exact ih answer hanswer ((ae_iff_of_countable.mp hae) (answer, state) (himpl op answer))

end PFunctor.FreeM
