/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Kernel
public import Cslib.Foundations.Data.PFunctor.Free.Trace

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

/-- A reachable trace has positive mass under any interpretation that gives its answers
positive mass and updates the observed state accordingly. -/
theorem runKernel_singleton_ne_zero_of_trace
    (update : (op : P.A) → P.B op → S → S)
    (himpl : ∀ op answer state, impl op state {(answer, update op answer state)} ≠ 0)
    (program : P.FreeM α) {value : α} {events : List (Sigma P.B)}
    (h : MonadAttach.CanReturn (trace program) (value, events)) (state : S) :
    runKernel impl program state
      {(value, events.foldl (fun st event => update event.1 event.2 st) state)} ≠ 0 := by
  induction program generalizing value events state with
  | pure result =>
    have heq : (value, events) = (result, []) := h
    cases heq
    simp
  | lift_bind op cont ih =>
    obtain ⟨answer, after, hafter, rfl⟩ := (canReturn_trace_lift_bind op cont value events).mp h
    rw [runKernel_bind, runKernel_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    intro hzero
    have hae := (lintegral_eq_zero_iff Measurable.of_discrete).mp hzero
    exact ih answer hafter (update op answer state)
      ((ae_iff_of_countable.mp hae) (answer, update op answer state) (himpl op answer state))

/-- When answers determine each observed state update, the joint kernel is supported on
complete structural traces with exactly that final state. -/
theorem runKernel_ae_exists_trace (update : (op : P.A) → P.B op → S → S)
    (himpl : ∀ op state, ∀ᵐ out ∂impl op state, out.2 = update op out.1 state)
    (program : P.FreeM α) (state : S) :
    ∀ᵐ out ∂runKernel impl program state, ∃ events,
      MonadAttach.CanReturn (trace program) (out.1, events) ∧
        events.foldl (fun st event => update event.1 event.2 st) state = out.2 := by
  induction program generalizing state with
  | pure value =>
    simp only [runKernel_pure, ae_dirac_eq]
    exact ⟨[], by simp, rfl⟩
  | lift_bind op cont ih =>
    rw [ae_iff, runKernel_bind, runKernel_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [himpl op state] with out hout
    apply measure_mono_null _ (ae_iff.mp (ih out.1 out.2))
    rintro result hresult ⟨events, htrace, hstate⟩
    apply hresult
    exact ⟨⟨op, out.1⟩ :: events,
      (canReturn_trace_lift_bind op cont _ _).mpr ⟨out.1, events, htrace, rfl⟩,
      by simpa only [List.foldl_cons, ← hout] using hstate⟩

end PFunctor.FreeM
