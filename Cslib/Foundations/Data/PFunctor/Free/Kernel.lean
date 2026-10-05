/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach
public import Mathlib.Probability.Kernel.Basic
public import Cslib.Foundations.MeasureTheory.Bind
public import Cslib.Foundations.MeasureTheory.Option
public import Init.Control.Option
public import Cslib.Foundations.Data.PFunctor.Free.Trace

/-!
# Stateful kernel interpretation of polynomial programs

A kernel handler jointly samples an operation's answer and the successor state. Its free
extension interprets a whole polynomial program as a kernel from initial states to results and
final states. Query answers are countable with measurable singletons, while internal states
and final results may be continuous. Countability supplies joint measurability when a returned
answer selects a continuation; no discreteness assumption is made on private states. Adapted from
`VCVio.EvalDist.PFunctorKernel`, with explicit handlers and Mathlib kernel classes.
-/

public section

namespace PFunctor.FreeM

section Interpretation

open MeasureTheory ProbabilityTheory

universe uA uB uS uR uT uQ

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR} {β : Type uT}
variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
variable [MeasurableSpace α] [MeasurableSpace β]

private noncomputable def runStateMeasure (impl : (a : P.A) → Kernel S (P.B a × S)) :
    FreeM P α → S → Measure (α × S)
  | .pure x, state => Measure.dirac (x, state)
  | .liftBind a next, state =>
      (impl a state).bind fun out => runStateMeasure impl (next out.1) out.2

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

private theorem measurable_runStateMeasure (impl : (a : P.A) → Kernel S (P.B a × S))
    (program : FreeM P α) :
    Measurable (runStateMeasure impl program) := by
  induction program with
  | pure x => exact Measure.measurable_dirac.comp (measurable_const.prodMk measurable_id)
  | lift_bind a next ih =>
      exact (Measure.measurable_bind' (measurable_from_prod_countable_right ih)).comp
        (impl a).measurable

/-- Interpret a free polynomial program as its joint result-and-state kernel. -/
noncomputable def runKernel (impl : (a : P.A) → Kernel S (P.B a × S)) (program : FreeM P α) :
    Kernel S (α × S) where
  toFun := runStateMeasure impl program
  measurable' := measurable_runStateMeasure impl program

/-- Returning a value keeps the current state. -/
@[simp]
theorem runKernel_pure (impl : (a : P.A) → Kernel S (P.B a × S)) (value : α) (state : S) :
    runKernel impl (pure value) state = Measure.dirac (value, state) := by rfl

/-- A query samples its answer and successor state jointly before running the continuation. -/
theorem runKernel_liftBind (impl : (a : P.A) → Kernel S (P.B a × S)) (a : P.A)
    (next : P.B a → FreeM P α) (state : S) :
    runKernel impl (.liftBind a next) state =
      (impl a state).bind (fun out => runKernel impl (next out.1) out.2) := by rfl

/-- The continuation selected by a countable result is jointly measurable with private state. -/
theorem measurable_runKernel_continuation [Countable α] [MeasurableSingletonClass α]
    (impl : (a : P.A) → Kernel S (P.B a × S)) (next : α → FreeM P β) :
    Measurable fun out : α × S => runKernel impl (next out.1) out.2 :=
  measurable_from_prod_countable_right fun x => (runKernel impl (next x)).measurable

/-- A lossless handler gives a lossless result-and-state kernel. -/
instance (impl : (a : P.A) → Kernel S (P.B a × S))
    [∀ a, IsMarkovKernel (impl a)] (program : FreeM P α) :
    IsMarkovKernel (runKernel impl program) where
  isProbabilityMeasure state := by
    induction program generalizing state with
    | pure x => exact ⟨by simp⟩
    | lift_bind a next ih =>
      change IsProbabilityMeasure ((impl a state).bind _)
      exact isProbabilityMeasure_bind
        (measurable_runKernel_continuation impl next).aemeasurable
        (Filter.Eventually.of_forall fun out => ih out.1 out.2)

/-- Stateful interpretation respects sequential substitution. -/
theorem runKernel_bind [Countable α] [MeasurableSingletonClass α]
    (impl : (a : P.A) → Kernel S (P.B a × S)) (program : FreeM P α)
    (next : α → FreeM P β) (state : S) :
    runKernel impl (FreeM.bind program next) state =
      (runKernel impl program state).bind fun out => runKernel impl (next out.1) out.2 := by
  induction program generalizing state with
  | pure x =>
      exact (Measure.dirac_bind (measurable_runKernel_continuation impl next) (x, state)).symm
  | lift_bind a rest ih =>
      change (impl a state).bind (fun out =>
        runKernel impl ((rest out.1).bind next) out.2) =
          ((impl a state).bind fun out => runKernel impl (rest out.1) out.2).bind
            (fun out => runKernel impl (next out.1) out.2)
      rw [Measure.bind_bind (measurable_runKernel_continuation impl rest).aemeasurable
        (measurable_runKernel_continuation impl next).aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun out => ih out.1 out.2)

/-- Mapping a countable result preserves the final private state. -/
theorem runKernel_map [Countable α] [MeasurableSingletonClass α]
    (impl : (a : P.A) → Kernel S (P.B a × S)) (f : α → β)
    (program : FreeM P α) (state : S) :
    runKernel impl (program.map f) state =
      (runKernel impl program state).map (fun out => (f out.1, out.2)) := by
  rw [← FreeM.bind_pure_comp, runKernel_bind]
  simp only [Function.comp_apply, runKernel_pure]
  exact Measure.bind_dirac_eq_map _
    (((measurable_of_countable f).comp measurable_fst).prodMk measurable_snd)

/-- Semantically equal continuations on reachable results give the same joint kernel.
The intermediate type needs no measurable structure, so this also applies to machine tapes. -/
theorem runKernel_bind_congr_of_canReturn {X : Type uB}
    (impl : (a : P.A) → Kernel S (P.B a × S)) (program : FreeM P X)
    (left right : X → FreeM P β)
    (h : ∀ x, MonadAttach.CanReturn program x → ∀ state,
      runKernel impl (left x) state = runKernel impl (right x) state) (state : S) :
    runKernel impl (program.bind left) state = runKernel impl (program.bind right) state := by
  induction program generalizing state with
  | pure x => exact h x rfl state
  | lift_bind op cont ih =>
    change (impl op state).bind (fun out => runKernel impl ((cont out.1).bind left) out.2) =
      (impl op state).bind (fun out => runKernel impl ((cont out.1).bind right) out.2)
    apply Measure.bind_congr_right
    refine Filter.Eventually.of_forall fun out => ih out.1 ?_ out.2
    intro x hx
    exact h x ⟨out.1, hx⟩

/-- An isolated query has exactly its supplied answer-and-state kernel. -/
@[simp]
theorem runKernel_lift (impl : (a : P.A) → Kernel S (P.B a × S)) (a : P.A) (state : S) :
    runKernel impl (FreeM.lift a) state = impl a state := by
  change (impl a state).bind Measure.dirac = impl a state
  exact Measure.bind_dirac

variable {Q : PFunctor.{uQ, uB}} [∀ a, MeasurableSpace (Q.B a)]
  [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]

/-- Interpreting an inlined polynomial handler agrees with interpreting each local handler as
a kernel first. Both sides retain the same shared private state across all calls. -/
theorem runKernel_liftM {X : Type uB} [MeasurableSpace X]
    (impl : (a : Q.A) → Kernel S (Q.B a × S)) (handler : (a : P.A) → FreeM Q (P.B a))
    (program : FreeM P X) (state : S) :
    runKernel impl (program.liftM handler) state =
      runKernel (fun a => runKernel impl (handler a)) program state := by
  induction program generalizing state with
  | pure x => rfl
  | lift_bind a next ih =>
      change runKernel impl ((handler a).bind (fun b => (next b).liftM handler)) state =
        (runKernel impl (handler a) state).bind
          (fun out => runKernel (fun a => runKernel impl (handler a)) (next out.1) out.2)
      rw [runKernel_bind]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun out => ih out.1 out.2)

/-- Inlining a `StateT` handler and then interpreting its remaining effects preserves the joint
result-and-state kernel. The hypothesis is local to each operation and initial state. -/
theorem denote_liftM_stateT {T X : Type uB} [MeasurableSpace T]
    [MeasurableSpace X] (μ : (a : Q.A) → Measure (Q.B a))
    (handler : (a : P.A) → StateT T Q.FreeM (P.B a))
    (impl : (a : P.A) → Kernel T (P.B a × T))
    (h : ∀ a state, denote μ (handler a state) = impl a state)
    (program : P.FreeM X) (state : T) :
    denote μ ((program.liftM handler) state) = runKernel impl program state := by
  induction program generalizing state with
  | pure x => rfl
  | lift_bind a next ih =>
    change denote μ ((handler a state).bind
      (fun out => ((next out.1).liftM handler) out.2)) =
        (impl a state).bind (fun out => runKernel impl (next out.1) out.2)
    have hm : Measurable fun out : P.B a × T =>
        denote μ (((next out.1).liftM handler) out.2) := by
      simpa only [ih] using measurable_runKernel_continuation impl next
    rw [denote_bind μ _ _ hm, h]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun out => ih out.1 out.2)

end Interpretation

section Aborting

open MeasureTheory ProbabilityTheory

universe u v w

variable {P Q : PFunctor.{u, v}} {S : Type w} {α : Type v}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, MeasurableSingletonClass (Q.B op)]
  [∀ op, Countable (Q.B op)] [MeasurableSpace S] [MeasurableSpace α]

/-- A local joint kernel law for nonfailing optional handlers extends to an adaptive program.
The state may be continuous, and no normalization assumption is needed. -/
theorem runKernel_liftM_optionT
    (impl : (op : P.A) → Kernel S (P.B op × S))
    (target : (op : Q.A) → Kernel S (Q.B op × S))
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (h : ∀ op state, runKernel target (handler op).run state =
      (impl op state).map (fun out => (some out.1, out.2)))
    (program : P.FreeM α) (state : S) :
    runKernel target (program.liftM handler).run state =
      runKernel impl (some <$> program) state := by
  induction program generalizing state with
  | pure value => simp
  | lift_bind op cont ih =>
    simp only [bind_eq_bind, liftM_lift_bind, OptionT.run_bind, _root_.map_bind]
    change runKernel target ((handler op).run >>= fun answer =>
      answer.elim (pure none) (fun value => ((cont value).liftM handler).run)) state =
        runKernel impl (lift op >>= fun value => some <$> cont value) state
    simp only [← bind_eq_bind, runKernel_bind, runKernel_lift]
    rw [h,
      Measure.bind_map _ (f := fun out : P.B op × S => (some out.1, out.2))
        (by fun_prop) (measurable_runKernel_continuation target
          (fun answer : Option (P.B op) =>
            answer.elim (pure none) (fun value => ((cont value).liftM handler).run)))]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun out => ih out.1 out.2)

end Aborting

section Support

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

end Support

end PFunctor.FreeM
