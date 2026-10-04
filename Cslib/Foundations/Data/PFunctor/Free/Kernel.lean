/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Mathlib.Probability.Kernel.Basic

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

open MeasureTheory ProbabilityTheory

universe uA uB uS uR uT uQ

namespace PFunctor

namespace FreeM

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

end FreeM
end PFunctor
