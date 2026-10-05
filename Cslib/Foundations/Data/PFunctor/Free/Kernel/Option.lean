/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Kernel
public import Cslib.Foundations.MeasureTheory.Bind
public import Cslib.Foundations.MeasureTheory.Option
public import Init.Control.Option

/-! # Stateful interpretation of nonfailing optional handlers -/

public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
