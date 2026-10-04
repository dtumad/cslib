/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Agreement of measure and PMF interpretations

The direct measure semantics agrees with ordinary monadic interpretation into `PMF` on
countable answer spaces. Result spaces need not be countable or discrete.
-/

public section

open MeasureTheory

namespace PMF

/-- PMF bind and Giry bind agree on a countable, discrete source. -/
theorem toMeasure_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (p : PMF α) (f : α → PMF β) :
    (p.bind f).toMeasure = p.toMeasure.bind fun a => (f a).toMeasure := by
  ext s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

end PMF

namespace PFunctor.FreeM

universe uA uB

/-- Evaluating with PMFs gives exactly the direct measure denotation. -/
theorem denote_eq_toMeasure_liftM {P : PFunctor.{uA, uB}}
    [∀ op, MeasurableSpace (P.B op)] [∀ op, Countable (P.B op)]
    [∀ op, MeasurableSingletonClass (P.B op)]
    (p : (op : P.A) → PMF (P.B op)) {α : Type uB} [MeasurableSpace α] (x : P.FreeM α) :
    denote (fun op => (p op).toMeasure) x = (x.liftM p).toMeasure := by
  induction x with
  | pure a => exact (PMF.toMeasure_pure a).symm
  | lift_bind op cont ih =>
    rw [denote_lift_bind _ _ _ Measurable.of_discrete.aemeasurable]
    change _ = ((p op).bind fun b => (cont b).liftM p).toMeasure
    rw [PMF.toMeasure_bind]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

end PFunctor.FreeM
