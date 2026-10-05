/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Resumption.Repeat
import Cslib.Foundations.Data.PFunctor.Resumption.Measure.Cost
import Cslib.Foundations.Data.PFunctor.Free.Measure.WP
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecificLimits.Basic
import Std.WP.Triple
import Std.Tactic.Do

/-! An exact, nondyadic sampler with an infinite rejected branch. Adapted from VCVio's
`Examples.ResumptionRejection`. This checks the returned-output limit, including zero fuel. -/

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace PFunctorProbability

abbrev four : PFunctor := ⟨Unit, fun _ => Fin 4⟩

def accept (x : Fin 4) : Option (Fin 3) :=
  if h : x.val < 3 then some ⟨x.val, h⟩ else none

def sample : Resumption four (Fin 3) := Resumption.repeatUntil () accept

noncomputable def answers (_ : four.A) : Measure (Fin 4) :=
  uniformOn Set.univ

instance (op : four.A) : IsProbabilityMeasure (answers op) := by
  unfold answers
  infer_instance

noncomputable abbrev interpretation : OutputMeasure four := .ofMeasure answers

theorem output_succ (k : ℕ) (s : Set (Fin 3)) :
    Resumption.outputMeasure answers (k + 1) sample s =
      (Measure.dirac 0 s + Measure.dirac 1 s + Measure.dirac 2 s +
        Resumption.outputMeasure answers k sample s) * (4 : ℝ≥0∞)⁻¹ := by
  rw [sample, Resumption.outputMeasure_repeatUntil_succ (P := four),
    Measure.bind_apply (Set.to_countable s).measurableSet Measurable.of_discrete.aemeasurable,
    lintegral_fintype]
  simp [answers, uniformOn_univ, Fin.sum_univ_succ, accept, ← add_mul, add_assoc]

theorem output_singleton (k : ℕ) (x : Fin 3) :
    Resumption.outputMeasure answers k sample {x} =
      ∑ j ∈ Finset.range k, (4 : ℝ≥0∞)⁻¹ ^ (j + 1) := by
  induction k with
  | zero => simp [sample]
  | succ k ih =>
    have h : Resumption.outputMeasure answers (k + 1) sample {x} =
        (1 + Resumption.outputMeasure answers k sample {x}) * (4 : ℝ≥0∞)⁻¹ := by
      rw [output_succ]
      fin_cases x <;> simp
    rw [h, ih, add_mul, one_mul, Finset.sum_range_succ']
    simp only [pow_succ, Finset.sum_mul, pow_zero, one_mul]
    exact add_comm _ _

theorem returned_uniform : sample.toMeasure interpretation =
    uniformOn Set.univ := by
  rw [Resumption.toMeasure_ofMeasure]
  apply Measure.ext_of_singleton
  intro x
  rw [Resumption.returnedMeasure_apply (P := four) _ _ _ (measurableSet_singleton _)]
  simp_rw [output_singleton]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric_add_one,
    uniformOn_univ, Measure.count_singleton]
  norm_num
  change ((4 : NNReal) : ℝ≥0∞)⁻¹ *
    ((1 : NNReal) - ((4 : NNReal) : ℝ≥0∞)⁻¹)⁻¹ = ((3 : NNReal) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv, ← ENNReal.coe_sub, ← ENNReal.coe_inv,
    ← ENNReal.coe_mul, ← ENNReal.coe_inv]
  · apply congrArg (fun r : NNReal => (r : ℝ≥0∞))
    apply NNReal.eq
    norm_num [NNReal.sub_def]
  all_goals norm_num [NNReal.sub_def]

example : IsProbabilityMeasure (sample.toMeasure interpretation) := by
  rw [returned_uniform]
  infer_instance

example : (Resumption.repeatUntil (P := four) () (fun _ => (none : Option (Fin 3)))).toMeasure
    interpretation = 0 := by simp [Resumption.toMeasure_ofMeasure]

theorem timeout_succ (k : ℕ) :
    FreeM.denote answers (Resumption.truncate (k + 1) sample) {none} =
      FreeM.denote answers (Resumption.truncate k sample) {none} * (4 : ℝ≥0∞)⁻¹ := by
  classical
  conv_lhs => rw [sample, Resumption.repeatUntil_eq_query, Resumption.truncate_query_succ]
  change FreeM.denote answers ((FreeM.lift (P := four) ()).bind
    (fun b => Resumption.truncate k ((accept b).elim sample Resumption.pure))) {none} = _
  rw [FreeM.denote_lift_bind (P := four) answers () _ Measurable.of_discrete.aemeasurable,
    Measure.bind_apply Option.measurableSet_none Measurable.of_discrete.aemeasurable,
    lintegral_fintype]
  simp [answers, uniformOn_univ, Fin.sum_univ_succ, accept,
    Measure.dirac_apply' _ Option.measurableSet_none]

theorem timeout (k : ℕ) :
    FreeM.denote answers (Resumption.truncate k sample) {none} = (4 : ℝ≥0∞)⁻¹ ^ k := by
  induction k with
  | zero =>
    rw [sample, Resumption.repeatUntil_eq_query, Resumption.truncate_query_zero]
    simp
  | succ k ih => rw [timeout_succ, ih, pow_succ]

example : Resumption.expectedQueries answers sample = (1 - (4 : ℝ≥0∞)⁻¹)⁻¹ := by
  simp only [Resumption.expectedQueries, timeout, ENNReal.tsum_geometric]

section Quantitative

open Std.WP

set_option experimental.vcgen true

noncomputable local instance : Lean.Order.CompleteLattice ℝ≥0∞ := .ofMathlib _
noncomputable local instance : WPMonad four.FreeM ℝ≥0∞ EStack⟨⟩ := FreeM.expectationWP answers

def accepted : four.FreeM Bool := do
  let x ← FreeM.lift ()
  pure (decide (x.val < 3))

example : ⦃(3 / 4 : ℝ≥0∞)⦄ accepted ⦃fun b => if b then 1 else 0⦄ := by
  vcgen [accepted]
  change (3 / 4 : ℝ≥0∞) ≤ ∫⁻ x : Fin 4, (if decide (x.val < 3) then 1 else 0) ∂answers ()
  norm_num [answers, lintegral_fintype,
    uniformOn_univ, Measure.count_singleton, Fin.sum_univ_succ]
  simp [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num, div_eq_mul_inv, add_mul, add_assoc]

end Quantitative

section Bundled

abbrev coin : PFunctor := .mk Unit (fun _ => Bool)

noncomputable abbrev fair : OutputMeasure coin :=
  .ofMeasure (fun _ => uniformOn (Set.univ : Set Bool))

noncomputable abbrev biased : OutputMeasure coin :=
  .ofMeasure (fun _ => bernoulliMeasure true false ⟨1 / 4, by norm_num⟩)

-- The same program and response type can have different explicit probability laws.
example : (FreeM.lift (P := coin) ()).toMeasure fair {true} = 1 / 2 := by
  rw [FreeM.toMeasure_lift]
  change uniformOn (Set.univ : Set Bool) {true} = _
  rw [uniformOn_univ, Measure.count_singleton]
  norm_num

theorem biased_true : (FreeM.lift (P := coin) ()).toMeasure biased {true} = 1 / 4 := by
  rw [FreeM.toMeasure_lift]
  norm_num [bernoulliMeasure_apply, unitInterval.toNNReal]
  change ((1 / 4 : NNReal) : ℝ≥0∞) = _
  norm_num

example (program : coin.FreeM Bool) : IsProbabilityMeasure (program.toMeasure biased) :=
  inferInstance

-- Normalized primitives do not normalize a diverging resumption.
example : (Resumption.repeatUntil (P := coin) () (fun _ => (none : Option Bool))).toMeasure
    fair = 0 := by simp [Resumption.toMeasure_ofMeasure]

-- Arbitrary measures remain available, including missing mass at an operation.
example : (FreeM.lift (P := coin) ()).toMeasure
    (.ofMeasure (fun _ => (1 / 2 : ℝ≥0∞) • Measure.dirac true)) Set.univ = 1 / 2 := by
  rw [FreeM.toMeasure_lift]
  simp

noncomputable abbrev combined :
    @OutputMeasure (four + coin) (OutputMeasure.sumMeasurableSpace four coin) :=
  interpretation.sum biased

-- The sum reuses Bool's existing instance definitionally.
example : OutputMeasure.sumMeasurableSpace four coin (.inr ()) =
    inferInstanceAs (MeasurableSpace Bool) := rfl

-- Composition retains each component's law and response measurable space.
example : (FreeM.lift (P := four + coin) (.inl ())).toMeasure (α := Fin 4) combined =
    uniformOn (Set.univ : Set (Fin 4)) := by
  rw [FreeM.toMeasure_lift]
  rfl

example : (FreeM.lift (P := four + coin) (.inr ())).toMeasure (α := Bool) combined {true} =
    1 / 4 := by
  have h := biased_true
  rw [FreeM.toMeasure_lift] at h ⊢
  exact h

example (program : (four + coin).FreeM Bool) :
    IsProbabilityMeasure (program.toMeasure combined) := inferInstance

example (program : (four + coin).FreeM Bool) :
    program.toResumption.toMeasure combined = program.toMeasure combined := by simp

end Bundled

end PFunctorProbability
