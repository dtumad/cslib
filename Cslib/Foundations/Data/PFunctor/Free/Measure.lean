/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measure semantics for polynomial free programs

`denote μ` assigns the answer measure `μ op` to each operation and composes using Mathlib's
Giry bind. A nonmeasurable continuation denotes zero; this is an invalid measurable program,
not nontermination. Discrete answer spaces make the internal measurability conditions automatic,
while the result space remains arbitrary.

The measures are explicit parameters. Losslessness uses Mathlib's `IsProbabilityMeasure`;
no separate notion of a probabilistic effect signature is needed. Adapted from
`VCVio.EvalDist.PFunctorMeasure.Core`.
-/

@[expose] public section

open MeasureTheory

universe uA uB v w uQ

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  {α : Type v} {β : Type w}

open scoped Classical in
/-- Interpret a free program by answer measures, using zero for nonmeasurable continuations. -/
noncomputable def denote (μ : (op : P.A) → Measure (P.B op))
    [MeasurableSpace α] : P.FreeM α → Measure α
  | .pure a => Measure.dirac a
  | .liftBind op cont =>
    if AEMeasurable (fun b => denote μ (cont b)) (μ op) then
      (μ op).bind fun b => denote μ (cont b)
    else 0

variable (μ : (op : P.A) → Measure (P.B op))

@[simp]
theorem denote_pure [MeasurableSpace α] (a : α) :
    denote μ (pure a : P.FreeM α) = Measure.dirac a := rfl

theorem denote_lift_bind [MeasurableSpace α] (op : P.A) (cont : P.B op → P.FreeM α)
    (hcont : AEMeasurable (fun b => denote μ (cont b)) (μ op)) :
    denote μ ((lift op).bind cont) = (μ op).bind fun b => denote μ (cont b) := by
  classical
  change (if AEMeasurable (fun b => denote μ (cont b)) (μ op) then _ else 0) = _
  exact ite_eq_left hcont

theorem denote_lift_bind_of_not_aemeasurable [MeasurableSpace α]
    (op : P.A) (cont : P.B op → P.FreeM α)
    (hcont : ¬ AEMeasurable (fun b => denote μ (cont b)) (μ op)) :
    denote μ ((lift op).bind cont) = 0 := by
  classical
  change (if AEMeasurable (fun b => denote μ (cont b)) (μ op) then _ else 0) = _
  exact ite_eq_right hcont

@[simp]
theorem denote_lift (op : P.A) : denote μ (lift op) = μ op := by
  rw [← bind_pure (lift op), denote_lift_bind μ op pure Measure.measurable_dirac.aemeasurable]
  exact Measure.bind_dirac

/-- The measurable composition of lossless operation and continuation is lossless. -/
theorem isProbabilityMeasure_denote_lift_bind [MeasurableSpace α] (op : P.A)
    [IsProbabilityMeasure (μ op)] (cont : P.B op → P.FreeM α)
    (hcont : AEMeasurable (fun b => denote μ (cont b)) (μ op))
    (hprob : ∀ᵐ b ∂μ op, IsProbabilityMeasure (denote μ (cont b))) :
    IsProbabilityMeasure (denote μ ((lift op).bind cont)) := by
  rw [denote_lift_bind μ op cont hcont]
  exact isProbabilityMeasure_bind hcont hprob

section Discrete

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

/-- Discrete operations are measurable even when the result space is not discrete. -/
instance [∀ op, IsProbabilityMeasure (μ op)] [MeasurableSpace α] (x : P.FreeM α) :
    IsProbabilityMeasure (denote μ x) := by
  induction x with
  | pure a => exact ⟨by simp⟩
  | lift_bind op cont ih =>
    exact isProbabilityMeasure_denote_lift_bind μ op cont
      Measurable.of_discrete.aemeasurable (Filter.Eventually.of_forall ih)

/-- The Giry composition law retains measurability at the result-to-continuation boundary. -/
theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (x : P.FreeM α) (f : α → P.FreeM β)
    (hf : Measurable fun a => denote μ (f a)) :
    denote μ (x.bind f) = (denote μ x).bind fun a => denote μ (f a) := by
  induction x with
  | pure a => simpa using (Measure.dirac_bind hf a).symm
  | lift_bind op cont ih =>
    rw [liftBind_bind, denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable]
    rw [Measure.bind_bind Measurable.of_discrete.aemeasurable hf.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

theorem denote_bind_of_discrete {α β : Type v}
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (x : P.FreeM α) (f : α → P.FreeM β) :
    denote μ (x >>= f) = (denote μ x).bind fun a => denote μ (f a) :=
  denote_bind μ x f Measurable.of_discrete

theorem denote_map [MeasurableSpace α] [MeasurableSpace β]
    (x : P.FreeM α) (f : α → β) (hf : Measurable f) :
    denote μ (map f x) = (denote μ x).map f := by
  rw [← bind_pure_comp f x, denote_bind μ x (pure ∘ f)]
  · exact Measure.bind_dirac_eq_map _ hf
  · exact Measure.measurable_dirac.comp hf

/-- Independent executions denote the product measure. -/
theorem denote_bind_bind_prod_mk [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (x : P.FreeM α) (y : P.FreeM β) :
    denote μ (x.bind fun a => y.bind fun b => pure (a, b)) =
      (denote μ x).prod (denote μ y) := by
  rw [denote_bind μ x _ Measurable.of_discrete, Measure.prod]
  apply Measure.bind_congr_right
  filter_upwards [] with a
  simpa only [← bind_pure_comp, Function.comp_def] using
    denote_map μ y (Prod.mk a) (by fun_prop)

/-- Inlining an operation handler preserves its measure interpretation. -/
theorem denote_liftM {Q : PFunctor.{uQ, uB}} [∀ op, MeasurableSpace (Q.B op)]
    [∀ op, DiscreteMeasurableSpace (Q.B op)] {α : Type uB} [MeasurableSpace α]
    (handler : (op : Q.A) → P.FreeM (Q.B op)) (x : Q.FreeM α) :
    denote μ (x.liftM handler) = denote (fun op => denote μ (handler op)) x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change denote μ ((handler op).bind fun b => (cont b).liftM handler) = _
    rw [denote_bind μ (handler op) _ Measurable.of_discrete,
      denote_lift_bind _ _ _ Measurable.of_discrete.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

end Discrete

/-- Probability measures at the operations bound the mass of any program by one. -/
theorem denote_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)]
    [MeasurableSpace α] (x : P.FreeM α) : denote μ x Set.univ ≤ 1 := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    by_cases hcont : AEMeasurable (fun b => denote μ (cont b)) (μ op)
    · rw [denote_lift_bind μ op cont hcont, Measure.bind_apply MeasurableSet.univ hcont]
      calc
        _ ≤ ∫⁻ _b, 1 ∂μ op := lintegral_mono ih
        _ = 1 := by simp
    · simp only [denote_lift_bind_of_not_aemeasurable μ op cont hcont,
        Measure.coe_zero, Pi.zero_apply, zero_le]

end PFunctor.FreeM
