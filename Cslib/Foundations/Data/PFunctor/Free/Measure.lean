/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Data.PFunctor.Measure
public import Mathlib.MeasureTheory.Measure.Prod
public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-!
# Measure semantics for polynomial free programs

`denote μ` assigns the answer measure `μ op` to each operation and composes using Mathlib's
Giry bind. A nonmeasurable continuation denotes zero; this is an invalid measurable program,
not nontermination. Discrete answer spaces make the internal measurability conditions automatic,
while the result space remains arbitrary.

`x.toMeasure μ` uses an explicit `PFunctor.OutputMeasure` bundle on the existing response
measurable spaces. It is definitionally the same interpretation as
`denote`, which accepts unbundled measures on existing spaces. Losslessness uses Mathlib's
`IsProbabilityMeasure`. Adapted from `VCVio.EvalDist.PFunctorMeasure.Core`.
-/

@[expose] public section

namespace PFunctor.FreeM

section Interpretation

open MeasureTheory

universe uA uB v w uQ

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

end Interpretation

section Support

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

end Support

section Bundled

open MeasureTheory

universe uA uB v w uQ

variable {P : PFunctor.{uA, uB}} {mP : ∀ op, MeasurableSpace (P.B op)}
  {α : Type v} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]

/-- Interpret a finite program using explicitly chosen response measures. -/
noncomputable def toMeasure (x : P.FreeM α) (μ : OutputMeasure P) : Measure α :=
  denote μ x

theorem toMeasure_ofMeasure (x : P.FreeM α) (μ : (op : P.A) → Measure (P.B op)) :
    x.toMeasure (.ofMeasure μ) = denote μ x := rfl

variable (μ : OutputMeasure P)

@[simp]
theorem toMeasure_pure (a : α) : (pure a : P.FreeM α).toMeasure μ = Measure.dirac a := rfl

@[simp]
theorem toMeasure_lift (op : P.A) : (lift op).toMeasure μ = μ op := denote_lift μ op

/-- Probability responses bound the mass even without discreteness. -/
theorem toMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)] (x : P.FreeM α) :
    x.toMeasure μ Set.univ ≤ 1 := denote_apply_univ_le_one μ x

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

theorem toMeasure_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    ((lift op).bind cont).toMeasure μ = (μ op).bind fun b => (cont b).toMeasure μ :=
  denote_lift_bind μ op cont Measurable.of_discrete.aemeasurable

instance [∀ op, IsProbabilityMeasure (μ op)] (x : P.FreeM α) :
    IsProbabilityMeasure (x.toMeasure μ) := inferInstanceAs (IsProbabilityMeasure (denote μ x))

theorem toMeasure_bind (x : P.FreeM α) (f : α → P.FreeM β)
    (hf : Measurable fun a => (f a).toMeasure μ) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  denote_bind μ x f hf

theorem toMeasure_bind_of_discrete [DiscreteMeasurableSpace α]
    (x : P.FreeM α) (f : α → P.FreeM β) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  toMeasure_bind μ x f Measurable.of_discrete

theorem toMeasure_map (x : P.FreeM α) (f : α → β) (hf : Measurable f) :
    (map f x).toMeasure μ = (x.toMeasure μ).map f := denote_map μ x f hf

/-- Inlining handlers that implement a chosen response law preserves that interpretation. -/
theorem toMeasure_liftM {Q : PFunctor.{uQ, uB}} {mQ : ∀ op, MeasurableSpace (Q.B op)}
    [∀ op, DiscreteMeasurableSpace (Q.B op)] (ν : OutputMeasure Q)
    {α : Type uB} [MeasurableSpace α] (handler : (op : Q.A) → P.FreeM (Q.B op))
    (hhandler : ∀ op, (handler op).toMeasure μ = ν op) (x : Q.FreeM α) :
    (x.liftM handler).toMeasure μ = x.toMeasure ν := by
  change denote μ (x.liftM handler) = denote ν x
  rw [denote_liftM]
  congr 1
  funext op
  exact hhandler op

end Bundled

end PFunctor.FreeM
