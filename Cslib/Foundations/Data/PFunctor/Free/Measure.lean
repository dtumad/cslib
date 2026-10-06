/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.MeasureSemantics
public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Output measures of polynomial programs

Given a measure `μ a` on the responses of each operation `a`, a program `x : P.FreeM α` has the
output measure `x.toMeasure μ`: each operation is answered according to `μ`, and the returned value
is observed. It is the fold of `x` into Mathlib's Giry bind, so it follows `Measure.bind`'s
convention for continuations that are not measurable. When the response spaces are discrete, every
continuation is measurable, `toMeasure` sends `bind` to the Giry bind (`toMeasure_bind`), so it is a
measure semantics of `P.FreeM` (`isMeasureSemantics_toMeasure`), and it sends programs to
probability measures whenever each `μ a` is one.
-/

@[expose] public section

open MeasureTheory

universe uA uA' uB u v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)] {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]

/-- The output measure of `x` when each operation `a` is answered according to `μ a`. -/
noncomputable def toMeasure (x : P.FreeM α) (μ : (a : P.A) → Measure (P.B a)) : Measure α :=
  x.foldFreeM .dirac fun a k => (μ a).bind k

variable (μ : (a : P.A) → Measure (P.B a))

@[simp]
theorem toMeasure_pure (a : α) : (pure a : P.FreeM α).toMeasure μ = .dirac a := rfl

@[simp]
theorem toMeasure_lift_bind (a : P.A) (k : P.B a → P.FreeM α) :
    ((lift a).bind (α := no_index (P.B a)) k).toMeasure μ =
      (μ a).bind fun b => (k b).toMeasure μ := rfl

@[simp]
theorem toMeasure_lift_bind' {α : Type uB} [MeasurableSpace α] (a : P.A) (k : P.B a → P.FreeM α) :
    (Bind.bind (α := no_index (P.B a)) (lift a) k).toMeasure μ =
      (μ a).bind fun b => (k b).toMeasure μ := rfl

@[simp]
theorem toMeasure_lift (a : P.A) : toMeasure (α := no_index (P.B a)) (lift a) μ = μ a :=
  Measure.bind_dirac

theorem isPureMeasureSemantics_toMeasure :
    Cslib.IsPureMeasureSemantics P.FreeM fun x => x.toMeasure μ :=
  ⟨toMeasure_pure μ⟩

section Discrete

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

theorem toMeasure_bind (x : P.FreeM α) {f : α → P.FreeM β}
    (hf : Measurable fun a => (f a).toMeasure μ) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ := by
  induction x with
  | pure a => exact (Measure.dirac_bind hf a).symm
  | lift_bind a k ih =>
    rw [liftBind_bind, toMeasure_lift_bind, toMeasure_lift_bind,
      Measure.bind_bind Measurable.of_discrete.aemeasurable hf.aemeasurable]
    exact congrArg _ (funext ih)

theorem isMeasureSemantics_toMeasure :
    Cslib.IsMeasureSemantics P.FreeM fun x => x.toMeasure μ where
  toIsPureMeasureSemantics := isPureMeasureSemantics_toMeasure μ
  map_bind x _ hf := toMeasure_bind μ x hf

theorem toMeasure_map (x : P.FreeM α) {f : α → β} (hf : Measurable f) :
    (x.map f).toMeasure μ = (x.toMeasure μ).map f := by
  rw [← bind_pure_comp, toMeasure_bind μ x (f := pure ∘ f) (Measure.measurable_dirac.comp hf)]
  exact Measure.bind_dirac_eq_map _ hf

@[simp]
theorem toMeasure_bind_of_discrete [DiscreteMeasurableSpace α] (x : P.FreeM α)
    (f : α → P.FreeM β) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  toMeasure_bind μ x .of_discrete

@[simp]
theorem toMeasure_bind_of_discrete' {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] (x : P.FreeM α) (f : α → P.FreeM β) :
    (x >>= f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  toMeasure_bind_of_discrete μ x f

@[simp]
theorem toMeasure_map_of_discrete [DiscreteMeasurableSpace α] (x : P.FreeM α) (f : α → β) :
    (x.map f).toMeasure μ = (x.toMeasure μ).map f :=
  toMeasure_map μ x .of_discrete

@[simp]
theorem toMeasure_map_of_discrete' {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] (x : P.FreeM α) (f : α → β) :
    (f <$> x).toMeasure μ = (x.toMeasure μ).map f :=
  toMeasure_map_of_discrete μ x f

instance [∀ a, IsProbabilityMeasure (μ a)] (x : P.FreeM α) :
    IsProbabilityMeasure (x.toMeasure μ) := by
  induction x with
  | pure a => exact Measure.dirac.isProbabilityMeasure
  | lift_bind a k ih =>
    exact isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable (.of_forall ih)

/-- A measure semantics of `P.FreeM` is the output measure for the measures it gives the
operations. -/
theorem _root_.Cslib.IsMeasureSemantics.eq_toMeasure {α : Type uB} [MeasurableSpace α]
    {sem : ∀ {α : Type uB} [MeasurableSpace α], P.FreeM α → Measure α}
    (hsem : Cslib.IsMeasureSemantics P.FreeM sem) (x : P.FreeM α) :
    sem x = x.toMeasure fun a => sem (lift a) := by
  induction x with
  | pure a => exact hsem.map_pure a
  | lift_bind a k ih =>
    simp only [toMeasure_lift_bind, ← ih]
    exact hsem.map_bind_of_discrete (lift a) k

/-- Interpreting each operation `a` as a program over `Q` answers it by the output measure of that
program. -/
@[simp]
theorem toMeasure_liftM {Q : PFunctor.{uA', uB}} [∀ b, MeasurableSpace (Q.B b)]
    [∀ b, DiscreteMeasurableSpace (Q.B b)] {α : Type uB} [MeasurableSpace α]
    (ν : (b : Q.A) → Measure (Q.B b)) (h : (a : P.A) → Q.FreeM (P.B a)) (x : P.FreeM α) :
    (x.liftM h).toMeasure ν = x.toMeasure fun a => (h a).toMeasure ν := by
  simpa using ((isMeasureSemantics_toMeasure ν).comp (isMonadHom_liftM h)).eq_toMeasure x

end Discrete

end PFunctor.FreeM
