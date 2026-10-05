/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Data.PFunctor.Resumption

/-!
# Embedding well-founded free programs into resumptions

This module contains the canonical inclusion of the initial-algebra
`FreeM p β` into the final-coalgebra `Resumption p β`. Keeping the bridge
above both foundational modules lets the base resumption API remain
independent of the free-monad layer.
-/

@[expose] public section

universe uA uB uα uβ

namespace PFunctor.FreeM

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- Embed a well-founded free program into the corresponding tau-free resumption. -/
def toResumption : FreeM p α → Resumption p α
  | .pure value => Resumption.pure value
  | .liftBind position next =>
      Resumption.query position fun direction => toResumption (next direction)

@[simp] theorem toResumption_pure (value : α) :
    toResumption (pure value : FreeM p α) = Resumption.pure value := rfl

theorem toResumption_liftBind (position : p.A)
    (next : p.B position → FreeM p α) :
    toResumption (FreeM.liftBind position next) =
      Resumption.query position fun direction => toResumption (next direction) := rfl

@[simp] theorem toResumption_lift (position : p.A) :
    toResumption (FreeM.lift position) = Resumption.lift position := rfl

@[simp] theorem toResumption_bind (program : FreeM p α) (k : α → FreeM p β) :
    toResumption (FreeM.bind program k) =
      Resumption.bind (toResumption program) (fun value => toResumption (k value)) := by
  induction program with
  | pure value => simp
  | lift_bind position next ih =>
    simp only [← liftBind_eq, FreeM.bind, toResumption, Resumption.bind_query, ih]

@[simp] theorem toResumption_map (f : α → β) (program : FreeM p α) :
    toResumption (FreeM.map f program) = Resumption.map f (toResumption program) := by
  simp only [← bind_pure_comp, toResumption_bind, Resumption.map, Function.comp_def,
    toResumption_pure]

@[simp] theorem toResumption_bind' {β : Type uα}
    (program : FreeM p α) (k : α → FreeM p β) :
    toResumption (program >>= k) = toResumption program >>= fun value => toResumption (k value) :=
  toResumption_bind program k

@[simp] theorem toResumption_map' {β : Type uα} (f : α → β) (program : FreeM p α) :
    toResumption (f <$> program) = f <$> toResumption program := toResumption_map f program

/-- The free-program embedding is injective: regarding a well-founded tree
as a possibly infinite tree loses no information. -/
theorem toResumption_injective : Function.Injective (toResumption (p := p) (α := α)) := by
  intro left
  induction left with
  | pure value =>
    intro right h
    cases right with
    | pure value' => simpa [← Resumption.dest_inj] using h
    | liftBind position next => simp [← Resumption.dest_inj, toResumption] at h
  | lift_bind position next ih =>
    intro right h
    cases right with
    | pure value => simp [← Resumption.dest_inj, ← liftBind_eq, toResumption] at h
    | liftBind position' next' =>
      obtain ⟨rfl, hnext⟩ := Sigma.mk.inj (Sum.inr.inj (congrArg Resumption.dest h))
      exact congrArg (FreeM.liftBind position)
        (funext fun direction => ih direction (congrFun (eq_of_heq hnext) direction))

/-- The inclusion preserves the monad operations. -/
theorem isMonadHom_toResumption : Cslib.IsMonadHom p.FreeM (Resumption p) toResumption :=
  .mk' toResumption_pure toResumption_bind

end PFunctor.FreeM
