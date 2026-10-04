/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Indexed effects as polynomial effects

A type-indexed effect family determines a polynomial functor: a shape packages an answer type
and an effect returning that type. The two free-monad presentations are equivalent, including
their interpretation in any monad. Packaging the answer type increases the shape universe;
signatures that already specify their answer types directly need no such increase.
-/

@[expose] public section

universe u v w w' z

/-- Package a type-indexed effect family as shapes with dependent answer types. -/
def PFunctor.ofFamily (F : Type u → Type v) : PFunctor.{max (u + 1) v, u} :=
  ⟨Σ α, F α, Sigma.fst⟩

namespace Cslib.FreeM

variable {F : Type u → Type v} {α : Type w} {β : Type w'}

/-- Regard a free program over indexed effects as a polynomial free program. -/
def toPFunctor : FreeM F α → (PFunctor.ofFamily F).FreeM α
  | .pure a => pure a
  | .liftBind (ι := ι) op cont => .liftBind ⟨ι, op⟩ fun b => toPFunctor (cont b)

/-- Recover the indexed-effect presentation of a polynomial program over `ofFamily`. -/
def ofPFunctor : (PFunctor.ofFamily F).FreeM α → FreeM F α
  | .pure a => pure a
  | .liftBind ⟨_, op⟩ cont => .liftBind op fun b => ofPFunctor (cont b)

@[simp]
theorem toPFunctor_pure (a : α) : toPFunctor (pure a : FreeM F α) = pure a := rfl

@[simp]
theorem ofPFunctor_pure (a : α) : ofPFunctor (pure a : (PFunctor.ofFamily F).FreeM α) =
    (pure a : FreeM F α) := rfl

@[simp]
theorem ofPFunctor_toPFunctor (x : FreeM F α) : ofPFunctor (toPFunctor x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change liftBind op (fun b => ofPFunctor (toPFunctor (cont b))) = liftBind op cont
    congr 1
    exact funext ih

@[simp]
theorem toPFunctor_ofPFunctor (x : (PFunctor.ofFamily F).FreeM α) :
    toPFunctor (ofPFunctor x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    rcases op with ⟨ι, op⟩
    change PFunctor.FreeM.liftBind (P := PFunctor.ofFamily F) ⟨ι, op⟩
      (fun b => toPFunctor (ofPFunctor (cont b))) =
        PFunctor.FreeM.liftBind (P := PFunctor.ofFamily F) ⟨ι, op⟩ cont
    congr 1
    exact funext ih

/-- The indexed and polynomial presentations of a free program are equivalent. -/
def equivPFunctor : FreeM F α ≃ (PFunctor.ofFamily F).FreeM α where
  toFun := toPFunctor
  invFun := ofPFunctor
  left_inv := ofPFunctor_toPFunctor
  right_inv := toPFunctor_ofPFunctor

@[simp]
theorem toPFunctor_bind (x : FreeM F α) (f : α → FreeM F β) :
    toPFunctor (x.bind f) = (toPFunctor x).bind fun a => toPFunctor (f a) := by
  induction x with
  | pure a => rfl
  | @lift_bind ι op cont ih =>
    change PFunctor.FreeM.liftBind (P := PFunctor.ofFamily F) ⟨ι, op⟩
      (fun b => toPFunctor ((cont b).bind f)) =
        PFunctor.FreeM.liftBind (P := PFunctor.ofFamily F) ⟨ι, op⟩
          (fun b => (toPFunctor (cont b)).bind _)
    congr 1
    exact funext ih

/-- Both syntax presentations have the same interpretation, including stateful interpretations. -/
theorem liftM_toPFunctor {m : Type u → Type z} [Monad m] {α : Type u}
    (interp : {β : Type u} → F β → m β) (x : FreeM F α) :
    (toPFunctor x).liftM (fun op : (PFunctor.ofFamily F).A => interp op.2) =
      x.liftM interp := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change (interp op >>= fun b => (toPFunctor (cont b)).liftM _) =
      (interp op >>= fun b => (cont b).liftM interp)
    congr 1
    exact funext ih

end Cslib.FreeM
