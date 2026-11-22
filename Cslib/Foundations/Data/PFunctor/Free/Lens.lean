/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Data.PFunctor.Lens

/-!
# Relabeling a free program along a polynomial lens

Each source operation becomes one target operation. The backward direction map selects the
source continuation. Interpreting the resulting program amounts to pulling the target handler
back along the lens.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃ v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
variable {α β : Type*}

/-- Transport a free polynomial tree along a polynomial lens.

The source polynomial `P` is the abstract/control interface. The target
polynomial `Q` is the concrete/runtime interface. At each `P`-node, the lens
chooses a `Q`-position by `toFunA`; when runtime supplies a `Q`-direction,
`toFunB` maps it back to the corresponding `P`-direction selecting the
control continuation. -/
@[implicit_reducible]
protected def mapLens (l : Lens P Q) : FreeM P α → FreeM Q α
  | .pure x => .pure x
  | .liftBind a rest => .liftBind (l.toFunA a) fun d =>
      (rest (l.toFunB a d)).mapLens l

@[simp]
theorem mapLens_pure (l : Lens P Q) (x : α) :
    (pure x : FreeM P α).mapLens l = FreeM.pure x :=
  rfl

theorem mapLens_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) :
    (FreeM.liftBind a rest).mapLens l =
      FreeM.liftBind (l.toFunA a) (fun d ↦ (rest (l.toFunB a d)).mapLens l) :=
  rfl

@[simp]
theorem mapLens_id (x : FreeM P α) :
    x.mapLens (Lens.id P) = x := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind a) (funext ih)

@[simp]
theorem mapLens_mapLens (l₂ : Lens Q R) (l₁ : Lens P Q) (x : FreeM P α) :
    (x.mapLens l₁).mapLens l₂ = x.mapLens (l₂ ∘ₗ l₁) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih =>
      exact congrArg (FreeM.liftBind (l₂.toFunA (l₁.toFunA a))) (funext fun d => ih _)

theorem mapLens_bind (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (FreeM.bind x f).mapLens l =
      FreeM.bind (x.mapLens l) (fun a => (f a).mapLens l) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind (l.toFunA a)) (funext fun d => ih _)

@[simp]
theorem mapLens_bind' {α β : Type v} (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapLens l = x.mapLens l >>= fun a => (f a).mapLens l := mapLens_bind l x f

/-- Relabelling a program along a lens commutes with mapping its results. -/
@[simp]
theorem mapLens_map {α β : Type v} (l : Lens P Q) (f : α → β) (x : FreeM P α) :
    (f <$> x).mapLens l = f <$> x.mapLens l := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind (l.toFunA a)) (funext fun d => ih _)

/-- Interpreting after relabeling answers each source call through the target handler. -/
theorem liftM_mapLens {Q : PFunctor.{uA₂, uB}} {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    {α : Type uB} (l : Lens P Q) (h : (a : Q.A) → m (Q.B a)) (x : P.FreeM α) :
    (x.mapLens l).liftM h = x.liftM (fun a => l.toFunB a <$> h (l.toFunA a)) := by
  induction x using FreeM.rec with
  | pure => rfl
  | liftBind a rest ih =>
    change (h (l.toFunA a) >>= fun d => ((rest (l.toFunB a d)).mapLens l).liftM h) =
      (l.toFunB a <$> h (l.toFunA a)) >>= fun b => (rest b).liftM _
    rw [bind_map_left]
    exact bind_congr fun d => ih _

end PFunctor.FreeM
