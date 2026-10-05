/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Control.Monad.Basic
public import Init.Control.Option

/-! # Monad morphisms through state and optional computations -/

public section

universe u v w w'

namespace StateT

variable {m : Type u → Type v} {n : Type u → Type w} {p : Type u → Type w'}
  {State α : Type u}

/-- Apply a transformation of the underlying monad, retaining the result and final state. -/
@[inline, expose] def mapMonad (F : ∀ {α}, m α → n α) (x : StateT State m α) : StateT State n α :=
  .mk fun state => F (x.run state)

@[simp] theorem run_mapMonad (F : ∀ {α}, m α → n α) (x : StateT State m α) (state : State) :
    (mapMonad F x).run state = F (x.run state) := rfl

@[simp] theorem mapMonad_id (x : StateT State m α) : mapMonad id x = x := rfl

@[simp] theorem mapMonad_comp (G : ∀ {α}, n α → p α) (F : ∀ {α}, m α → n α)
    (x : StateT State m α) : mapMonad (G ∘ F) x = mapMonad G (mapMonad F x) := rfl

theorem mapMonad_eq_monadMap (F : ∀ {α}, m α → m α) (x : StateT State m α) :
    mapMonad F x = monadMap @F x := rfl

end StateT

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w} {p : Type u → Type w'} {α : Type u}

/-- Apply a transformation of the underlying monad to the optional result. -/
@[inline, expose] def mapMonad (F : ∀ {α}, m α → n α) (x : OptionT m α) : OptionT n α :=
  F x.run

@[simp] theorem run_mapMonad (F : ∀ {α}, m α → n α) (x : OptionT m α) :
    (mapMonad F x).run = F x.run := rfl

@[simp] theorem mapMonad_id (x : OptionT m α) : mapMonad id x = x := rfl

@[simp] theorem mapMonad_comp (G : ∀ {α}, n α → p α) (F : ∀ {α}, m α → n α)
    (x : OptionT m α) : mapMonad (G ∘ F) x = mapMonad G (mapMonad F x) := rfl

theorem mapMonad_eq_monadMap (F : ∀ {α}, m α → m α) (x : OptionT m α) :
    mapMonad F x = monadMap @F x := rfl

end OptionT

namespace Cslib.IsMonadHom

variable {m : Type u → Type v} {n : Type u → Type w}
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  {F : ∀ {α}, m α → n α}

/-- Apply a monad morphism to the joint result and state. -/
theorem stateT (hf : IsMonadHom m n F) (State : Type u) :
    IsMonadHom (StateT State m) (StateT State n) (StateT.mapMonad F) :=
  .mk' (fun a => funext fun state => hf.map_pure (a, state))
    (fun x f => funext fun state => hf.map_bind (x.run state) (fun out => (f out.1).run out.2))

/-- Apply a monad morphism to the optional result, preserving early failure. -/
theorem optionT (hf : IsMonadHom m n F) :
    IsMonadHom (OptionT m) (OptionT n) (OptionT.mapMonad F) :=
  .mk' (fun a => hf.map_pure (some a)) (fun x _ =>
    (hf.map_bind x.run _).trans (bind_congr fun | none => hf.map_pure none | some _ => rfl))

end Cslib.IsMonadHom

namespace Cslib

/-- Flatten independent state layers, preserving both final states. -/
theorem isMonadHom_stateT_stateT {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (State Tape : Type u) :
    IsMonadHom (StateT State (StateT Tape m)) (StateT (State × Tape) m)
      (fun action (state, tape) =>
        (fun out => (out.1.1, out.1.2, out.2)) <$> action state tape) :=
  .mk' (fun value => funext fun (state, tape) => map_pure _ _)
    (fun action cont => funext fun (state, tape) => by
      simp only [Bind.bind, StateT.bind, map_eq_pure_bind, bind_assoc, pure_bind])

/-- Changing a state representation through an equivalence preserves the entire computation. -/
theorem isMonadHom_stateT_equiv {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {State Encoded : Type u} (equiv : Encoded ≃ State) :
    IsMonadHom (StateT State m) (StateT Encoded m)
      (fun action state => (fun out => (out.1, equiv.symm out.2)) <$> action (equiv state)) :=
  .mk' (fun value => funext fun state => by
      simp only [Pure.pure, StateT.pure, map_pure, Equiv.symm_apply_apply])
    (fun action cont => funext fun state => by
      simp only [Bind.bind, StateT.bind, map_eq_pure_bind, bind_assoc, pure_bind,
        Equiv.apply_symm_apply])

end Cslib
