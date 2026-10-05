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

namespace Cslib.IsMonadHom

universe u v w

variable {m : Type u → Type v} {n : Type u → Type w}
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  {F : ∀ {α}, m α → n α}

/-- Apply a monad morphism to the joint result and state. -/
theorem stateT (hf : IsMonadHom m n F) (State : Type u) :
    IsMonadHom (StateT State m) (StateT State n)
      (fun x state => F (x.run state)) := by
  apply IsMonadHom.mk'
  · intro α a
    funext state
    exact hf.map_pure (a, state)
  · intro α β x f
    funext state
    exact hf.map_bind (x.run state) (fun out => (f out.1).run out.2)

/-- Apply a monad morphism to the optional result, preserving early failure. -/
theorem optionT (hf : IsMonadHom m n F) :
    IsMonadHom (OptionT m) (OptionT n) (fun x => OptionT.mk (F x.run)) := by
  apply IsMonadHom.mk'
  · intro α a
    exact hf.map_pure (some a)
  · intro α β x f
    change F (x.run >>= _) = F x.run >>= _
    rw [hf.map_bind]
    congr 1
    funext out
    cases out with
    | none => exact hf.map_pure none
    | some a => rfl

end Cslib.IsMonadHom

namespace Cslib

universe u v

/-- Flatten independent state layers, preserving both final states. -/
theorem isMonadHom_stateT_stateT {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (State Tape : Type u) :
    IsMonadHom (StateT State (StateT Tape m)) (StateT (State × Tape) m)
      (fun action (state, tape) =>
        (fun out => (out.1.1, out.1.2, out.2)) <$> action state tape) := by
  apply IsMonadHom.mk'
  · intro α value
    funext ⟨state, tape⟩
    exact map_pure _ _
  · intro α β action cont
    funext ⟨state, tape⟩
    simp only [Bind.bind, StateT.bind, map_eq_pure_bind, bind_assoc, pure_bind]

/-- Changing a state representation through an equivalence preserves the entire computation. -/
theorem isMonadHom_stateT_equiv {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {State Encoded : Type u} (equiv : Encoded ≃ State) :
    IsMonadHom (StateT State m) (StateT Encoded m)
      (fun action state => (fun out => (out.1, equiv.symm out.2)) <$> action (equiv state)) := by
  apply IsMonadHom.mk'
  · intro α value
    funext state
    simp only [Pure.pure, StateT.pure, map_pure, Equiv.symm_apply_apply]
  · intro α β action cont
    funext state
    simp only [Bind.bind, StateT.bind, map_eq_pure_bind, bind_assoc, pure_bind,
      Equiv.apply_symm_apply]

end Cslib
