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

/-- Flatten two state layers and reject either optional failure. A failed computation exposes
neither state; successful computations retain both states in their original order. -/
theorem isMonadHom_stateT_optionT_stateT (State Tape : Type) :
    IsMonadHom (StateT State (OptionT (StateT Tape Option))) (StateT (State × Tape) Option)
      (fun action (state, tape) => do
        let (out, tape') ← (action state).run tape
        let (value, state') ← out
        pure (value, state', tape')) := by
  apply IsMonadHom.mk'
  · intro α value
    rfl
  · intro α β action cont
    funext ⟨state, tape⟩
    dsimp only [Bind.bind, StateT.bind, OptionT.bind, OptionT.mk, OptionT.run,
      Pure.pure, StateT.pure, OptionT.pure]
    cases h : action state tape with
    | none => rfl
    | some out =>
      rcases out with ⟨out, tape'⟩
      cases out with
      | none => rfl
      | some out => rfl

end Cslib
