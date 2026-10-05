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

/-- Flatten optional failure around a stateful partial computation. A failed result discards
its state, just like a failure in the underlying state computation. -/
theorem isMonadHom_optionT_stateT_option (State : Type) :
    IsMonadHom (OptionT (StateT State Option)) (StateT State Option)
      (fun action state => do
        let (out, state') ← action.run state
        let value ← out
        pure (value, state')) := by
  apply IsMonadHom.mk'
  · intro α value
    rfl
  · intro α β action cont
    funext state
    dsimp only [Bind.bind, StateT.bind, OptionT.bind, OptionT.mk, OptionT.run,
      Pure.pure, StateT.pure, OptionT.pure]
    cases h : action state with
    | none => rfl
    | some out =>
      rcases out with ⟨out, state'⟩
      cases out <;> rfl

/-- Flatten optional failure around an effectful state computation. Either failure discards
the state, while a successful result retains the state and all preceding ambient effects. -/
theorem isMonadHom_optionT_stateT_optionT {m : Type → Type*} [Monad m] [LawfulMonad m]
    (State : Type) :
    IsMonadHom (OptionT (StateT State (OptionT m))) (StateT State (OptionT m))
      (fun action state => do
        let (out, state') ← action.run state
        let value ← OptionT.mk (pure out)
        pure (value, state')) := by
  apply IsMonadHom.mk'
  · intro α value
    funext state
    simp [Pure.pure, StateT.pure, OptionT.pure, OptionT.run, OptionT.mk,
      Bind.bind, OptionT.bind]
  · intro α β action cont
    funext state
    dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.mk, OptionT.run,
      Pure.pure, StateT.pure, OptionT.pure]
    simp only [LawfulMonad.bind_assoc]
    congr 1
    funext out
    cases out with
    | none => simp
    | some out =>
      rcases out with ⟨out, state'⟩
      cases out <;> simp [StateT.pure, Pure.pure, OptionT.pure, OptionT.mk]

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

/-- Flatten private state and two possible failures while retaining the ambient effects.
Either failure rejects the result together with both states. -/
theorem isMonadHom_stateT_optionT_stateT_optionT {m : Type → Type*}
    [Monad m] [LawfulMonad m] (State Tape : Type) :
    IsMonadHom (StateT State (OptionT (StateT Tape (OptionT m))))
      (StateT (State × Tape) (OptionT m))
      (fun action (state, tape) => do
        let (out, tape') ← (action state).run tape
        let (value, state') ← OptionT.mk (pure out)
        pure (value, state', tape')) := by
  apply IsMonadHom.mk'
  · intro α value
    funext ⟨state, tape⟩
    simp [Pure.pure, StateT.pure, OptionT.pure, OptionT.run, OptionT.mk,
      Bind.bind, OptionT.bind]
  · intro α β action cont
    funext ⟨state, tape⟩
    dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.mk, OptionT.run,
      Pure.pure, StateT.pure, OptionT.pure]
    simp only [LawfulMonad.bind_assoc]
    congr 1
    funext out
    cases out with
    | none => simp
    | some out =>
      rcases out with ⟨out, tape'⟩
      cases out with
      | none =>
        dsimp +instances only [StateT.pure, Pure.pure, OptionT.pure, OptionT.mk]
        simp
      | some out => simp

end Cslib
