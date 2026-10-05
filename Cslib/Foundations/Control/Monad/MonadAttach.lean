/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Init.Control.Lawful.MonadAttach.Lemmas
public import Mathlib.Data.List.Monad
public import Mathlib.Data.List.Forall2

/-! # Reachable outputs of monadic list traversals -/

public section

namespace List

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m] {α : Type w} {β : Type u}

/-- Each output of a monadic traversal is reachable from its corresponding input. -/
theorem forall₂_of_canReturn_mapM (f : α → m β) (input : List α) {output : List β}
    (h : MonadAttach.CanReturn (input.mapM f) output) :
    Forall₂ (fun a b => MonadAttach.CanReturn (f a) b) input output := by
  induction input generalizing output with
  | nil =>
    have h := LawfulMonadAttach.eq_of_canReturn_pure h
    subst output
    exact .nil
  | cons a input ih =>
    rw [mapM_cons] at h
    obtain ⟨b, hb, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨rest, hrest, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    cases LawfulMonadAttach.eq_of_canReturn_pure h
    exact .cons hb (ih hrest)

/-- Traversing a list preserves its length on every reachable execution. -/
theorem length_of_canReturn_mapM (f : α → m β) (input : List α) {output : List β}
    (h : MonadAttach.CanReturn (input.mapM f) output) : output.length = input.length :=
  (forall₂_of_canReturn_mapM f input h).length_eq.symm

end List
