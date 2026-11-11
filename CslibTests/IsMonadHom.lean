/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Control.Monad.IsMonadHom.List

namespace CslibTests.IsMonadHom

open Cslib

variable {m n : Type → Type} [Monad m] [Monad n] {F : ∀ {α}, m α → n α}

-- `grind` moves a monad morphism through a `for` loop over a list,
example (hf : IsMonadHom m n F) (l : List Nat) (step : Nat → Nat → m Nat) :
    F (do
      let mut acc := 0
      for x in l do
        acc ← step acc x
      return acc) =
    (do
      let mut acc := 0
      for x in l do
        acc ← F (step acc x)
      return acc) := by
  grind

-- over an array,
example (hf : IsMonadHom m n F) (xs : Array Nat) (step : Nat → Nat → m Nat) :
    F (do
      let mut acc := 0
      for x in xs do
        acc ← step acc x
      return acc) =
    (do
      let mut acc := 0
      for x in xs do
        acc ← F (step acc x)
      return acc) := by
  grind

-- and over a range, whose loop is a loop over a list when the monads are lawful.
example [LawfulMonad m] [LawfulMonad n] (hf : IsMonadHom m n F) (k : Nat)
    (step : Nat → Nat → m Nat) :
    F (do
      let mut acc := 0
      for i in 0...k do
        acc ← step acc i
      return acc) =
    (do
      let mut acc := 0
      for i in 0...k do
        acc ← F (step acc i)
      return acc) := by
  grind

-- `forIn'` over an array passes the membership proofs through.
example (hf : IsMonadHom m n F) (xs : Array Nat) (init : Nat)
    (f : (a : Nat) → a ∈ xs → Nat → m (ForInStep Nat)) :
    F (forIn' xs init f) = forIn' xs init fun a h b => F (f a h b) := by
  grind

end CslibTests.IsMonadHom
