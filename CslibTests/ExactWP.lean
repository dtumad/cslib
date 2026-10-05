/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Control.Monad.ExactWP
import Std.Tactic.Do

/-! Exactness and explicit dual readings through a state-and-exception stack. -/

open Cslib Std.WP OrderDual

set_option experimental.vcgen true

namespace CslibTests.ExactWP

abbrev M := ExceptT Unit (StateT Nat Id)
abbrev EPred := (Unit → Nat → Prop) × EStack⟨⟩

def increment (fail : Bool) : M Nat := do
  modify (· + 1)
  if fail then throw () else get

example : ExactWPMonad M (Nat → Prop) EPred := inferInstance

example (post : Nat → Nat → Prop) (onError : Unit → Nat → Prop) :
    wp (increment false) post (onError, ()) = fun s => post (s + 1) (s + 1) := by
  rfl

section Dual

local instance : WPMonad M (Nat → Prop)ᵒᵈ EPredᵒᵈ := ExactWPMonad.dual

-- Override core's direct transformer interpretation with the same chosen reading.
local instance {α} : WP (M α) α (Nat → Prop)ᵒᵈ EPredᵒᵈ := WPMonad.toWP α

example : ExactWPMonad M (Nat → Prop)ᵒᵈ EPredᵒᵈ := inferInstance

example (post : Nat → Nat → Prop) (onError : Unit → Nat → Prop) :
    ofDual (wp (increment true) (fun a => toDual (post a)) (toDual (onError, ()))) =
      fun s => onError () (s + 1) := by
  rfl

example : ⦃toDual (fun s => 0 < s)⦄
    (do let n ← (pure 1 : M Nat); pure (n + 1))
    ⦃fun n => toDual (fun s => n = 2 ∧ 0 < s)⦄ := by
  vcgen
  intro s h
  exact h.2

end Dual

end CslibTests.ExactWP
