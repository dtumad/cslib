/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.WP
import Std.Tactic.Do

/-! Core verification-condition generation under explicitly selected structural readings. -/

open PFunctor Std.WP

set_option experimental.vcgen true

namespace CslibTests.PFunctorWP

abbrev coin : PFunctor := ⟨Unit, fun _ => Bool⟩

def program : coin.FreeM Bool := do
  let b ← FreeM.lift ()
  if b then pure true else pure (!b)

section Necessary

local instance : WPMonad coin.FreeM Prop EStack⟨⟩ := FreeM.forallWP (fun _ => Set.univ)

example : LawfulWPMonadAttach coin.FreeM Prop EStack⟨⟩ := inferInstance
local instance (x : coin.FreeM Bool) : WPConjunctive x :=
  FreeM.forallWP_conjunctive (fun _ => Set.univ) x

example : WPConjunctive program := inferInstance
example : Cslib.ExactWPMonad coin.FreeM Prop EStack⟨⟩ := inferInstance

example : ⦃True⦄ program ⦃fun b => b = true⦄ := by
  vcgen [program]
  simp_all

end Necessary

section Possible

local instance : WPMonad coin.FreeM Prop EStack⟨⟩ := FreeM.existsWP (fun _ => Set.univ)

-- Keep the dependent result type explicit for core's symbolic spec matcher.
example : ⦃True⦄ FreeM.lift (P := coin) () ⦃fun b : coin.B () => b = true⦄ := by
  vcgen
  exact ⟨true, Set.mem_univ _, rfl⟩

end Possible

-- Possibility of true must not imply that all executions return true.
example : ¬ ((FreeM.forallWP (P := coin) (fun _ => Set.univ)).toWP Bool).wp
    (FreeM.lift (P := coin) ()) (fun b => b = true) () := by
  intro h
  have := (FreeM.forallWP_univ_iff _ _).mp h false (FreeM.canReturn_lift _ _)
  cases this

section ChosenResponses

local instance : WPMonad coin.FreeM Prop EStack⟨⟩ := FreeM.forallWP (fun _ => {true})

example : ⦃True⦄ FreeM.lift (P := coin) () ⦃fun b : coin.B () => b = true⦄ := by
  vcgen
  simp_all

end ChosenResponses

example (responses : (op : coin.A) → Set (coin.B op)) (post : coin.B () → Prop) :
    letI : WPMonad coin.FreeM Prop EStack⟨⟩ := FreeM.forallWP responses
    ⦃∀ b ∈ responses (), post b⦄ FreeM.lift (P := coin) () ⦃post⦄ := by
  let : WPMonad coin.FreeM Prop EStack⟨⟩ := FreeM.forallWP responses
  vcgen
  grind

end CslibTests.PFunctorWP
