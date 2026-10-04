/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Init.Internal.Order
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Mathlib lattices as core assertion lattices

This explicit construction lets a client of `Std.WP` use a Mathlib complete lattice without
installing competing global order instances. Adapted from PolyFun's `ToCslib.Order.LeanOrder`.
-/

@[expose] public section

/-- Regard a Mathlib complete lattice as a core complete lattice, with the same order. -/
@[instance_reducible]
def Lean.Order.CompleteLattice.ofMathlib (α : Type*) [_root_.CompleteLattice α] :
    Lean.Order.CompleteLattice α where
  rel := (· ≤ ·)
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup c := ⟨sSup {x | c x}, fun _ =>
    ⟨fun h _ hy => le_trans (le_sSup hy) h, fun h => sSup_le h⟩⟩
