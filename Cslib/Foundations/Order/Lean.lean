/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
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

namespace Lean.Order

universe u

variable {α : Type u}

/-- Core's order read backwards on the order dual. -/
instance instPartialOrderOrderDual [PartialOrder α] : PartialOrder αᵒᵈ where
  rel x y := PartialOrder.rel (α := α) y x
  rel_refl := PartialOrder.rel_refl (α := α)
  rel_trans h₁ h₂ := PartialOrder.rel_trans (α := α) h₂ h₁
  rel_antisymm h₁ h₂ := PartialOrder.rel_antisymm (α := α) h₂ h₁

/-- The order dual of a complete lattice: the supremum of a predicate is its infimum below. -/
instance instCompleteLatticeOrderDual [CompleteLattice α] : CompleteLattice αᵒᵈ :=
  { instPartialOrderOrderDual (α := α) with
    has_sup := fun c => ⟨inf (α := α) c, fun _ => inf_spec (α := α)⟩ }

/-- The dual order is the original order with its arguments swapped. -/
theorem rel_orderDual [PartialOrder α] (x y : αᵒᵈ) :
    PartialOrder.rel x y = PartialOrder.rel (α := α) (OrderDual.ofDual y) (OrderDual.ofDual x) :=
  rfl

end Lean.Order
