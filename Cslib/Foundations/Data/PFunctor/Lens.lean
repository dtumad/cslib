/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic

/-!
# Lenses between polynomial functors

A lens sends each source position to a target position and takes a direction at that target
position back to a source direction. When the polynomials describe query interfaces, the two
maps translate the outgoing request and decode its reply.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

/-- A forward map on positions and a backward map on their associated directions. -/
structure Lens (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward map on positions, sending each position of `P` to a position of `Q`. -/
  toFunA : P.A → Q.A
  /-- The backward map on directions, pulling a direction of `Q` at `toFunA a` back to a
  direction of `P` at `a`. -/
  toFunB : ∀ a, Q.B (toFunA a) → P.B a

/-- Infix notation for constructing a lens `toFunA ⇆ toFunB`; activate it with
`open scoped PFunctor`. -/
scoped infixr:25 " ⇆ " => Lens.mk

namespace Lens

/-- The identity lens -/
@[reducible]
protected def id (P : PFunctor.{uA, uB}) : Lens P P where
  toFunA := fun a => a
  toFunB := fun _ b => b

/-- Composition of lenses -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA := l.toFunA ∘ l'.toFunA
  toFunB := fun i => (l'.toFunB i) ∘ l.toFunB (l'.toFunA i)

@[inherit_doc] scoped[PFunctor] infixl:75 " ∘ₗ " => PFunctor.Lens.comp

@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    (Lens.id Q) ∘ₗ f = f := rfl

@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    f ∘ₗ (Lens.id P) = f := rfl

theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (l : Lens R S) (l' : Lens Q R) (l'' : Lens P Q) :
    (l ∘ₗ l') ∘ₗ l'' = l ∘ₗ (l' ∘ₗ l'') := rfl

end Lens

end PFunctor
