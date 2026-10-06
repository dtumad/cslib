/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.PNat.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Group generators

A group generator (`GroupGen`) is an algorithm, a program in a monad `m₀`, that samples for each
security parameter the description of a cyclic group with a generator of known order: every
element is the generator raised to exactly one exponent below the order. Assumptions such as the
hardness of decisional Diffie–Hellman are stated relative to a group generator.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto

/-- A group generator: for each security parameter, a program in `m₀` sampling the description of a
cyclic group with a generator of known order. -/
structure GroupGen (m₀ : Type → Type*) where
  /-- Descriptions of groups. -/
  Desc : Type
  /-- The elements of the described group. -/
  Elem : Desc → Type
  [group : ∀ d, Group (Elem d)]
  /-- The order of the described group. -/
  order : Desc → ℕ+
  /-- The generator of the described group. -/
  gen : ∀ d, Elem d
  /-- Each element is the generator raised to exactly one exponent below the order. -/
  bijective_pow : ∀ d, Function.Bijective fun x : Fin (order d) => gen d ^ x.val
  /-- Sample a group description for the security parameter. -/
  setup : ℕ → m₀ Desc

namespace GroupGen

attribute [instance] group

variable {m₀ : Type → Type*} (𝒢 : GroupGen m₀)

instance : MeasurableSpace 𝒢.Desc := ⊤

instance : DiscreteMeasurableSpace 𝒢.Desc := ⟨fun _ => trivial⟩

instance (d : 𝒢.Desc) : MeasurableSpace (𝒢.Elem d) := ⊤

instance (d : 𝒢.Desc) : DiscreteMeasurableSpace (𝒢.Elem d) := ⟨fun _ => trivial⟩

instance (d : 𝒢.Desc) : Finite (𝒢.Elem d) := .of_surjective _ (𝒢.bijective_pow d).2

end GroupGen

end Cslib.Crypto
