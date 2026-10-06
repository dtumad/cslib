/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Defs

/-!
# The decisional Diffie–Hellman experiments

For a group element `g` and exponents in `Fin n`, a test distinguishes a Diffie–Hellman triple
`(g ^ x, g ^ r, g ^ (x * r))` from a triple `(g ^ x, g ^ r, g ^ z)` with an independent third
exponent. The experiments are programs in an arbitrary monad `m`, given a sampler of exponents;
the assumption that the two are hard to distinguish is stated about their output distributions
under a chosen semantics of `m`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.DDH

variable {m : Type → Type*} [Monad m] {G : Type} [Monoid G] {n : ℕ}

/-- Run a test on a Diffie–Hellman triple. -/
def realExperiment (sample : m (Fin n)) (g : G) (test : G → G → G → m Bool) : m Bool := do
  let x ← sample
  let r ← sample
  test (g ^ x.val) (g ^ r.val) (g ^ (x.val * r.val))

/-- Run a test on a triple whose third exponent is sampled independently. -/
def idealExperiment (sample : m (Fin n)) (g : G) (test : G → G → G → m Bool) : m Bool := do
  let x ← sample
  let r ← sample
  let z ← sample
  test (g ^ x.val) (g ^ r.val) (g ^ z.val)

end Cslib.Crypto.DDH
