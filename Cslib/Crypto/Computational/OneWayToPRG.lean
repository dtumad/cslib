/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Generator
public import Cslib.Crypto.Computational.Pseudoentropy.OneWay

/-!
# Pseudorandom generators from one-way functions

A general uniform one-way function gives a samplable pseudoentropy pair. Its inverse-polynomial
gap admits a polynomial entropy grid, and the pseudoentropy construction gives a deterministic
polynomial-time generator expanding every input by one bit. All security reductions are uniform
strict PPT, and no entropy estimate or nonuniform advice is an additional hypothesis.

## References

* Johan Håstad, Russell Impagliazzo, Leonid Levin, and Michael Luby,
  *A Pseudorandom Generator from Any One-Way Function*, SIAM Journal on Computing 28(4), 1999,
  [original theorem](https://doi.org/10.1137/S0097539793244708).
* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction
  for Any Hardness*, TCC 2006, Sections 4–5,
  [construction followed here](https://crypto.ethz.ch/publications/files/Holens06.pdf).

The matrix extractor and uniform length conversion preserve the polynomial guarantees;
we do not assert the write-up's optimized seed-length exponent or practical efficiency.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Pseudoentropy

/-- Every uniform one-way function implies a uniform pseudorandom generator with one bit of
stretch at every seed length. The existence of a one-way function remains the sole assumption. -/
theorem OneWay.exists_pseudorandomGenerator {f : Word → Word} (hf : OneWay f) :
    ∃ generator : Word → Word, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨pair, hpair⟩ := hf.exists_pseudoentropyPair
  exact hpair.exists_pseudorandomGenerator (densityBound := fun n => 16 * (n + 7))
    (by polytime) (Filter.Eventually.of_forall EntropyGrid.four_steps_le_owf_gap)

end Cslib.Crypto
