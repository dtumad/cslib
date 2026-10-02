/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Computational.Ensemble

/-!
# Pseudorandom generators

A secure generator is deterministic polynomial time, stretches every input length, and maps uniform
seeds to an ensemble computationally indistinguishable from uniform words of the output length.
Both experiments give the distinguisher the seed-length security parameter. The expansion function
is constrained by actual output length and polynomial-time evaluation; it is not a free source of
exponentially long outputs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.3.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- The output ensemble obtained from uniform seeds. -/
noncomputable def generatorEnsemble (generator : Word → Word) (n : ℕ) : PMF Word :=
  (uniformBits n).map generator

/-- The real PRG experiment: expand a uniform seed, then invoke the distinguisher. -/
noncomputable def prgRealGame (generator : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := distinguishingGame (generatorEnsemble generator n) (adversary n)

/-- The ideal PRG experiment: give the distinguisher a uniform word of the output length. -/
noncomputable def prgIdealGame (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := distinguishingGame (uniformBits (length n)) (adversary n)

/-- A secure pseudorandom generator of the specified stretch, against uniform PPT distinguishers. -/
def PseudorandomGenerator (generator : Word → Word) (length : ℕ → ℕ) : Prop :=
  IsPolyTime id generator ∧
  (∀ input, (generator input).length = length input.length) ∧
  (∀ n, n < length n) ∧
  ComputationallyIndistinguishable (generatorEnsemble generator) (fun n => uniformBits (length n))

/-- The generator's stretch is necessarily bounded by a polynomial. -/
theorem PseudorandomGenerator.length_le {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ c d : ℕ, ∀ n, length n ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hbound⟩ := h.1.length_le
  refine ⟨c, d, fun n => ?_⟩
  simpa [h.2.1] using hbound (List.replicate n false)

/-- A generator's real samples have polynomially bounded length. -/
theorem PseudorandomGenerator.bounded_real {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    PolynomiallyBoundedEnsemble (generatorEnsemble generator) :=
  (PolynomiallyBoundedEnsemble.uniformBits PolynomiallyBounded.id).map h.1

/-- A generator's ideal samples have polynomially bounded length as well. -/
theorem PseudorandomGenerator.bounded_ideal {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    PolynomiallyBoundedEnsemble (fun n => uniformBits (length n)) :=
  PolynomiallyBoundedEnsemble.uniformBits h.length_le

end Cslib.Crypto
