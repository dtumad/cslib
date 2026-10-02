/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Cslib.Probability.BitString

/-!
# Polynomially bounded ensembles

The general indistinguishability definition measures a distinguisher's time in the combined length
of the unary security parameter and its sample. `PolynomiallyBoundedEnsemble` supplies the usual
additional convention that every sample has length polynomial in the security parameter.
`PolynomiallyBoundedEnsemble.clock_bound` then bounds the distinguisher's clock by a polynomial in
the security parameter alone.

This bounds sample lengths, without assuming efficient sampling. Uniform binary samples,
PPT outputs on empty auxiliary input, and deterministic polynomial-time images satisfy it.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Every supported word has length bounded by a polynomial in the security parameter. -/
def PolynomiallyBoundedEnsemble (X : ℕ → PMF Word) : Prop :=
  ∃ size : ℕ → ℕ, PolynomiallyBounded size ∧
    ∀ n word, word ∈ (X n).support → word.length ≤ size n

namespace PolynomiallyBoundedEnsemble

/-- Uniform words of polynomially bounded length form a polynomially bounded ensemble. -/
theorem uniformBits {size : ℕ → ℕ} (hsize : PolynomiallyBounded size) :
    PolynomiallyBoundedEnsemble (fun n => Probability.uniformBits (size n)) := by
  refine ⟨size, hsize, fun n word hword => ?_⟩
  exact (length_of_mem_support_uniformBits hword).le

/-- An efficiently computed image preserves the bound on sample lengths. -/
theorem map {X : ℕ → PMF Word} {f : Word → Word}
    (hX : PolynomiallyBoundedEnsemble X) (hf : IsPolyTime id f) :
    PolynomiallyBoundedEnsemble (fun n => (X n).map f) := by
  obtain ⟨size, hsize, hX⟩ := hX
  obtain ⟨c, d, hf⟩ := hf.length_le
  refine ⟨fun n => c * (size n + 1) ^ d,
    (PolynomiallyBounded.const c).mul ((hsize.add (.const 1)).pow d), ?_⟩
  intro n word hword
  obtain ⟨input, hinput, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  exact (hf input).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_left (Nat.add_le_add_right (hX n input hinput) 1) d))

/-- Any PPT sampler on empty auxiliary input produces polynomially bounded samples. -/
theorem of_isPPT {program : ℕ → Word → ProbComp Word} (h : IsPPT wordEncoding program) :
    PolynomiallyBoundedEnsemble (fun n => ProbComp.eval (program n [])) := by
  obtain ⟨c, d, h⟩ := h.length_le
  refine ⟨fun n => c * (n + 2) ^ d,
    (PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d), ?_⟩
  intro n word hword
  simpa [wordEncoding] using h n [] word hword

/-- On these samples, a clock polynomial in parameter plus input length is bounded by a
polynomial in the security parameter alone. -/
theorem clock_bound {X : ℕ → PMF Word} (hX : PolynomiallyBoundedEnsemble X) (c d : ℕ) :
    ∃ c' d' : ℕ, ∀ n word, word ∈ (X n).support →
      c * (n + word.length + 2) ^ d ≤ c' * (n + 1) ^ d' := by
  obtain ⟨size, hsize, hX⟩ := hX
  have hclock := (PolynomiallyBounded.const c).mul
    (((PolynomiallyBounded.id.add hsize).add (.const 2)).pow d)
  obtain ⟨c', d', hclock⟩ := hclock
  refine ⟨c', d', fun n word hword => ?_⟩
  apply le_trans _ (hclock n)
  apply Nat.mul_le_mul_left c (Nat.pow_le_pow_left _ d)
  have := hX n word hword
  omega

end PolynomiallyBoundedEnsemble

end Cslib.Crypto
