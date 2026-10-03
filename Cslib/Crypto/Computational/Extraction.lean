/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.LinearHash
public import Cslib.Crypto.Computational.Reduction
public import Cslib.Crypto.Computational.Statistical

/-!
# Extracting computationally indistinguishable sources

An efficiently computable extractor preserves computational indistinguishability. If the comparison
source has sufficiently small collision probability, the leftover hash lemma then replaces its
extracted bits by uniform bits. The hash seed is revealed in both experiments.

This is a step toward OWF-to-PRG, not the full implication: a suitable high-entropy comparison
source is an explicit hypothesis. In particular, this file does not derive that hypothesis from
one-wayness or presume that an arbitrary one-way function preserves uniformity.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 3.3 (Lemma 1) and Section 5 (extraction in the PRG construction).
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use Boolean-matrix hashing and the library's uniform PPT postprocessing theorem.
* Johan Håstad, Russell Impagliazzo, Leonid Levin, and Michael Luby,
  *A Pseudorandom Generator from Any One-Way Function*, SIAM Journal on Computing 28(4), 1999.
  [Original OWF-to-PRG theorem](https://doi.org/10.1137/S0097539793244708).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Probability.PMF

/-- A source indistinguishable from a sufficiently diffuse source yields computationally uniform
extraction. The comparison source need not be efficiently sampled; the extractor is PPT. -/
theorem ComputationallyIndistinguishable.extract_uniform {X : ℕ → PMF Word}
    {length : ℕ → ℕ} {source : ∀ n, PMF (BitString (length n))}
    (hsource : ComputationallyIndistinguishable X (fun n => (source n).map List.ofFn))
    (count : ℕ → ℕ)
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hcollision : Negligible (fun n => (2 : ℝ) ^ count n * collisionProbability (source n))) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun input => ProbComp.eval (LinearHash.extract (count n) input)))
      (fun n => uniformBits (count n * length n + count n)) := by
  have hPPT : IsPPT wordEncoding (fun n input => LinearHash.extract (count n) input) := by ppt
  apply (hsource.bind (fun n input => LinearHash.extract (count n) input) hPPT).trans
  apply StatisticallyIndistinguishable.computationallyIndistinguishable
  apply negligible_of_le (hcollision.sqrt.mul_const (2 : ℝ)⁻¹) (fun _ => dist_nonneg)
  intro n
  simpa only [div_eq_mul_inv] using LinearHash.extract_distance_le (m := count n) (source n)

end Cslib.Crypto
