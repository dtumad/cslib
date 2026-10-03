/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Basic
public import Cslib.Computability.Probabilistic.CoinTape
public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.EntropyConcentration

/-!
# Uniform seeds for samplable pseudoentropy pairs

Every strict PPT sampler admits one polynomial-time deterministic evaluator driven by a uniform
polynomial-length seed. `SeedRealization` exposes this algorithm while preserving the pair's exact
finite joint law. Its `output` is the finite mathematical view used for entropy accounting.

The entropy chain rule accounts for every seed bit, including coins unused by the sampler:
`H(observation) + H(bit | observation) + H(seed | observation, bit) = seed length`.
Thus the third source in the later extraction argument retains the unused randomness too.
The seed also bounds the information in a single outcome, giving an explicit exponential
concentration bound for independent repetitions of the pair.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Definition 4 and Section 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  Our checked machine replay supplies the deterministic uniform-seed presentation expected by
  Definition 4. Section 5 provides the entropy accounting for the three-extractor construction.
  The concentration bound is the seed-length variant documented in `EntropyConcentration`.
  These results do not yet establish the PRG construction.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability

/-- A deterministic evaluator of a pair from a uniform seed, with all input bits counted. -/
structure SeedRealization (pair : SamplablePair) where
  /-- The complete number of seed bits at this parameter. -/
  length : ℕ → ℕ
  /-- The seed length is efficiently available in unary. -/
  length_isPolyTime : IsPolyTime unaryEncoding (fun n => unaryEncoding (length n))
  /-- Evaluate the public observation and hidden bit from a saved seed. -/
  evaluate : ℕ → Word → Word × Bool
  /-- Evaluation is one polynomial-time word program, also on malformed seeds. -/
  efficient : IsPolyTime parameterEncoding (fun input =>
    pairEncoding wordEncoding boolEncoding (evaluate input.1 input.2))
  /-- Uniform seeds realize exactly the original finite joint law. -/
  distribution : ∀ n, (uniformBits (length n)).map (evaluate n) =
    (pair.joint n).map (fun output => (pair.encode n output.1, output.2))

/-- A strict PPT sampler supplies an efficient uniform-seed realization with no additional
computability or sampling assumption. -/
theorem exists_seedRealization (pair : SamplablePair) : Nonempty (SeedRealization pair) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := pair.efficient.exists_seeded_evaluator
  refine ⟨{ length := fun n => c * (n + 1) ^ d
            length_isPolyTime := by polytime
            evaluate := evaluate
            efficient := hefficient.comp_encoded
              (isPolyTime_security.pair (left := unaryEncoding) (right := wordEncoding)
                isPolyTime_auxiliaryInput)
            distribution := ?_ }⟩
  intro n
  rw [← pair.eval_sample]
  symm
  simpa only [unaryEncoding_apply, List.length_replicate] using hrealize n

namespace SeedRealization

variable {pair : SamplablePair} (seed : SeedRealization pair)

/-- Every well-formed seed produces an encoded observation and bit in the original finite law. -/
theorem exists_output (n : ℕ) (bits : BitString (seed.length n)) :
    ∃ output : pair.Observation n × Bool,
      (pair.encode n output.1, output.2) = seed.evaluate n (List.ofFn bits) := by
  have hs : seed.evaluate n (List.ofFn bits) ∈
      ((uniformBits (seed.length n)).map (seed.evaluate n)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨List.ofFn bits, mem_support_uniformBits_iff.mpr List.length_ofFn, rfl⟩
  rw [seed.distribution] at hs
  obtain ⟨output, _, houtput⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  exact ⟨output, houtput⟩

/-- The evaluator's finite mathematical output on a well-formed seed. No search over observations
is run: its word representation is exactly the efficient evaluator's output. -/
noncomputable def output (n : ℕ) (bits : BitString (seed.length n)) : pair.Observation n × Bool :=
  (exists_output seed n bits).choose

/-- The finite view preserves the evaluator's complete output, including the hidden bit. -/
theorem encode_output (n : ℕ) (bits : BitString (seed.length n)) :
    (pair.encode n (seed.output n bits).1, (seed.output n bits).2) =
      seed.evaluate n (List.ofFn bits) := (exists_output seed n bits).choose_spec

/-- The uniform finite-seed presentation has the original joint law. -/
theorem output_distribution (n : ℕ) :
    (PMF.uniformOfFintype (BitString (seed.length n))).map (seed.output n) = pair.joint n := by
  apply PMF.map_injective (f := fun output : pair.Observation n × Bool =>
    (pair.encode n output.1, output.2)) (by
      intro a b h
      exact Prod.ext ((pair.encode n).injective (congrArg Prod.fst h))
        (congrArg (fun output : Word × Bool => output.2) h))
  rw [PMF.map_comp]
  simpa only [uniformBits, PMF.map_comp, Function.comp_def, seed.encode_output] using
    seed.distribution n

/-- Every possible output has at least the probability of one complete seed. -/
theorem mass_ge (n : ℕ) (result : pair.Observation n × Bool)
    (hresult : result ∈ (pair.joint n).support) :
    (2 : ℝ) ^ (-(seed.length n : ℝ)) ≤ (pair.joint n result).toReal := by
  rw [← seed.output_distribution] at hresult ⊢
  simpa [BitString, Real.logb_pow] using PMF.uniform_map_mass_ge (seed.output n) result hresult

/-- Independent repetitions concentrate their conditional information around the Shannon
entropy of the pair. The loss accounts for the sampler's full saved seed length. -/
theorem conditionalSurprisal_concentration (n repetitions : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((PMF.pi (fun _ : Fin repetitions => pair.joint n)).toOuterMeasure {outcomes |
      ∑ i, PMF.surprisal (PMF.conditionalSnd (pair.joint n) (outcomes i).1) (outcomes i).2 ≤
        repetitions * PMF.conditionalEntropy (pair.joint n) - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (repetitions * (seed.length n : ℝ) ^ 2)) := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    PMF.pi_sum_conditionalSurprisal_le (fun _ : Fin repetitions => pair.joint n)
      (Nat.cast_nonneg (seed.length n)) (fun _ => seed.mass_ge n) hε

/-- Revealing the observation and hidden bit leaves exactly the remaining seed entropy.
This identity also counts coins that the sampler never inspected. -/
theorem entropy_chain_rule (n : ℕ) :
    PMF.entropy ((pair.joint n).map Prod.fst) + PMF.conditionalEntropy (pair.joint n) +
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (seed.length n))).map
        (fun bits => (seed.output n bits, bits))) = seed.length n := by
  have h := PMF.entropy_chain_rule_deterministic
    (PMF.uniformOfFintype (BitString (seed.length n)))
    (fun bits => (seed.output n bits).1) (fun bits => (seed.output n bits).2)
  have hmarginal : (PMF.uniformOfFintype (BitString (seed.length n))).map
      (fun bits => (seed.output n bits).1) = (pair.joint n).map Prod.fst := by
    rw [← seed.output_distribution, PMF.map_comp]
    rfl
  simpa [hmarginal, seed.output_distribution, PMF.entropy_uniform, BitString, Real.logb_pow] using h

end SeedRealization

end Cslib.Crypto.Pseudoentropy.SamplablePair
