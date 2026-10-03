/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GeneratorPadding
public import Cslib.Crypto.Computational.Pseudoentropy.ThreeSource.Candidates

/-!
# A common seed length for the entropy grid

One polynomial bounds the input sizes of all entropy-grid entries. Padding to that common
length gives each candidate exactly one bit of stretch and preserves the secure choice against
uniform indexed tests. The common length is increasing and at least the security parameter plus
one, preparing later reindexing by the actual seed length.

This supplies the common-length candidate family used before amplification and XOR in
Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability Filter

/-- The entire grid fits one efficient increasing seed-length schedule. -/
theorem exists_common_seedLength {sourceBits observationBound densityBound : ℕ → ℕ}
    (hsource : IsPolyTime unaryEncoding (fun n => unaryEncoding (sourceBits n)))
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBound n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n))) :
    ∃ common : ℕ → ℕ, IsPolyTime unaryEncoding (fun n => unaryEncoding (common n)) ∧
      StrictMono common ∧ (∀ n, n + 1 ≤ common n) ∧
      ∀ n index, index < size (sourceBits n) (densityBound n) →
        seedLength n (sourceBits n) (observationBound n) (densityBound n) index ≤ common n := by
  have hsize := (size_isPolyTime hsource hdensity).polynomiallyBounded
  have hseed : IsPolyTime (pairEncoding unaryEncoding unaryEncoding) (fun input =>
      unaryEncoding (seedLength input.1 (sourceBits input.1) (observationBound input.1)
        (densityBound input.1) input.2)) := by
    apply seedLength_isPolyTime <;> polytime
  obtain ⟨c, d, hbound⟩ := hseed.indexed_polynomial_bound
    (f := fun n index => seedLength n (sourceBits n) (observationBound n) (densityBound n) index)
    hsize
  refine ⟨fun n => n + 1 + c * (n + 1) ^ d, by polytime, ?_, fun n => by lia, ?_⟩
  · intro n m hnm
    have hpower := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia : n + 1 ≤ m + 1) d)
    lia
  · intro n index hindex
    exact (hbound n index hindex).trans (by lia)

/-- Normalize every grid entry to a chosen common seed length and one bit of stretch. -/
def paddedGenerate (n sourceBits observationBound densityBound commonBits index : ℕ)
    (evaluate : Word → Word × Bool) (seed : Word) : Word :=
  GeneratorPadding.generate (seedLength n sourceBits observationBound densityBound index) commonBits
    (generate n sourceBits observationBound densityBound index evaluate) seed

/-- The padded family uses the same saved sampler and ordinary word operations. -/
theorem paddedGenerate_isPolyTime {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBound n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hcommon : IsPolyTime unaryEncoding (fun n => unaryEncoding (common n))) :
    IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      (fun input => paddedGenerate input.1.1 (saved.length input.1.1) (observationBound input.1.1)
        (densityBound input.1.1) (common input.1.1) input.1.2
          (saved.evaluate input.1.1) input.2) := by
  have hlength := saved.length_isPolyTime
  have hgenerate := generate_of_realization_isPolyTime saved hobservation hdensity
  have hseed : IsPolyTime (pairEncoding unaryEncoding unaryEncoding) (fun input =>
      unaryEncoding (seedLength input.1 (saved.length input.1) (observationBound input.1)
        (densityBound input.1) input.2)) := by
    apply seedLength_isPolyTime <;> polytime
  unfold paddedGenerate
  refine GeneratorPadding.generate_isPolyTime
    (hseed.comp_encoded (isPolyTime_fst _ wordEncoding))
    (hcommon.comp_encoded (isPolyTime_fst _ wordEncoding).fst) ?_ (isPolyTime_snd _ wordEncoding)
  apply hgenerate.comp_encoded (encodeArg := pairEncoding
    (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
    (f := fun input : ((ℕ × ℕ) × Word) × Word => (input.1.1, input.2))
  polytime

/-- Correctly sized common inputs give exactly one bit of stretch. -/
theorem length_paddedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    (n observationBound densityBound commonBits index : ℕ)
    (hfits : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ observationBound)
    (hcommon : seedLength n (saved.length n) observationBound densityBound index ≤ commonBits)
    {seed : Word} (hseed : seed.length = commonBits) :
    (paddedGenerate n (saved.length n) observationBound densityBound commonBits index
      (saved.evaluate n) seed).length = commonBits + 1 := by
  apply GeneratorPadding.length_generate hcommon _ hseed
  intro seed hseed
  rw [length_generate saved n _ _ _ hfits hseed]
  exact seedLength_lt_outputLength ..

/-- Padding preserves one secure choice against every uniform indexed test. -/
theorem exists_secure_padded_choice {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBound n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hcommon : IsPolyTime unaryEncoding (fun n => unaryEncoding (common n)))
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ observationBound n)
    (hbound : ∀ n index, index < size (saved.length n) (densityBound n) →
      seedLength n (saved.length n) (observationBound n) (densityBound n) index ≤ common n)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ,
      (∀ᶠ n in atTop, choose n < size (saved.length n) (densityBound n)) ∧
      ∀ test : ℕ → ℕ → Word → ProbComp Bool,
        IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
          boolEncoding (fun input => test input.1.1 input.1.2 input.2) →
        Negligible (fun n => Game.advantage
          (((uniformBits (common n)).map (paddedGenerate n (saved.length n) (observationBound n)
            (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformBits (common n + 1)).bind
            (fun word => ProbComp.eval (test n (choose n) word)))) := by
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_choice hpair saved hobservation hdensity hfits hgap
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  have hlength := saved.length_isPolyTime
  have hseed : IsPolyTime (pairEncoding unaryEncoding unaryEncoding) (fun input =>
      unaryEncoding (seedLength input.1 (saved.length input.1) (observationBound input.1)
        (densityBound input.1) input.2)) := by
    apply seedLength_isPolyTime <;> polytime
  let reduction := fun n index => GeneratorPadding.test
    (seedLength n (saved.length n) (observationBound n) (densityBound n) index) (common n)
    (test n index)
  have h := hsecure reduction (GeneratorPadding.test_isPPT
    (seedBits := fun input : ℕ × ℕ => seedLength input.1 (saved.length input.1)
      (observationBound input.1) (densityBound input.1) input.2)
    (commonBits := fun input : ℕ × ℕ => common input.1)
    (adversary := fun input : ℕ × ℕ => test input.1 input.2) hseed
    (hcommon.comp_encoded (isPolyTime_fst unaryEncoding unaryEncoding)) htest)
  apply h.congr'
  filter_upwards [hchoose] with n hn
  exact (GeneratorPadding.advantage_eq _ _ (hbound n (choose n) hn)
    (seedLength_lt_outputLength n (saved.length n) (observationBound n) (densityBound n)
      (choose n))).symm

end Cslib.Crypto.Pseudoentropy.EntropyGrid
