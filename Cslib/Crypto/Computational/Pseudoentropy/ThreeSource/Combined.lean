/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GeneratorXor
public import Cslib.Crypto.Computational.Pseudoentropy.ThreeSource.Amplification

/-!
# Combining the entropy-grid candidates

Run every amplified candidate on a separate seed block and XOR the outputs. The result expands
their total seed length by one bit. The secure choice from the entropy argument proves security;
the program itself never chooses or estimates an entropy.

This completes the indexed construction of Thomas Holenstein, *Pseudorandom Generators from
One-Way Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of
Theorem 1, [write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
The security parameter determines the seed length here. `GeneratorReindex` extends this family
to every input length, and `Pseudoentropy.Generator` assembles the complete theorem.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability Filter

/-- Use one independent seed block per candidate and XOR the amplified outputs. -/
def combinedGenerate (n sourceBits observationBound densityBound commonBits : ℕ)
    (evaluate : Word → Word × Bool) (seed : Word) : Word :=
  GeneratorXor.generate (size sourceBits densityBound) commonBits
    (size sourceBits densityBound * commonBits + 1)
    (fun index => amplifiedGenerate n sourceBits observationBound densityBound commonBits
      index evaluate) seed

/-- The complete grid construction has one uniform polynomial-time implementation. -/
theorem combinedGenerate_isPolyTime {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBound n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hcommon : IsPolyTime unaryEncoding (fun n => unaryEncoding (common n))) :
    IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun input =>
      combinedGenerate input.1 (saved.length input.1) (observationBound input.1)
        (densityBound input.1) (common input.1) (saved.evaluate input.1) input.2) := by
  have hlength := saved.length_isPolyTime
  unfold combinedGenerate
  refine GeneratorXor.generate_isPolyTime (by polytime) (by polytime) (by polytime) ?_ (by polytime)
  have hgenerate := amplifiedGenerate_isPolyTime saved
    (observationBound := observationBound) (densityBound := densityBound) (common := common)
    hobservation hdensity hcommon
  apply hgenerate.comp_encoded
    (encodeArg := pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
    (f := fun input : ((ℕ × Word) × ℕ) × Word => ((input.1.1.1, input.1.2), input.2))
  polytime

/-- The output is one bit longer than the total cost of all the independent seed blocks. -/
theorem length_combinedGenerate (n sourceBits observationBound densityBound commonBits : ℕ)
    (evaluate : Word → Word × Bool) (seed : Word) :
    (combinedGenerate n sourceBits observationBound densityBound commonBits evaluate seed).length =
      size sourceBits densityBound * commonBits + 1 := by
  simp only [combinedGenerate, GeneratorXor.length_generate]

/-- One entropy-valid choice suffices for security of the complete, explicitly computed grid. -/
theorem combinedGenerate_indistinguishable {pair : SamplablePair} {gap : ℕ → ℝ}
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
    ComputationallyIndistinguishable
      (fun n => (uniformBits (size (saved.length n) (densityBound n) * common n)).map
        (combinedGenerate n (saved.length n) (observationBound n) (densityBound n) (common n)
          (saved.evaluate n)))
      (fun n => uniformBits (size (saved.length n) (densityBound n) * common n + 1)) := by
  obtain ⟨choose, hchoose, hsecure⟩ := exists_secure_amplified_choice hpair saved
    (observationBound := observationBound) (densityBound := densityBound) (common := common)
    hobservation hdensity hcommon hfits hbound hgap
  have hlength := saved.length_isPolyTime
  unfold combinedGenerate
  refine GeneratorXor.indistinguishable (choose := choose)
    (count := fun n => size (saved.length n) (densityBound n)) (seedBits := common)
    (outputBits := fun n => size (saved.length n) (densityBound n) * common n + 1)
    (generator := fun n index => amplifiedGenerate n (saved.length n) (observationBound n)
      (densityBound n) (common n) index (saved.evaluate n))
    (by polytime) hcommon (by polytime) ?_ hchoose hsecure
  exact amplifiedGenerate_isPolyTime saved (observationBound := observationBound)
    (densityBound := densityBound) (common := common) hobservation hdensity hcommon

end Cslib.Crypto.Pseudoentropy.EntropyGrid
