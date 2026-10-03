/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GeneratorReindex
public import Cslib.Crypto.Computational.Pseudoentropy.ThreeSource.Combined

/-!
# Pseudorandom generators from pseudoentropy pairs

Realize the pair with a deterministic sampler and saved coins, enumerate the entropy grid,
pad and amplify every candidate, then XOR their outputs. Finally extend the resulting family
to every seed length. The density schedule must resolve the pair's gap; no entropy estimate
or chosen successful candidate is supplied to the generator.

This formalizes Thomas Holenstein, *Pseudorandom Generators from One-Way Functions:
A Simple Construction for Any Hardness*, TCC 2006, Section 5 and the final proof of Theorem 1,
[write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
The matrix extractor used here gives polynomial seed length without claiming the paper's
optimized seed-length exponent.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter

/-- A samplable pseudoentropy pair with an efficiently resolved gap gives a uniform PRG
expanding every seed length by one bit. -/
theorem SamplablePair.HasGap.exists_pseudorandomGenerator {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) {densityBound : ℕ → ℕ}
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ generator : Word → Word, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨saved⟩ := pair.exists_seedRealization
  obtain ⟨bound, hbound, hfits⟩ := pair.exists_observationBound
  obtain ⟨common, hcommon, _, hge, hsize⟩ := EntropyGrid.exists_common_seedLength
    (sourceBits := saved.length) (observationBound := bound) (densityBound := densityBound)
    saved.length_isPolyTime hbound hdensity
  have htotal :=
    (EntropyGrid.size_isPolyTime saved.length_isPolyTime hdensity).unary_mul hcommon
  refine ⟨GeneratorReindex.generate
    (fun n => EntropyGrid.size (saved.length n) (densityBound n) * common n)
    (fun n => EntropyGrid.combinedGenerate n (saved.length n) (bound n) (densityBound n)
      (common n) (saved.evaluate n)), ?_⟩
  refine GeneratorReindex.pseudorandomGenerator htotal ?_ ?_ ?_ ?_
  · intro n
    exact (hge n).trans (Nat.le_mul_of_pos_left _ (EntropyGrid.size_pos ..))
  · exact EntropyGrid.combinedGenerate_isPolyTime saved
      (observationBound := bound) (densityBound := densityBound) (common := common)
      hbound hdensity hcommon
  · intro n seed _
    exact EntropyGrid.length_combinedGenerate ..
  · exact EntropyGrid.combinedGenerate_indistinguishable hpair saved
      (observationBound := bound) (densityBound := densityBound) (common := common)
      hbound hdensity hcommon hfits hsize hgap

end Cslib.Crypto.Pseudoentropy
