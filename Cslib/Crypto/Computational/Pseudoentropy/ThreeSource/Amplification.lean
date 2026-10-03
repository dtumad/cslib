/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.ThreeSource.Padding
public import Cslib.Crypto.Computational.Stretch

/-!
# Amplifying the entropy-grid candidates

Each padded candidate is iterated until its output is one bit longer than all the candidates'
independent seeds together. The uniformly randomized stretching reduction preserves the secure
choice, with polynomial loss. This prepares XOR combination without computing that choice.

We follow Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction
for Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability Filter

/-- Amplify one candidate enough to pay for all candidates' independent seeds. -/
def amplifiedGenerate (n sourceBits observationBound densityBound commonBits index : ℕ)
    (evaluate : Word → Word × Bool) (seed : Word) : Word :=
  PRGStretch.iterate
    (paddedGenerate n sourceBits observationBound densityBound commonBits index evaluate)
    commonBits (size sourceBits densityBound * commonBits + 1 - commonBits) seed

/-- The entire amplified family is uniformly efficient, including on malformed seed inputs. -/
theorem amplifiedGenerate_isPolyTime {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBound n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hcommon : IsPolyTime unaryEncoding (fun n => unaryEncoding (common n))) :
    IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      (fun input => amplifiedGenerate input.1.1 (saved.length input.1.1)
        (observationBound input.1.1) (densityBound input.1.1) (common input.1.1) input.1.2
          (saved.evaluate input.1.1) input.2) := by
  have hlength := saved.length_isPolyTime
  unfold amplifiedGenerate
  refine PRGStretch.iterate_isPolyTime ?_ (by polytime) (by polytime) (by polytime)
  have hgenerate := paddedGenerate_isPolyTime saved
    (observationBound := observationBound) (densityBound := densityBound) (common := common)
    hobservation hdensity hcommon
  apply hgenerate.comp_encoded
    (encodeArg := pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
    (f := fun input : ((ℕ × ℕ) × Word) × Word => (input.1.1, input.2))
  polytime

private theorem length_add_count (sourceBits densityBound commonBits : ℕ) :
    commonBits + (size sourceBits densityBound * commonBits + 1 - commonBits) =
      size sourceBits densityBound * commonBits + 1 := by
  have hsize : 0 < size sourceBits densityBound :=
    Nat.mul_pos (by lia) (dyadicSize_pos densityBound)
  have := Nat.le_mul_of_pos_left commonBits hsize
  lia

/-- Every enumerated candidate outputs one more bit than the total seed cost of the grid. -/
theorem length_amplifiedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    (n observationBound densityBound commonBits index : ℕ)
    (hfits : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ observationBound)
    (hcommon : seedLength n (saved.length n) observationBound densityBound index ≤ commonBits)
    {seed : Word} (hseed : seed.length = commonBits) :
    (amplifiedGenerate n (saved.length n) observationBound densityBound commonBits index
      (saved.evaluate n) seed).length = size (saved.length n) densityBound * commonBits + 1 := by
  unfold amplifiedGenerate
  rw [PRGStretch.length_iterate_of_le
    (fun _ hs => length_paddedGenerate saved n _ _ _ _ hfits hcommon hs) _ _ hseed.ge, hseed]
  exact length_add_count ..

/-- Amplification preserves one choice secure against every uniform indexed test. -/
theorem exists_secure_amplified_choice {pair : SamplablePair} {gap : ℕ → ℝ}
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
          (((uniformBits (common n)).map (amplifiedGenerate n (saved.length n)
            (observationBound n) (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformBits (size (saved.length n) (densityBound n) * common n + 1)).bind
            (fun word => ProbComp.eval (test n (choose n) word)))) := by
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_padded_choice hpair saved
      (observationBound := observationBound) (densityBound := densityBound) (common := common)
      hobservation hdensity hcommon hfits hbound hgap
  have hlength := saved.length_isPolyTime
  have hcount : IsPolyTime unaryEncoding (fun n =>
      unaryEncoding (size (saved.length n) (densityBound n) * common n + 1 - common n)) := by
    polytime
  have h := PRGStretch.indexed_indistinguishable (seedBits := common)
    (generator := fun n index => paddedGenerate n (saved.length n) (observationBound n)
      (densityBound n) (common n) index (saved.evaluate n))
    (count := fun n => size (saved.length n) (densityBound n) * common n + 1 - common n)
    (choose := choose)
    (paddedGenerate_isPolyTime saved (observationBound := observationBound)
      (densityBound := densityBound) (common := common) hobservation hdensity hcommon)
    hcommon hcount hsecure
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  unfold amplifiedGenerate
  simpa only [length_add_count] using h test htest

end Cslib.Crypto.Pseudoentropy.EntropyGrid
