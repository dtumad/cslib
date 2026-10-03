/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.OneWay
public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Tactic.PPT

/-!
# Normalizing the output length of a one-way function

A self-delimiting image followed by padding has a length determined solely by the input length.
Equality of padded images implies equality of the original images, even if an inverter returns a
candidate of a different length. A uniform PPT reduction therefore preserves one-wayness.

This removes an interface mismatch with fixed-width presentations of OWF-to-PRG. It does not make
an arbitrary one-way function length-preserving, injective, or regular.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Definition 1 and Section 4.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  The write-up starts with `f : {0,1}ⁿ → {0,1}ᵐ`. This module supplies a uniform reduction from
  our general word-function definition to that fixed-output-length setting, using CSLib's
  existing self-delimiting pair encoding.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

namespace OneWayNormalization

/-- Normalize a word function using a polynomial-time bound supplied in unary. -/
def normalize (f : Word → Word) (bound : ℕ → ℕ) (input : Word) : Word :=
  padWord (bound input.length) (f input)

/-- Output normalization preserves deterministic polynomial time. -/
theorem normalize_isPolyTime {f : Word → Word} (hf : IsPolyTime wordEncoding f)
    {bound : ℕ → ℕ} (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n))) :
    IsPolyTime wordEncoding (normalize f bound) := by
  unfold normalize
  polytime

/-- Any inverter for the normalized function gives an inverter for the original function.
The only preparation is padding its challenge; the candidate is returned unchanged. -/
theorem inversion_le (f : Word → Word) (bound : ℕ → ℕ) (adversary : Inverter) (n : ℕ) :
    winProbability (inversionGame (normalize f bound) adversary n) ≤
      winProbability (inversionGame f
        (fun n image => adversary n (padWord (bound n) image)) n) := by
  unfold inversionGame
  apply winProbability_bind_mono
  intro input hinput
  have hlen : input.length = n := length_of_mem_support_uniformBits
    (by simpa only [ProbComp.eval_sample] using hinput)
  simp only [normalize, hlen]
  apply winProbability_bind_mono
  intro candidate _
  apply winProbability_pure_mono
  intro h
  exact beq_iff_eq.mpr (word_eq_of_padWord_eq (beq_iff_eq.mp h))

end OneWayNormalization

/-- Fixed-length output padding preserves one-wayness against uniform PPT inverters. -/
theorem OneWay.normalize {f : Word → Word} (hf : OneWay f) (bound : ℕ → ℕ)
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n))) :
    OneWay (OneWayNormalization.normalize f bound) := by
  apply OneWay.of_inversion_negligible (OneWayNormalization.normalize_isPolyTime hf.polyTime hbound)
  intro adversary hPPT
  have hreduce : IsPPT wordEncoding (fun n image =>
      adversary n (padWord (bound n) image)) := by ppt
  exact negligible_of_le (hf.inversion_negligible _ hreduce)
    (fun _ => winProbability_nonneg _) (OneWayNormalization.inversion_le f bound adversary)

/-- Every general word OWF yields an OWF whose output length depends only on the input length.
Both evaluation and the output-length function are uniformly polynomial time. -/
theorem OneWay.exists_fixedOutputLength {f : Word → Word} (hf : OneWay f) :
    ∃ (g : Word → Word) (length : ℕ → ℕ), OneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      IsPolyTime unaryEncoding (fun n => unaryEncoding (length n)) := by
  obtain ⟨c, d, hsize⟩ := hf.polyTime.length_le
  let bound (n : ℕ) := c * (n + 1) ^ d
  have hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)) := by
    unfold bound
    polytime
  refine ⟨OneWayNormalization.normalize f bound, fun n => 2 * bound n + 1,
    hf.normalize bound hbound, ?_, by polytime⟩
  intro input
  exact length_padWord (hsize input)

end Cslib.Crypto
