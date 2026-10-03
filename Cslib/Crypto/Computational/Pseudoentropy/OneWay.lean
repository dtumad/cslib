/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.WordReduction
public import Cslib.Crypto.Computational.OneWay.Normalize
public import Cslib.Computability.Probabilistic.CoinTape

/-!
# The pseudoentropy prediction gap from one-wayness

The executable hashed parity reduction has polynomial loss. One-wayness therefore makes its
inversion term negligible, leaving an inverse-polynomial gap between feasible prediction and
the entropy threshold. Each predictor supplies one inverter with a fixed precision degree;
neither its code nor its choice of saved randomness depends on a nonuniform advice string.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Definition 4 and Section 4, Lemmas 3 and 4.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use the public matrix and dyadic-range variant proved in `HashReduction`. This module
  discharges the inversion hypothesis using uniform strict PPT one-wayness.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open Probability GoldreichLevin Filter

/-- A single cubic precision suffices for all sufficiently large dimensions. -/
theorem precision_three_ge {n : ℕ} (hn : 8 ≤ n) :
    8 * hashCount n ≤ precision 3 n := by
  have hcount := hashCount_le n
  have hsquare : 9 ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by lia) 2
  have hcube := Nat.mul_le_mul_right (n + 1) hsquare
  simp only [precision, pow_succ] at *
  nlinarith

/-- The finite entropy threshold holds eventually against every uniform PPT word predictor.
The image may have any fixed width at each parameter; it need not be a permutation or regular. -/
theorem eventually_prediction_entropy_le {f : Word → Word} (hf : OneWay f)
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ Word)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n)
    (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) :
    ∀ᶠ n in atTop, 2 * winProbability (predictionGame (sample f) adversary n) - 1 ≤
      1 - PMF.conditionalEntropy (joint (count := hashCount n) (finiteFunction n)) -
        1 / (hashCount n : ℝ) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.exists_padded_bool_coin_evaluator
  have hinversion := hf.inversion_negligible _ (wordInverter_isPPT hf.polyTime hefficient c d 3)
  have hloss : Negligible (fun n => 128 * (dyadicSize (16 * hashCount n) : ℝ) ^ 2 *
      winProbability (inversionGame f (wordInverter f evaluate c d 3) n)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      hinversion.polynomiallyBounded_mul
        (show PolynomiallyBounded (fun n => 128 * dyadicSize (16 * hashCount n) ^ 2) by fun_prop)
  have hsmall := hloss.eventually_le_inv_polynomial
    hashCount_polynomiallyBounded (fun n => Nat.pos_of_ne_zero (NeZero.ne (hashCount n)))
  filter_upwards [hsmall, eventually_ge_atTop 8] with n hsmall hn
  have h := word_prediction_entropy_le f (finiteFunction n) (encodeImage n)
    (hencode n) (hlength n) adversary evaluate c d hrealize 3 (precision_three_ge hn)
  have htwo : (2 : ℝ) / hashCount n = 2 * (1 / (hashCount n : ℝ)) := by ring
  rw [htwo] at h
  linarith

/-- A one-way function with a fixed image width at each parameter gives a samplable
pseudoentropy pair. The gap is inverse-linear in the original input length. -/
theorem pair_hasGap {f : Word → Word} (hf : OneWay f)
    {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ Word)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x))
    (imageLength : ℕ → ℕ) (hlength : ∀ n image, (encodeImage n image).length = imageLength n) :
    (pair f hf.polyTime finiteFunction encodeImage hencode).HasGap
      (fun n => 1 / (hashCount n : ℝ)) :=
  eventually_prediction_entropy_le hf finiteFunction encodeImage hencode imageLength hlength

end Cslib.Crypto.Pseudoentropy.HashPair

namespace Cslib.Crypto

open Probability Pseudoentropy

/-- Every one-way word function yields an exactly samplable pseudoentropy pair with an explicit
inverse-polynomial prediction gap. Normalization handles arbitrary original output lengths. -/
theorem OneWay.exists_pseudoentropyPair {f : Word → Word} (hf : OneWay f) :
    ∃ pair : SamplablePair, pair.HasGap (fun n => 1 / (2 * ((n : ℝ) + 7))) := by
  obtain ⟨g, length, hg, hlength, _⟩ := hf.exists_fixedOutputLength
  let finiteFunction (n : ℕ) (x : BitString n) := wordBits (length n) (g (List.ofFn x))
  let encodeImage (n : ℕ) : BitString (length n) ↪ Word :=
    ⟨List.ofFn, fun _ _ h => List.ofFn_inj.mp h⟩
  have hencode (n : ℕ) (x : BitString n) :
      g (List.ofFn x) = encodeImage n (finiteFunction n x) := by
    exact (ofFn_wordBits (by simp [hlength])).symm
  refine ⟨HashPair.pair g hg.polyTime finiteFunction encodeImage hencode,
    (HashPair.pair_hasGap hg finiteFunction encodeImage hencode length
      (fun _ _ => List.length_ofFn)).mono
      (fun n => ?_)⟩
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (HashPair.hashCount n))
  · exact_mod_cast HashPair.hashCount_le n

end Cslib.Crypto
