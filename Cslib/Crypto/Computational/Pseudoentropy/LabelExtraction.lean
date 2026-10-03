/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.DenseMask
public import Cslib.Crypto.Computational.Pseudoentropy.MaskedExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.Seed
public import Cslib.Crypto.Computational.Pseudoentropy.ExtractionSchedule

/-!
# Computational extraction of a pseudoentropy pair's labels

The dense-mask theorem supplies a comparison experiment for each efficient sequence test.
Extraction makes that experiment statistically uniform. Its information budget is the sampler's
seed length plus `n + 2`, independently of the test's polynomial running-time degree.

The theorem retains all observations and the hash seed. `HasGap.extract_labels` instantiates a
polynomial repetition schedule and proves its error negligible, leaving only the entropy budget
and admissible density conditions. The later generator construction must remove unknown entropies.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the transition from Game 2 through Game 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use fresh soft masks and the checked strict PPT sequence learner.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability Probability.PMF Filter

/-- Hashing repeated labels is computationally uniform whenever the extraction schedule stays
below an admissible density and its explicit statistical error is negligible. The test's complete
sampling and hashing reduction must be strict PPT; observations and the hash seed stay public. -/
theorem HasGap.extracted_advantage_negligible {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization)
    {Seed Output : ℕ → Type} [∀ n, Fintype (Seed n)] [∀ n, Fintype (Output n)]
    [∀ n, Nonempty (Output n)] (seed : ∀ n, ProbComp (Seed n))
    (hash : ∀ n, Seed n → Word → Output n)
    (test : ∀ n, List Word × Seed n × Output n → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun input => extractLabels (seed input.1) (hash input.1) input.2 >>= test input.1))
    {count numerator densityBound : ℕ → ℕ} {slack : ℕ → ℝ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hnumerator : IsPolyTime unaryEncoding (fun n => unaryEncoding (numerator n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (seed n))
      (fun s (bits : BitString (count n)) => hash n s (List.ofFn bits)))
    (hslack : ∀ n, 0 ≤ slack n)
    (herror : Negligible (fun n =>
      2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
        Real.sqrt (Fintype.card (Output n) * (2 * (2 : ℝ) ^
          (-(count n * ((numerator n : ℝ) / dyadicSize (densityBound n)) - slack n)))) / 2)) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>=
        fun samples => extractLabels (seed n) (hash n) samples >>= test n))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n)) (count n) (seed n)).bind
          (fun output => ProbComp.eval (test n output)))) := by
  classical
  let error := fun n =>
    2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
      Real.sqrt (Fintype.card (Output n) * (2 * (2 : ℝ) ^
        (-(count n * ((numerator n : ℝ) / dyadicSize (densityBound n)) - slack n)))) / 2
  let reduced := fun n samples => extractLabels (seed n) (hash n) samples >>= test n
  apply (Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder _
    tendsto_natCast_atTop_atTop).mpr
  intro degree
  let inverseGap := fun n => dyadicSize (count n) * (n + 1) ^ degree
  have hinverseGap : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseGap n)) := by
    unfold inverseGap
    polytime
  have hgap (n : ℕ) : 0 < inverseGap n := by
    exact Nat.mul_pos (dyadicSize_pos _) (Nat.pow_pos (by lia))
  have hmasks := hpair.eventually_exists_mask reduced htest hcount hnumerator hdensity
    hinverseGap hgap
  have hbound : PolynomiallyBounded
      (fun n => 2 * inverseGap n * dyadicSize (densityBound n)) := by
    have := hinverseGap.polynomiallyBounded
    have := hdensity.polynomiallyBounded
    fun_prop
  have hmass := maskedSample_dyadic_mass_ge_eventually
    (fun n => OracleComp.sample (pair.joint n)) (fun _ => id) (fun _ => Prod.snd)
    realization.length (fun n => 2 * inverseGap n * dyadicSize (densityBound n)) hbound
    (by simpa only [ProbComp.eval_sample] using realization.mass_ge)
  refine ⟨2, Filter.eventually_map.mpr ?_⟩
  filter_upwards [hmasks, hmass, hvalid,
    (herror degree).eventually_le_const (by norm_num : (0 : ℝ) < 1)] with
    n hmask hmass hn hsmall
  obtain ⟨mask, hdense, hpositive, hdistinguish⟩ := hmask hn.1 hn.2.1 hn.2.2
  have hclose := maskedSample_extract (OracleComp.sample (pair.joint n))
    (fun value => pair.encode n value.1) Prod.snd mask (count n) (realization.length n + n + 2)
    (hmass mask (fun value _ => hpositive value)) (seed n) (hash n) (hhash n) hdense (hslack n)
  have hcompare := extractLabels_sequence_gap (pair.sample n)
    (maskedSample (OracleComp.sample (pair.joint n))
      (fun value => pair.encode n value.1) Prod.snd mask)
    (count n) (seed n) (hash n) (test n) _ hclose
  have htotal : Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>= reduced n))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n)) (count n) (seed n)).bind
          (fun output => ProbComp.eval (test n output))) ≤
        (dyadicSize (count n) : ℝ) / inverseGap n + error n := by
    change _ - error n ≤ _ at hcompare
    exact le_of_lt ((sub_lt_iff_lt_add.mp (hcompare.trans_lt hdistinguish)))
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (Game.advantage_nonneg _ _))]
  have hprecision : (n : ℝ) ^ degree * ((dyadicSize (count n) : ℝ) / inverseGap n) ≤ 1 := by
    have hdyadic : (dyadicSize (count n) : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos _).ne'
    simp only [inverseGap, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      div_mul_eq_div_div, div_self hdyadic, mul_one_div]
    apply (div_le_one (by positivity)).mpr
    gcongr
    linarith
  have h := mul_le_mul_of_nonneg_left htotal (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) degree)
  dsimp only [error, reduced] at h
  nlinarith

/-- An explicit polynomial repetition schedule makes extracted labels computationally uniform.
The numerical premise reserves two entropy slacks below the chosen density; their cost per sample
is exactly `1 / (2 * (inverseSlack + 1))`. No comparison source or negligible-error hypothesis is
required. -/
theorem HasGap.extract_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization)
    {Seed : ℕ → Type} [∀ n, Fintype (Seed n)] {outputBits inverseSlack : ℕ → ℕ}
    (seed : ∀ n, ProbComp (Seed n)) (hash : ∀ n, Seed n → Word → BitString (outputBits n))
    (test : ∀ n, List Word × Seed n × BitString (outputBits n) → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun input => extractLabels (seed input.1) (hash input.1) input.2 >>= test input.1))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    {numerator densityBound : ℕ → ℕ}
    (hnumerator : IsPolyTime unaryEncoding (fun n => unaryEncoding (numerator n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (seed n))
      (fun s (bits : BitString
        (ExtractionSchedule.count n (realization.length n) (inverseSlack n))) =>
          hash n s (List.ofFn bits)))
    (hbudget : ∀ᶠ n in atTop,
      outputBits n + 2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n))) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (OracleComp.replicate
        (ExtractionSchedule.count n (realization.length n) (inverseSlack n)) (pair.sample n) >>=
          fun samples => extractLabels (seed n) (hash n) samples >>= test n))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n))
          (ExtractionSchedule.count n (realization.length n) (inverseSlack n)) (seed n)).bind
            (fun output => ProbComp.eval (test n output)))) := by
  apply hpair.extracted_advantage_negligible realization seed hash test htest
    (ExtractionSchedule.count_isPolyTime (isPolyTime_input unaryEncoding)
      realization.length_isPolyTime hslack) hnumerator hdensity hvalid hhash
    (slack := fun n => ExtractionSchedule.slack n (realization.length n) (inverseSlack n))
    (fun _ => Nat.cast_nonneg _)
  apply ExtractionSchedule.error_negligible.trans_eventually_abs_le
  filter_upwards [hbudget] with n hn
  change |(_ : ℝ)| ≤ |ExtractionSchedule.error n|
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by unfold ExtractionSchedule.error; positivity)]
  simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using ExtractionSchedule.error_le n (realization.length n) (inverseSlack n)
      (outputBits n) ((numerator n : ℝ) / dyadicSize (densityBound n)) hn

end Cslib.Crypto.Pseudoentropy.SamplablePair
