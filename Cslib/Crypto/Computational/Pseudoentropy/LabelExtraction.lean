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

The theorem retains all observations and the hash seed. `HasGap.extract_indexed_labels` instantiates
a polynomial repetition schedule and proves its error negligible, leaving only the entropy budget
and admissible density conditions. A valid index may be chosen arbitrarily at each parameter;
the efficient reduction handles all indices. The generator must still combine the candidates.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the transition from Game 2 through Game 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use fresh soft masks and the checked strict PPT sequence learner.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability Probability.PMF Filter

/-- Label extraction is computationally uniform along any valid choices from an efficient
polynomial-size family. The choices need not be computable: the reduction handles all indices
uniformly, and only the proof uses the chosen index. Observations and hash seeds stay public. -/
theorem HasGap.indexed_extracted_advantage_negligible {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {Seed Output : ℕ → ℕ → Type} [∀ n i, Fintype (Seed n i)] [∀ n i, Fintype (Output n i)]
    [∀ n i, Nonempty (Output n i)] (seed : ∀ n i, ProbComp (Seed n i))
    (hash : ∀ n i, Seed n i → Word → Output n i)
    (test : ∀ n i, List Word × Seed n i × Output n i → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun input => extractLabels (seed input.1.1 input.1.2) (hash input.1.1 input.1.2)
          input.2 >>= test input.1.1 input.1.2))
    {candidates count densityBound : ℕ → ℕ} {numerator : ℕ → ℕ → ℕ} {slack : ℕ → ℝ}
    (hcandidates : IsPolyTime unaryEncoding (fun n => unaryEncoding (candidates n)))
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hnumerator : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (numerator input.1 input.2)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n i, IsTwoUniversal (ProbComp.eval (seed n i))
      (fun s (bits : BitString (count n)) => hash n i s (List.ofFn bits)))
    (hslack : ∀ n, 0 ≤ slack n)
    (herror : Negligible (fun n =>
      2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
        Real.sqrt (Fintype.card (Output n (choose n)) * (2 * (2 : ℝ) ^
          (-(count n * ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) -
            slack n)))) / 2)) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>=
        fun samples => extractLabels (seed n (choose n)) (hash n (choose n)) samples >>=
          test n (choose n)))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n)) (count n) (seed n (choose n))).bind
          (fun output => ProbComp.eval (test n (choose n) output)))) := by
  classical
  let error := fun n =>
    2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
      Real.sqrt (Fintype.card (Output n (choose n)) * (2 * (2 : ℝ) ^
        (-(count n * ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) - slack n)))) / 2
  let reduced := fun n i samples => extractLabels (seed n i) (hash n i) samples >>= test n i
  apply (Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder _
    tendsto_natCast_atTop_atTop).mpr
  intro degree
  let inverseGap := fun n => dyadicSize (count n) * (n + 1) ^ degree
  have hinverseGap : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseGap n)) := by
    unfold inverseGap
    polytime
  have hgap (n : ℕ) : 0 < inverseGap n := by
    exact Nat.mul_pos (dyadicSize_pos _) (Nat.pow_pos (by lia))
  have hmasks := hpair.eventually_exists_indexed_mask reduced htest hcandidates hcount
    hnumerator hdensity hinverseGap hgap
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
  filter_upwards [hmasks, hmass, hchoose, hvalid,
    (herror degree).eventually_le_const (by norm_num : (0 : ℝ) < 1)] with
    n hmask hmass hindex hn hsmall
  obtain ⟨mask, hdense, hpositive, hdistinguish⟩ := hmask (choose n) hindex hn.1 hn.2.1 hn.2.2
  have hclose := maskedSample_extract (OracleComp.sample (pair.joint n))
    (fun value => pair.encode n value.1) Prod.snd mask (count n) (realization.length n + n + 2)
    (hmass mask (fun value _ => hpositive value)) (seed n (choose n)) (hash n (choose n))
    (hhash n (choose n)) hdense (hslack n)
  have hcompare := extractLabels_sequence_gap (pair.sample n)
    (maskedSample (OracleComp.sample (pair.joint n))
      (fun value => pair.encode n value.1) Prod.snd mask)
    (count n) (seed n (choose n)) (hash n (choose n)) (test n (choose n)) _ hclose
  have htotal : Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>= reduced n (choose n)))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n)) (count n) (seed n (choose n))).bind
          (fun output => ProbComp.eval (test n (choose n) output))) ≤
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

/-- The explicit repetition schedule makes any valid indexed label extractor computationally
uniform. Only the proof uses the chosen indices; the sampler, hash, and test form one uniformly
efficient family. The entropy budget discharges the complete statistical error. -/
theorem HasGap.extract_indexed_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {Seed : ℕ → ℕ → Type} [∀ n i, Fintype (Seed n i)]
    {outputBits : ℕ → ℕ → ℕ} {candidates inverseSlack : ℕ → ℕ}
    (seed : ∀ n i, ProbComp (Seed n i))
    (hash : ∀ n i, Seed n i → Word → BitString (outputBits n i))
    (test : ∀ n i, List Word × Seed n i × BitString (outputBits n i) → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun input => extractLabels (seed input.1.1 input.1.2) (hash input.1.1 input.1.2)
          input.2 >>= test input.1.1 input.1.2))
    (hcandidates : IsPolyTime unaryEncoding (fun n => unaryEncoding (candidates n)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    {numerator : ℕ → ℕ → ℕ} {densityBound : ℕ → ℕ}
    (hnumerator : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (numerator input.1 input.2)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n i, IsTwoUniversal (ProbComp.eval (seed n i))
      (fun s (bits : BitString
        (ExtractionSchedule.count n (realization.length n) (inverseSlack n))) =>
          hash n i s (List.ofFn bits)))
    (hbudget : ∀ᶠ n in atTop,
      outputBits n (choose n) +
        2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n))) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (OracleComp.replicate
        (ExtractionSchedule.count n (realization.length n) (inverseSlack n)) (pair.sample n) >>=
          fun samples => extractLabels (seed n (choose n)) (hash n (choose n)) samples >>=
            test n (choose n)))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        OracleComp.sample (pair.joint n))
          (ExtractionSchedule.count n (realization.length n) (inverseSlack n))
          (seed n (choose n))).bind
            (fun output => ProbComp.eval (test n (choose n) output)))) := by
  apply hpair.indexed_extracted_advantage_negligible realization choose seed hash test htest
    hcandidates
    (ExtractionSchedule.count_isPolyTime (isPolyTime_input unaryEncoding)
      realization.length_isPolyTime hslack) hnumerator hdensity hchoose hvalid hhash
    (slack := fun n => ExtractionSchedule.slack n (realization.length n) (inverseSlack n))
    (fun _ => Nat.cast_nonneg _)
  apply ExtractionSchedule.error_negligible.trans_eventually_abs_le
  filter_upwards [hbudget] with n hn
  change |(_ : ℝ)| ≤ |ExtractionSchedule.error n|
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by unfold ExtractionSchedule.error; positivity)]
  simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using ExtractionSchedule.error_le n (realization.length n) (inverseSlack n)
      (outputBits n (choose n)) ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) hn

end Cslib.Crypto.Pseudoentropy.SamplablePair
