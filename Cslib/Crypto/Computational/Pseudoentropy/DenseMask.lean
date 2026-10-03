/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Basic
public import Cslib.Crypto.Computational.Pseudoentropy.SequenceLearner

/-!
# Dense masks against uniform sequence tests

A pseudoentropy pair's prediction bound forces every efficient sequence test to admit a dense
soft mask with small distinguishing gap. Otherwise the concrete sequence learner constructs one
uniform strict PPT predictor violating that bound. The mask's nonzero probabilities have an
explicit inverse-polynomial lower bound, needed for the subsequent extraction estimate.

The density and repetition schedules are efficiently computable. The density need only be valid
and below the entropy threshold at the parameter where the conclusion is used. Neither the
program nor its parameters are chosen separately at each input length.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  We use the clocked soft-mask implementation, with all sampling failures included.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability Boosting Filter

/-- Every uniform sequence test eventually admits a dense soft mask with small distinguishing
gap. The mask may depend on the test and parameter; its positive probabilities are uniformly
bounded below by the configured dyadic rate. The statement exposes no boosting state. -/
theorem HasGap.eventually_exists_mask {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (test : ℕ → List (Word × Bool) → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun input => test input.1 input.2))
    {count numerator densityBound inverseGap : ℕ → ℕ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hnumerator : IsPolyTime unaryEncoding (fun n => unaryEncoding (numerator n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hinverseGap : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseGap n)))
    (hgap : ∀ n, 0 < inverseGap n) :
    ∀ᶠ n in atTop, 0 < numerator n → numerator n ≤ dyadicSize (densityBound n) →
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n →
      ∃ mask : pair.Observation n × Bool → ProbComp Bool,
        (numerator n : ℝ) / dyadicSize (densityBound n) ≤
          winProbability (OracleComp.sample (pair.joint n) >>= mask) ∧
        (∀ value, 0 < winProbability (mask value) →
          1 / (dyadicSize (2 * inverseGap n * dyadicSize (densityBound n)) : ℝ) ≤
            winProbability (mask value)) ∧
        advantage (OracleComp.replicate (count n) (pair.sample n) >>= test n)
          (OracleComp.replicate (count n) (maskedSample (OracleComp.sample (pair.joint n))
            (fun value => pair.encode n value.1) Prod.snd mask) >>= test n) <
              (dyadicSize (count n) : ℝ) / inverseGap n := by
  classical
  let source : ℕ → ProbComp (Word × Bool) := fun n => (fun value : pair.Observation n × Bool =>
    (pair.encode n value.1, value.2)) <$> OracleComp.sample (pair.joint n)
  have hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source := by
    apply pair.efficient.congr
    intro n
    simp only [source, pair.eval_sample, ProbComp.eval_map, ProbComp.eval_sample]
  obtain ⟨sizeCoeff, sizeDegree, hsize⟩ := hsource.length_le
  let width := fun n => sizeCoeff * (n + 1) ^ sizeDegree
  have hwidth : IsPolyTime unaryEncoding (fun n => unaryEncoding (width n)) := by
    unfold width
    polytime
  have hsize' (n : ℕ) (value : pair.Observation n × Bool)
      (hvalue : value ∈ (pair.joint n).support) : (pair.encode n value.1).length ≤ width n := by
    have h := hsize n (pair.encode n value.1, value.2)
      (by simpa only [source, ProbComp.eval_map, ProbComp.eval_sample] using
        (PMF.mem_support_map_iff _ _ _).mpr ⟨value, hvalue, rfl⟩)
    simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply,
      boolEncoding, Function.Embedding.coeFn_mk, List.length_singleton,
      unaryEncoding_apply, List.length_replicate] at h
    dsimp only [width]
    lia
  obtain ⟨c, d, evaluate, hevaluate, hrealize⟩ := SequenceLearner.exists_evaluator htest
  let params := fun n => SequenceLearner.parameters n (numerator n) (densityBound n)
    (inverseGap n) (SavedPrediction.codeBound n (count n) c d (width n) + 1)
  have hcode : IsPolyTime unaryEncoding (fun n =>
      unaryEncoding (SavedPrediction.codeBound n (count n) c d (width n))) := by
    apply SavedPrediction.codeBound_isPolyTime c d <;> polytime
  have hrate : IsPolyTime unaryEncoding (fun n => unaryEncoding (params n).rateBound) := by
    dsimp only [params, SequenceLearner.parameters]
    polytime
  let adversary : Distinguisher := fun n observation =>
    SequenceLearner.predict evaluate (source n) (unaryEncoding n) (count n) c d (width n)
      (inverseGap n) (params n) observation
  have hadversary : IsPPT boolEncoding adversary := by
    change IsPPTOn parameterEncoding boolEncoding _
    exact SequenceLearner.predict_isPPT c d hevaluate
      (hsource.preprocess isPolyTime_security) isPolyTime_security isPolyTime_auxiliaryInput
      (hcount.comp_encoded isPolyTime_security) (hwidth.comp_encoded isPolyTime_security)
      (hinverseGap.comp_encoded isPolyTime_security) isPolyTime_security
      (hnumerator.comp_encoded isPolyTime_security) (hdensity.comp_encoded isPolyTime_security)
      (hrate.comp_encoded isPolyTime_security)
      ((hcode.unary_add (g := fun _ => 1)
        (isPolyTime_const unaryEncoding [true])).comp_encoded isPolyTime_security)
  have hsmall := SequenceLearner.failureBound_eventually_le (params := params)
    (inverseGap := inverseGap) (by change PolynomiallyBounded id; exact .id)
    hdensity.polynomiallyBounded hrate.polynomiallyBounded hinverseGap.polynomiallyBounded
    (fun _ => le_rfl)
  filter_upwards [hsmall, hpair.eventually_error_ge adversary hadversary] with n hsmall hhard
  intro hnum hnumBound hthreshold
  let := Fintype.ofFinite (pair.Observation n)
  have hvalid : (params n).Valid := ⟨hnum, hnumBound⟩
  by_contra hnone
  have hdistinguish (state : State)
      (hdense : (params n).delta ≤ density (pair.joint n) (params n).rate
        (fun value => state.margin (fun code value =>
          signedPredict evaluate code (pair.encode n value.1)) Prod.snd value - state.threshold)) :
      (dyadicSize (count n) : ℝ) / inverseGap n ≤
        advantage (OracleComp.replicate (count n) (source n) >>= test n)
          (OracleComp.replicate (count n) (maskedSample (OracleComp.sample (pair.joint n))
            (fun value => pair.encode n value.1) Prod.snd (fun value =>
              SequenceLearner.mask (signedPredict evaluate) (params n) state
                (pair.encode n value.1, value.2))) >>= test n) := by
    let mask := fun value : pair.Observation n × Bool =>
      SequenceLearner.mask (signedPredict evaluate) (params n) state
        (pair.encode n value.1, value.2)
    have hmass (value) (hpositive : 0 < winProbability (mask value)) :
        1 / (dyadicSize (2 * inverseGap n * dyadicSize (densityBound n)) : ℝ) ≤
          winProbability (mask value) :=
      inv_dyadicSize_le_eval_sampleDyadicCoin (params n).rateBound _ hpositive
    have hdense' : (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        winProbability (OracleComp.sample (pair.joint n) >>= mask) := by
      change (params n).delta ≤ _
      rw [winProbability_sample_bind]
      simpa only [mask, SequenceLearner.mask_probability, density, State.margin, State.votes]
        using hdense
    have hnot := fun h => hnone ⟨mask, hdense', hmass, h⟩
    apply le_of_not_gt
    intro hgap
    apply hnot
    have hsourceEq : ProbComp.eval (source n) = ProbComp.eval (pair.sample n) := by
      simp only [source, ProbComp.eval_map, ProbComp.eval_sample, pair.eval_sample]
    simpa only [advantage, ProbComp.eval_bind,
      ProbComp.eval_replicate_congr hsourceEq (count n)] using hgap
  have hprediction := SequenceLearner.predict_error (OracleComp.sample (pair.joint n))
    (fun value => pair.encode n value.1) Prod.snd evaluate (unaryEncoding n)
    (count n) c d (width n) (inverseGap n) (params n) (test n) hvalid (hgap n)
    (SequenceLearner.parameters_gamma_le _ _ _ _ _ hvalid (hgap n))
    (by simpa only [ProbComp.eval_sample] using hsize' n)
    (by simp only [params, SequenceLearner.parameters, unaryEncoding_apply,
      List.length_replicate, le_refl])
    (fun state value hvalue => hrealize n (OracleComp.sample (pair.joint n))
      (fun value => pair.encode n value.1) Prod.snd (count n) (width n) (params n) state
        (pair.encode n value.1) (hsize' n value (by simpa using hvalue)))
    (by simpa only [source, ProbComp.eval_sample, advantage, Game.advantage, winProbability]
      using hdistinguish)
  have hlaw : ProbComp.eval (predictionGame pair.sample adversary n) =
      ProbComp.eval (do
        let value ← OracleComp.sample (pair.joint n)
        (fun answer => answer == value.2) <$> adversary n (pair.encode n value.1)) := by
    simp only [predictionGame, ProbComp.eval_bind, pair.eval_sample, PMF.bind_map,
      ProbComp.eval_sample, ProbComp.eval_map, ProbComp.eval_pure]
    rfl
  rw [hlaw] at hhard
  change (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤ _ at hhard
  change (params n).delta ≤ _ at hthreshold
  have htolerance : (0 : ℝ) < (params n).predictionInverseTolerance := by
    exact_mod_cast (params n).predictionInverseTolerance_pos
  change (ProbComp.eval (do
    let value ← OracleComp.sample (pair.joint n)
    (fun answer => answer == value.2) <$> adversary n (pair.encode n value.1)) false).toReal ≤
      (params n).delta / 2 - 1 / (params n).predictionInverseTolerance +
        SequenceLearner.failureBound (params n) (inverseGap n) at hprediction
  have hpositive : (0 : ℝ) < 1 / (2 * (params n).predictionInverseTolerance) := by positivity
  have hhalf : (1 : ℝ) / (params n).predictionInverseTolerance =
      2 * (1 / (2 * (params n).predictionInverseTolerance)) := by ring
  linarith

end Cslib.Crypto.Pseudoentropy.SamplablePair
