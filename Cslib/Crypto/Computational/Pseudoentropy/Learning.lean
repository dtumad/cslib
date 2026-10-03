/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Masking
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Learner

/-!
# From sequence distinguishers to a learned predictor

Saved coordinate predictors turn a sequence distinguishing gap into the average bias of a
weighted validation trial. The explicit learner then samples descriptions, chooses an orientation,
and estimates their validation rates. Its output has positive weighted correlation with high
probability. All target predictions receive only the public observation.

The replay hypothesis is supplied by `SavedPrediction.exists_evaluator`; the masked-source
extraction argument must still supply the distinguishing gap for each dense boosting measure.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  This combines the fresh-mask adaptation with explicit sampling and empirical selection.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Cslib.Probability Boosting

variable {α β : Type}

/-- The complete sequence gap is the dyadic coordinate count times the average weighted
validation bias of saved descriptions. The replay law is needed only at actual observations. -/
theorem maskedSequence_validation_gap [Finite α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (test : List (β × Bool) → ProbComp Bool)
    (candidates : ProbComp Word) (predict : Word → β → Bool)
    (hrealize : ∀ value,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval
          (maskedSequencePredictor source observe truth mask count test (observe value))) :
    winProbability (OracleComp.replicate count ((fun value => (observe value, truth value)) <$>
      source) >>= test) -
        winProbability
          (OracleComp.replicate count (maskedSample source observe truth mask) >>= test) =
      (dyadicSize count : ℝ) * (winProbability (candidates >>= fun code =>
        weightedTrial source mask
          (fun value => pure (predict code (observe value) == truth value))) - 1 / 2) := by
  let := Fintype.ofFinite α
  have hpoint (value : α) :
      winProbability
        (candidates >>= fun code => pure (predict code (observe value) == truth value)) =
        winProbability ((fun guess => guess == truth value) <$>
          maskedSequencePredictor source observe truth mask count test (observe value)) := by
    apply congrArg Game.winProbability
    have h := congrArg (PMF.map (fun guess => guess == truth value)) (hrealize value)
    simpa only [bind_pure_comp, ProbComp.eval_map, PMF.map_comp, Function.comp_def] using h
  have hvalidation : winProbability (candidates >>= fun code => weightedTrial source mask
      (fun value => pure (predict code (observe value) == truth value))) =
      winProbability (weightedTrial source mask (fun value =>
        candidates >>= fun code => pure (predict code (observe value) == truth value))) :=
    congrArg Game.winProbability (eval_weightedTrial_bind candidates source mask _)
  rw [maskedSequence_prediction_gap, hvalidation, weightedTrial_probability]
  simp_rw [hpoint]
  simp only [winProbability, Game.winProbability, mul_assoc, add_sub_cancel_left]

/-- A noticeable sequence gap of either sign gives an explicitly sampled predictor with
positive weighted correlation. Its failure probability includes discovery and estimation. -/
theorem maskedSequence_learn_error_pow [Fintype α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (test : List (β × Bool) → ProbComp Bool)
    (candidates : ProbComp Word) (predict : Word → β → Bool)
    (hrealize : ∀ value,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval
          (maskedSequencePredictor source observe truth mask count test (observe value)))
    (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap ≤
      |winProbability (OracleComp.replicate count ((fun value => (observe value, truth value)) <$>
        source) >>= test) -
          winProbability (OracleComp.replicate count (maskedSample source observe truth mask) >>=
            test)|) :
    ((ProbComp.eval (learn candidates (fun code => weightedTrial source mask
      (fun value => pure (predict code (observe value) == truth value)))
        confidence inverseGap)).toOuterMeasure
      {code | ¬ 1 / (2 * inverseGap) ≤ ∑ value, (ProbComp.eval source value).toReal *
        (winProbability (mask value) * signedVote (signedPredict predict code (observe value))
          (truth value))}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  apply learn_correlation_error_pow candidates source mask
    (fun code value => predict code (observe value)) truth confidence inverseGap hgap
  have hcount : (0 : ℝ) < dyadicSize count := by exact_mod_cast dyadicSize_pos count
  rw [maskedSequence_validation_gap source observe truth mask count test candidates predict
      hrealize,
    abs_mul, abs_of_pos hcount] at hdistinguish
  have hfactor : (dyadicSize count : ℝ) / inverseGap =
      dyadicSize count * (1 / inverseGap : ℝ) := by ring
  rw [hfactor] at hdistinguish
  nlinarith

end Cslib.Crypto.Pseudoentropy
