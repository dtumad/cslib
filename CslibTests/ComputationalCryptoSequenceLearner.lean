/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.SequenceLearner
public import Cslib.Crypto.Computational.Pseudoentropy.Basic

/-!
# A complete sequence-to-prediction reduction

The public observation reveals its label. A sequence test checks this relation, so masking a
dense set of labels gives a noticeable distinguishing gap. The library builds the saved evaluator
from that test and uses the actual sampled learner in the boosting loop. No learner-correlation
or successful-sign hypothesis is supplied by this example.
-/

public section

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Pseudoentropy
open Cslib.Crypto.Pseudoentropy.Boosting

namespace CslibTests.ComputationalCryptoSequenceLearner

/-- Check whether the first observation's visible bit agrees with its label. -/
noncomputable def visibleTest (_n : ℕ) (samples : List (Word × Bool)) : ProbComp Bool :=
  let sample := samples.headD ([], false)
  pure (sample.1.headD false == sample.2)

theorem visibleTest_isPPT : IsPPTOn (pairEncoding unaryEncoding
    (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
      (fun pair => visibleTest pair.1 pair.2) := by
  have hsample := (isPolyTime_snd unaryEncoding
    (listEncoding (pairEncoding wordEncoding boolEncoding))).list_headD ([], false)
  have hobservation := hsample.fst
  have htruth := hsample.snd
  unfold visibleTest
  exact ((hobservation.headD false).bool₂ htruth (· == ·)).isPPTOn

/-- The source presents a random label together with an observation revealing it. -/
noncomputable def visibleSource : ProbComp (Word × Bool) :=
  (fun bit : Bool => ([bit], bit)) <$> OracleComp.uniform Bool

private theorem one_sample (n : ℕ) (source : ProbComp (Word × Bool)) :
    OracleComp.replicate 1 source >>= visibleTest n =
      source >>= fun sample => pure (sample.1.headD false == sample.2) := by
  simp [OracleComp.replicate_succ, visibleTest]

/-- A label is wrong exactly when masking replaces it by the other fair bit. -/
private theorem masked_correct (weights : Bool → ProbComp Bool) (bit : Bool) :
    winProbability (maskBit (weights bit) bit >>= fun answer => pure (bit == answer)) =
      1 - winProbability (weights bit) / 2 := by
  have hmap (p : PMF Bool) : p.map (fun answer => bit == answer) true = p bit := by
    cases bit <;> simp [PMF.map_apply]
  simp only [winProbability, Game.winProbability, ProbComp.eval_bind, ProbComp.eval_pure]
  change ((ProbComp.eval (maskBit (weights bit) bit)).map (fun answer => bit == answer)
    true).toReal = _
  rw [hmap, eval_maskBit_apply]
  simp only [ite_true]

/-- The test's exact distinguishing gap is half the soft-mask density. -/
private theorem visible_gap (n : ℕ) (weights : Bool → ProbComp Bool) :
    winProbability (OracleComp.replicate 1 visibleSource >>= visibleTest n) -
      winProbability (OracleComp.replicate 1
        (maskedSample (OracleComp.uniform Bool) (fun bit => [bit]) id weights) >>=
          visibleTest n) =
      (∑ bit, (ProbComp.eval (OracleComp.uniform Bool) bit).toReal *
        winProbability (weights bit)) / 2 := by
  rw [one_sample, one_sample]
  simp only [visibleSource, maskedSample, bind_assoc, bind_map_left, List.headD_cons, id_eq]
  rw [winProbability_bind, winProbability_bind]
  simp_rw [masked_correct]
  simp [winProbability, Game.winProbability, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The rate meets the learner's `1/16` correlation, and the bound includes its orientation bit. -/
def parameters (c d n : ℕ) : Parameters :=
  ⟨n, 1, 0, 16, SavedPrediction.codeBound (unaryEncoding n).length 1 c d 1 + 1⟩

/-- The source, saved descriptions, learning, boosting, and final prediction form one program. -/
noncomputable def visiblePredictor (c d : ℕ) (evaluate : Word → Word → Bool)
    (n : ℕ) (observation : Word) : ProbComp Bool :=
  SequenceLearner.predict evaluate visibleSource (unaryEncoding n) 1 c d 1 8
    (parameters c d n) observation

theorem visiblePredictor_isPPT (c d : ℕ) {evaluate : Word → Word → Bool}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2])) :
    IsPPT boolEncoding (visiblePredictor c d evaluate) := by
  have hbound : IsPolyTime parameterEncoding (fun pair =>
      unaryEncoding (SavedPrediction.codeBound pair.1 1 c d 1)) := by
    apply SavedPrediction.codeBound_isPolyTime c d <;> polytime
  unfold visiblePredictor
  change IsPPTOn parameterEncoding boolEncoding _
  apply SequenceLearner.predict_isPPT c d hevaluate
  all_goals try dsimp only [visibleSource, parameters]
  all_goals try simp only [unaryEncoding, Function.Embedding.coeFn_mk, List.length_replicate]
  all_goals ppt

private theorem parameters_bounds (c d n : ℕ) :
    (parameters c d n).Valid ∧ (parameters c d n).gamma ≤ (1 : ℝ) / (2 * 8) ∧
      (parameters c d n).delta = (1 : ℝ) / 2 ∧
        (parameters c d n).predictionInverseTolerance = 16384 := by
  have hlog : Nat.log 2 16 = 4 := by decide +kernel
  norm_num [parameters, Parameters.Valid, Parameters.gamma, Parameters.rate, Parameters.delta,
    Parameters.predictionInverseTolerance, Parameters.inverseRate, Parameters.denominator,
    dyadicSize, hlog]

private theorem eval_visible_prediction (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (predictionGame (fun _ => visibleSource) adversary n) =
      ProbComp.eval (do
        let bit ← OracleComp.uniform Bool
        (fun answer => answer == bit) <$> adversary n [bit]) := by
  simp only [predictionGame, visibleSource, bind_map_left, bind_pure_comp]

private theorem predictionGame_at (adversary : Distinguisher) (n : ℕ) :
    predictionGame (fun _ => visibleSource) adversary n =
      predictionGame (fun _ => visibleSource) (fun _ => adversary n) n := rfl

private theorem visible_prediction_error (c d n : ℕ) (evaluate : Word → Word → Bool)
    (params : Parameters) (hvalid : params.Valid) (hgamma : params.gamma ≤ (1 : ℝ) / (2 * 8))
    (hdelta : params.delta = (1 : ℝ) / 2)
    (hbound : SavedPrediction.codeBound (unaryEncoding n).length 1 c d 1 + 1 ≤ params.codeBound)
    (hrealize : ∀ state bit,
      ProbComp.eval ((fun code => evaluate code [bit]) <$>
        SequenceLearner.candidates (signedPredict evaluate) visibleSource
          (unaryEncoding n) 1 c d 1 params state) =
        ProbComp.eval (maskedSequencePredictor (OracleComp.uniform Bool) (fun bit => [bit]) id
          (fun bit => SequenceLearner.mask (signedPredict evaluate) params state ([bit], bit))
          1 (visibleTest n) [bit])) :
    (ProbComp.eval (predictionGame (fun _ => visibleSource)
      (fun _ observation => SequenceLearner.predict evaluate visibleSource
        (unaryEncoding n) 1 c d 1 8 params observation) n) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        SequenceLearner.failureBound params 8 := by
  have h := SequenceLearner.predict_error (OracleComp.uniform Bool) (fun bit => [bit]) id
    evaluate (unaryEncoding n) 1 c d 1 8 params (visibleTest n)
    hvalid (by decide) hgamma (by intro bit _; simp) hbound
    (fun state bit _ => by simpa only [visibleSource, id_eq] using hrealize state bit) (by
      intro state hdense
      let weights := fun bit =>
        SequenceLearner.mask (signedPredict evaluate) params state ([bit], bit)
      have hweight : params.delta ≤
          ∑ bit, (ProbComp.eval (OracleComp.uniform Bool) bit).toReal *
            winProbability (weights bit) := by
        simpa only [weights, SequenceLearner.mask_probability, density, State.margin, State.votes,
          id_eq] using hdense
      have hgap := visible_gap n weights
      simp only [visibleSource] at hgap
      simp only [id_eq]
      rw [hgap]
      have hhalf := div_le_div_of_nonneg_right hweight (by norm_num : (0 : ℝ) ≤ 2)
      rw [hdelta] at hhalf
      exact (by norm_num [dyadicSize] : (dyadicSize 1 : ℝ) / 8 ≤ (1 / 2) / 2).trans
        (hhalf.trans (le_abs_self _)))
  rw [eval_visible_prediction]
  simpa only [id_eq, visibleSource] using h

open Filter in
/-- A certified distinguisher constructs one strict PPT predictor with a proved advantage.
The exact saved evaluator, orientation, learner, and final model are all chosen by the reduction. -/
theorem exists_predictor_from_test :
    ∃ adversary : Distinguisher, IsPPT boolEncoding adversary ∧
      ∀ᶠ n in atTop,
        (ProbComp.eval (predictionGame (fun _ => visibleSource) adversary n) false).toReal ≤
          (1 : ℝ) / 4 - 1 / 32768 := by
  obtain ⟨c, d, evaluate, hevaluate, hrealize⟩ :=
    SequenceLearner.exists_evaluator visibleTest_isPPT
  refine ⟨visiblePredictor c d evaluate, visiblePredictor_isPPT c d hevaluate, ?_⟩
  have hfailure := SequenceLearner.failureBound_eventually_le
    (params := parameters c d) (inverseGap := fun _ => 8)
    (by simpa only [parameters] using PolynomiallyBounded.id)
    (by dsimp only [parameters]; fun_prop) (by dsimp only [parameters]; fun_prop)
    (by fun_prop) (fun _ => le_rfl)
  filter_upwards [hfailure] with n hn
  obtain ⟨hvalid, hgamma, hdelta, htolerance⟩ := parameters_bounds c d n
  have h := visible_prediction_error c d n evaluate (parameters c d n) hvalid hgamma hdelta le_rfl
    (fun state bit => by
      simpa only [visibleSource, id_eq] using hrealize n (OracleComp.uniform Bool)
        (fun bit => [bit]) id 1 1 (parameters c d n) state [bit] (by simp))
  rw [hdelta, htolerance] at h
  rw [htolerance] at hn
  have hbound := h.trans (show (1 : ℝ) / 2 / 2 - 1 / 16384 +
      SequenceLearner.failureBound (parameters c d n) 8 ≤ 1 / 4 - 1 / 32768 by linarith)
  rw [predictionGame_at]
  have hpredictor : visiblePredictor c d evaluate n = fun observation =>
      SequenceLearner.predict evaluate visibleSource (unaryEncoding n) 1 c d 1 8
        (parameters c d n) observation := rfl
  rw [hpredictor]
  exact hbound

end CslibTests.ComputationalCryptoSequenceLearner
