/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Selection

/-!
# Training and evaluating a boosted predictor

`train` runs the clocked loop and selects the final slope. Its result is the stored state paired
with a natural numerator. `predict` uses only this description and the public observation;
training labels are never supplied at prediction time.

The correctness bound adds the loop's guard and learner failures to the final selection failure.
The learner's correlation contract remains an explicit hypothesis. The efficiency certificates
compose the existing programming rules, independently of these probabilistic guarantees.

## References

* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
  Lemma 2.4 and Claims 2.15–2.16. [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  As in `Selection`, the final predictor uses empirical selection over a finite slope grid.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability

/-- Keep a stopped majority predictor, or select a slope from fresh labeled samples. -/
noncomputable def finish (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (params : Parameters) (state : State) : ProbComp (State × ℕ) :=
  if state.stopped then pure (state, 0)
  else (fun slope => (state, slope)) <$> selectSlope params.confidence
    params.predictionInverseTolerance params.predictionGridBound (withVotes evaluate source state)

/-- Train one predictor description using the clocked loop and uniform final selection. -/
noncomputable def train (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (params : Parameters) : ProbComp (State × ℕ) := do
  let state ← run evaluate source learn params
  finish evaluate source params state

/-- Evaluate a learned description on public information alone. The numerator is unused when
the majority stopping test succeeded. -/
noncomputable def predict (evaluate : Word → Word → Bool) (precision : ℕ)
    (model : State × ℕ) (observation : Word) : ProbComp Bool :=
  if model.1.stopped then pure (majority (model.1.votes evaluate observation))
  else clippedPredict precision model.2 (model.1.votes evaluate observation)

section Efficiency

variable {α : Type} {input : α ↪ Word} {evaluate : Word → Word → Bool}

/-- Final selection composes the evaluator, training source, stored state, and unary parameters. -/
theorem finish_isPPT {source : α → ProbComp (Word × Bool)} {params : α → Parameters}
    {state : α → State}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hstate : IsPolyTime input (fun a => State.encoding (state a)))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (htolerance : IsPolyTime input (fun a => unaryEncoding (params a).predictionInverseTolerance))
    (hprecision : IsPolyTime input (fun a => unaryEncoding (params a).predictionGridBound)) :
    IsPPTOn input (pairEncoding State.encoding unaryEncoding)
      (fun a => finish evaluate (source a) (params a) (state a)) := by
  have hselect := selectSlope_isPPT hconfidence htolerance hprecision
    (withVotes_isPPT hevaluate hsource hstate)
  unfold finish
  apply IsPPTOn.cond (State.stopped_isPolyTime hstate)
  · ppt
  · exact hselect.pair hstate

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptFinish : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``finish, ``finish_isPPT)]

/-- Training is strict PPT on every execution, including guard and learner failures. -/
theorem train_isPPT {source : α → ProbComp (Word × Bool)}
    {learn : α → State → ProbComp Word} {params : α → Parameters}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hlearn : IsPPTOn (pairEncoding input State.encoding) wordEncoding
      (fun pair => learn pair.1 pair.2))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (hdensityNum : IsPolyTime input (fun a => unaryEncoding (params a).densityNumerator))
    (hdensityBound : IsPolyTime input (fun a => unaryEncoding (params a).densityBound))
    (hrateBound : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hcodeBound : IsPolyTime input (fun a => unaryEncoding (params a).codeBound)) :
    IsPPTOn input (pairEncoding State.encoding unaryEncoding)
      (fun a => train evaluate (source a) (learn a) (params a)) := by
  have hrun := run_isPPT hevaluate hsource hlearn hconfidence hdensityNum hdensityBound
    hrateBound hcodeBound
  have htolerance : IsPolyTime input (fun a =>
      unaryEncoding (params a).predictionInverseTolerance) := by
    unfold Parameters.predictionInverseTolerance Parameters.inverseRate Parameters.denominator
    polytime
  have hprecision : IsPolyTime input (fun a =>
      unaryEncoding (params a).predictionGridBound) := by
    unfold Parameters.predictionGridBound Parameters.clock Parameters.inverseRate
      Parameters.denominator
    polytime
  unfold train
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptTrain : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``train, ``train_isPPT)]

/-- Applying a trained predictor requires only efficient observations and the stored description. -/
theorem predict_isPPT {precision : α → ℕ} {model : α → State × ℕ} {observation : α → Word}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hprecision : IsPolyTime input (fun a => unaryEncoding (precision a)))
    (hmodel : IsPolyTime input (fun a => pairEncoding State.encoding unaryEncoding (model a)))
    (hobservation : IsPolyTime input observation) :
    IsPPTOn input boolEncoding
      (fun a => predict evaluate (precision a) (model a) (observation a)) := by
  have hstopped := State.stopped_isPolyTime hmodel.fst
  have hvotes := State.votes_isPolyTime hevaluate hmodel.fst hobservation
  have hslope := hmodel.snd
  unfold predict
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptPredict : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``predict, ``predict_isPPT)]

end Efficiency

/-- Prediction error on a source. This semantic definition also permits infinite source types. -/
noncomputable def predictionError {α : Type*} (source : PMF α) (observe : α → Word)
    (truth : α → Bool) (evaluate : Word → Word → Bool) (precision : ℕ) (model : State × ℕ) : ℝ :=
  (source.bind (fun x => (ProbComp.eval (predict evaluate precision model (observe x))).map
    (fun answer => answer == truth x)) false).toReal

/-- A stopped model has exactly its deterministic majority error. -/
theorem predictionError_stopped {α : Type*} (source : PMF α) (observe : α → Word)
    (truth : α → Bool) (evaluate : Word → Word → Bool) (precision : ℕ) (model : State × ℕ)
    (hstopped : model.1.stopped = true) :
    predictionError source observe truth evaluate precision model =
      (source.toOuterMeasure
        {x | majority (model.1.votes evaluate (observe x)) ≠ truth x}).toReal := by
  simp only [predictionError, predict, hstopped, ite_true, ProbComp.eval_pure, PMF.pure_map]
  change ((source.map (fun x => majority (model.1.votes evaluate (observe x)) == truth x))
    false).toReal = _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 2
  ext x
  simp

section Correctness

variable {α : Type} [Fintype α]

/-- An active model has exactly the clipped error used by the slope-selection theorem. -/
theorem predictionError_active (source : PMF α) (observe : α → Word) (truth : α → Bool)
    (evaluate : Word → Word → Bool) (precision : ℕ) (model : State × ℕ)
    (hactive : model.1.stopped = false) :
    predictionError source observe truth evaluate precision model =
      clippedError source (model.1.margin (fun code x => evaluate code (observe x)) truth)
        (model.2 / dyadicSize precision) := by
  have hwrong (p : PMF Bool) (truth : Bool) :
      p.map (fun answer => answer == truth) false = p (!truth) := by
    cases truth <;> simp [PMF.map_apply]
  simp only [predictionError, predict, hactive, Bool.false_eq_true, ite_false,
    Cslib.Probability.PMF.bind_apply_toReal, hwrong, eval_clippedPredict_wrong,
    clippedError, State.margin, State.votes]

variable (source : ProbComp α) (observe : α → Word) (truth : α → Bool)
  (evaluate : Word → Word → Bool) (learn : State → ProbComp Word) (params : Parameters)

/-- Either stopping branch gives the same prediction advantage, except for final slope selection. -/
theorem finish_sound (hparams : params.Valid) {state : State}
    (hstate : State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state)
    (hbounded : state.Bounded params.clock params.codeBound) :
    ((ProbComp.eval (finish evaluate ((fun x => (observe x, truth x)) <$> source)
      params state)).toOuterMeasure {model | ¬ predictionError (ProbComp.eval source) observe
        truth evaluate params.predictionGridBound model ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance}).toReal ≤
      (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  cases hstopped : state.stopped
  · have h := hstate.selectSlope_advantage hparams hbounded hstopped params.confidence
    have herr (slope : ℕ) := predictionError_active (ProbComp.eval source) observe truth
      evaluate params.predictionGridBound (state, slope) hstopped
    simpa only [finish, hstopped, Bool.false_eq_true, ite_false, ProbComp.eval_map,
      PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, herr] using h
  · have hgood : predictionError (ProbComp.eval source) observe truth evaluate
        params.predictionGridBound (state, 0) ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance := by
      rw [predictionError_stopped _ _ _ _ _ _ hstopped]
      apply le_trans _ hparams.majority_error_le
      simpa only [State.Successful, hstopped, ite_true, State.votes] using hstate
    simp only [finish, hstopped, ite_true, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
      Set.mem_ofPred_eq, hgood, not_true_eq_false, ite_false, ENNReal.toReal_zero]
    positivity

variable (hparams : params.Valid) {error : ℝ} (herror : 0 ≤ error)
  (hlearn : ∀ state : State,
    params.delta ≤ density (ProbComp.eval source) params.rate
      (fun x => state.margin (fun code x => evaluate code (observe x)) truth x - state.threshold) →
    ((ProbComp.eval (learn state)).toOuterMeasure
      {code | ¬ State.GoodPredictor (ProbComp.eval source)
        (fun code x => evaluate code (observe x)) truth params state code}).toReal ≤ error)

include hparams herror hlearn

/-- The complete training algorithm has one failure bound for guards, learners, and selection.
All obligations refer to the supplied source and the descriptions actually stored by the loop. -/
theorem train_sound :
    ((ProbComp.eval (train evaluate ((fun x => (observe x, truth x)) <$> source)
      learn params)).toOuterMeasure {model | ¬ predictionError (ProbComp.eval source) observe
        truth evaluate params.predictionGridBound model ≤
          params.delta / 2 - 1 / params.predictionInverseTolerance}).toReal ≤
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) +
        (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  rw [train, ProbComp.eval_bind]
  refine (PMF.toOuterMeasure_bind_failure_toReal_le _ _
    {state | State.Successful (ProbComp.eval source)
      (fun code x => evaluate code (observe x)) truth params state} _ (by positivity)
    (fun state hsupport hstate => finish_sound source observe truth evaluate params hparams hstate
      (run_bounded evaluate _ learn params state hsupport))).trans ?_
  exact add_le_add
    (run_sound source observe truth evaluate learn params hparams herror hlearn) le_rfl

/-- Averaging over training gives an unconditional prediction-error bound. Training is
independent of the challenge, and only its public observation reaches the trained predictor. -/
theorem train_predict_error :
    (ProbComp.eval (do
      let x ← source
      let model ← train evaluate ((fun x => (observe x, truth x)) <$> source) learn params
      (fun answer => answer == truth x) <$>
        predict evaluate params.predictionGridBound model (observe x)) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence + error) +
        (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence := by
  let training := train evaluate ((fun x => (observe x, truth x)) <$> source) learn params
  let test := fun model => (ProbComp.eval source).bind (fun x =>
    (ProbComp.eval (predict evaluate params.predictionGridBound model (observe x))).map
      (fun answer => answer == truth x))
  have hdelta := hparams.delta_pos
  have hthreshold : 0 ≤ params.delta / 2 - 1 / params.predictionInverseTolerance :=
    (by positivity : 0 ≤ 7 * params.delta / 16).trans hparams.majority_error_le
  have h := PMF.toOuterMeasure_bind_failure_toReal_le (ProbComp.eval training) test
    {model | predictionError (ProbComp.eval source) observe truth evaluate
      params.predictionGridBound model ≤ params.delta / 2 - 1 / params.predictionInverseTolerance}
    {false} hthreshold (fun model _ hgood => by
      simpa only [PMF.toOuterMeasure_apply_singleton, Set.mem_ofPred_eq, predictionError, test]
        using hgood)
  have hbad := train_sound source observe truth evaluate learn params hparams herror hlearn
  have hbound := h.trans (add_le_add hbad le_rfl)
  simp only [ProbComp.eval_bind, ProbComp.eval_map]
  rw [PMF.bind_comm (ProbComp.eval source)]
  have hfinal := by simpa only [PMF.toOuterMeasure_apply_singleton] using hbound
  dsimp only [training, test] at hfinal
  linarith

end Correctness

end Cslib.Crypto.Pseudoentropy.Boosting
