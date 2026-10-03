/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Hybrid.SavedPrediction
public import Cslib.Crypto.Computational.Pseudoentropy.Learning
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Training

/-!
# A sequence learner for the boosting loop

Each boosting state defines a fresh soft mask. The learner samples saved coordinate predictors
using that mask, then validates them on fresh labeled examples. Stored descriptions contain the
sampled data and test coins; they do not recursively contain the state that generated them.
Their uniform size bound therefore justifies the loop's truncation on every execution.

The evaluator is obtained from the sequence test's strict PPT certificate. Its signed version
interprets the learner's orientation bit, and is also the evaluator used by subsequent rounds.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the prediction reduction.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  We use fresh soft masks and the clocked boosting implementation.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SequenceLearner

open Probability Boosting

/-- Sample the current soft weight on a fresh labeled observation. -/
noncomputable def mask (evaluate : Word → Word → Bool) (params : Parameters) (state : State)
    (sample : Word × Bool) : ProbComp Bool :=
  sampleWeight params.rateBound 1 state.threshold (state.votes evaluate sample.1) sample.2

/-- Draw saved coordinate descriptions before receiving any challenge observation. -/
noncomputable def candidates (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (base : Word) (count c d width : ℕ) (params : Parameters) (state : State) : ProbComp Word :=
  SavedPrediction.sample wordEncoding base
    (maskedSample source Prod.fst Prod.snd (mask evaluate params state)) source count c d width

/-- Learn a signed coordinate predictor against the state's soft mask. The evaluator supplied
here interprets unsigned descriptions; the loop uses `signedPredict evaluate`. -/
noncomputable def learn (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (base : Word) (count c d width inverseGap : ℕ) (params : Parameters) (state : State) :
    ProbComp Word :=
  Boosting.learn (candidates (signedPredict evaluate) source base count c d width params state)
    (fun code => weightedTrial source (mask (signedPredict evaluate) params state)
      (fun sample => pure (evaluate code sample.1 == sample.2))) params.confidence inverseGap

/-- Train with the sequence learner, then predict from the challenge's public observation. -/
noncomputable def predict (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (base : Word) (count c d width inverseGap : ℕ) (params : Parameters) (observation : Word) :
    ProbComp Bool := do
  let model ← Boosting.train (signedPredict evaluate) source
    (learn evaluate source base count c d width inverseGap params) params
  Boosting.predict (signedPredict evaluate) params.predictionGridBound model observation

section Efficiency

variable {α : Type} {input : α ↪ Word} {evaluate : Word → Word → Bool}
  {params : α → Parameters} {state : α → State}

/-- Masks compose the efficient evaluator with the stored state and a labeled sample. -/
theorem mask_isPPT {sample : α → Word × Bool}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hrate : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hstate : IsPolyTime input (fun a => State.encoding (state a)))
    (hsample : IsPolyTime input (fun a => pairEncoding wordEncoding boolEncoding (sample a))) :
    IsPPTOn input boolEncoding (fun a => mask evaluate (params a) (state a) (sample a)) := by
  have hvotes := State.votes_isPolyTime hevaluate hstate hsample.fst
  have hthreshold := State.threshold_isPolyTime hstate
  have htruth := hsample.snd
  unfold mask
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptMask : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``mask, ``mask_isPPT)]

/-- Drawing descriptions is strict PPT even on executions with inaccurate guards or learners. -/
theorem candidates_isPPT {source : α → ProbComp (Word × Bool)} {base : α → Word}
    {count width : α → ℕ} (c d : ℕ)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hbase : IsPolyTime input base)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hrate : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hstate : IsPolyTime input (fun a => State.encoding (state a))) :
    IsPPTOn input wordEncoding (fun a =>
      candidates evaluate (source a) (base a) (count a) c d (width a) (params a) (state a)) := by
  have hmasked : IsPPTOn input (pairEncoding wordEncoding boolEncoding) (fun a =>
      maskedSample (source a) Prod.fst Prod.snd (mask evaluate (params a) (state a))) := by
    ppt
  unfold candidates
  exact SavedPrediction.sample_isPPT c d hbase hmasked hsource hcount hwidth

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptCandidates : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``candidates, ``candidates_isPPT)]

/-- The adaptive sequence learner is strict PPT in the complete stored state and source input. -/
theorem learn_isPPT {source : α → ProbComp (Word × Bool)} {base : α → Word}
    {count width inverseGap : α → ℕ} (c d : ℕ)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hbase : IsPolyTime input base)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hgap : IsPolyTime input (fun a => unaryEncoding (inverseGap a)))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (hrate : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hstate : IsPolyTime input (fun a => State.encoding (state a))) :
    IsPPTOn input wordEncoding (fun a =>
      learn evaluate (source a) (base a) (count a) c d (width a) (inverseGap a)
        (params a) (state a)) := by
  have hsigned := signedPredict_isPolyTime hevaluate
  have hcandidates := candidates_isPPT c d hsigned hsource hbase hcount hwidth hrate hstate
  unfold learn
  apply Boosting.learn_isPPT hcandidates <;> ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptLearn : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``learn, ``learn_isPPT)]

/-- The complete reduction has one uniform strict PPT implementation. The client supplies
source and evaluator certificates and polynomial-time numerical parameters, not machine data. -/
theorem predict_isPPT {source : α → ProbComp (Word × Bool)} {base observation : α → Word}
    {count width inverseGap : α → ℕ} (c d : ℕ)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hbase : IsPolyTime input base) (hobservation : IsPolyTime input observation)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hgap : IsPolyTime input (fun a => unaryEncoding (inverseGap a)))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (hdensityNum : IsPolyTime input (fun a => unaryEncoding (params a).densityNumerator))
    (hdensityBound : IsPolyTime input (fun a => unaryEncoding (params a).densityBound))
    (hrate : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hcodeBound : IsPolyTime input (fun a => unaryEncoding (params a).codeBound)) :
    IsPPTOn input boolEncoding (fun a =>
      predict evaluate (source a) (base a) (count a) c d (width a) (inverseGap a)
        (params a) (observation a)) := by
  have hsigned := signedPredict_isPolyTime hevaluate
  have hlearner : IsPPTOn (pairEncoding input State.encoding) wordEncoding (fun pair =>
      learn evaluate (source pair.1) (base pair.1) (count pair.1) c d (width pair.1)
        (inverseGap pair.1) (params pair.1) pair.2) := by
    apply learn_isPPT c d hevaluate <;> ppt
  have htraining := Boosting.train_isPPT
    (learn := fun a => learn evaluate (source a) (base a) (count a) c d (width a)
      (inverseGap a) (params a)) hsigned hsource hlearner hconfidence hdensityNum
      hdensityBound hrate hcodeBound
  have hprecision : IsPolyTime input (fun a => unaryEncoding (params a).predictionGridBound) := by
    unfold Parameters.predictionGridBound Parameters.predictionInverseTolerance Parameters.clock
      Parameters.inverseRate Parameters.denominator
    polytime
  unfold predict
  apply IsPPTOn.bind_with (middle := pairEncoding State.encoding unaryEncoding)
  · exact htraining
  · apply Boosting.predict_isPPT hsigned <;> polytime

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptPredict : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``predict, ``predict_isPPT)]

end Efficiency

/-- The mask used by the executable learner is exactly the analytic soft weight. -/
theorem mask_probability (evaluate : Word → Word → Bool) (params : Parameters) (state : State)
    (sample : Word × Bool) :
    winProbability (mask evaluate params state sample) = weight params.rate
      (voteMargin (state.votes evaluate sample.1) sample.2 - state.threshold) := by
  simpa only [mask, winProbability, Game.winProbability, Parameters.rate, Parameters.inverseRate,
    Nat.cast_one] using eval_sampleWeight_true params.rateBound 1 state.threshold
      (state.votes evaluate sample.1) sample.2

/-- The code bound depends on the source's output width, not the current state's size. -/
theorem candidates_length_le (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (base : Word) (count c d width : ℕ) (params : Parameters) (state : State)
    (hwidth : ∀ sample ∈ (ProbComp.eval source).support, sample.1.length ≤ width)
    {code : Word} (hcode : code ∈ (ProbComp.eval
      (candidates evaluate source base count c d width params state)).support) :
    code.length ≤ SavedPrediction.codeBound base.length count c d width := by
  apply SavedPrediction.length_sample_le wordEncoding base _ source count c d width _ hwidth hcode
  intro sample hsample
  simp only [eval_maskedSample, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hsample
  obtain ⟨original, horiginal, bit, _, rfl⟩ := hsample
  exact hwidth original horiginal

/-- Orientation and empirical selection add at most one bit to a sampled description. -/
theorem learn_length_le (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (base : Word) (count c d width inverseGap : ℕ) (params : Parameters) (state : State)
    (hwidth : ∀ sample ∈ (ProbComp.eval source).support, sample.1.length ≤ width)
    {code : Word} (hcode : code ∈ (ProbComp.eval
      (learn evaluate source base count c d width inverseGap params state)).support) :
    code.length ≤ SavedPrediction.codeBound base.length count c d width + 1 :=
  Boosting.learn_length_le _ _ params.confidence inverseGap _
    (fun _ => candidates_length_le _ _ _ _ _ _ _ _ _ hwidth) hcode

/-- One certified sequence test gives a fixed evaluator for every parameter, source, and
boosting state. The challenge observation is supplied only after the description is sampled. -/
theorem exists_evaluator {Param : Type} {input : Param ↪ Word}
    {test : Param → List (Word × Bool) → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding input (listEncoding (pairEncoding wordEncoding boolEncoding)))
      boolEncoding (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Bool),
      IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]) ∧
      ∀ a {α : Type} (source : ProbComp α) (observe : α → Word) (truth : α → Bool)
          count width params state observation, observation.length ≤ width →
        ProbComp.eval ((fun code => evaluate code observation) <$>
          candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
            (input a) count c d width params state) =
          ProbComp.eval (maskedSequencePredictor source observe truth
            (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
            count (test a) observation) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := SavedPrediction.exists_evaluator htest
  refine ⟨c, d, evaluate, hefficient, ?_⟩
  intro a α source observe truth count width params state observation hwidth
  simpa only [candidates, maskedSequencePredictor, maskedSample, bind_map_left, Functor.map_map,
    Function.comp_def, wordEncoding, Function.Embedding.refl_apply] using
      hrealize a (maskedSample ((fun x => (observe x, truth x)) <$> source) Prod.fst Prod.snd
        (mask (signedPredict evaluate) params state)) ((fun x => (observe x, truth x)) <$> source)
          count width observation hwidth

/-- A common bound for all sampled guards, candidate discovery, validation, and slope selection. -/
noncomputable def failureBound (params : Parameters) (inverseGap : ℕ) : ℝ :=
  ((params.clock * ((params.confidence + 1) * (4 * inverseGap) ^ 2 + 3) +
    dyadicSize params.predictionGridBound + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ params.confidence

/-- Polynomial parameters and at least `n` confidence bits make the complete failure bound
negligible. The polynomial degree may depend on the fixed sequence distinguisher. -/
theorem failureBound_negligible {params : ℕ → Parameters} {inverseGap : ℕ → ℕ}
    (hconfidence : PolynomiallyBounded (fun n => (params n).confidence))
    (hdensity : PolynomiallyBounded (fun n => (params n).densityBound))
    (hrate : PolynomiallyBounded (fun n => (params n).rateBound))
    (hgap : PolynomiallyBounded inverseGap) (hbudget : ∀ n, n ≤ (params n).confidence) :
    Negligible (fun n => failureBound (params n) (inverseGap n)) := by
  have hdecay : Negligible (fun n => (1 / 2 : ℝ) ^ (params n).confidence) := by
    apply negligible_of_le (negligible_geometric (ratio := (1 / 2 : ℝ)) (by norm_num))
      (fun _ => by positivity)
    intro n
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hbudget n)
  apply negligible_polynomial_mul hdecay (fun _ => by positivity)
  unfold Parameters.predictionGridBound Parameters.predictionInverseTolerance Parameters.clock
    Parameters.inverseRate Parameters.denominator
  fun_prop

open Filter in
/-- Eventually all sampling failures consume at most half the inverse-polynomial prediction
advantage. The threshold may depend on the fixed distinguisher and its polynomial parameters. -/
theorem failureBound_eventually_le {params : ℕ → Parameters} {inverseGap : ℕ → ℕ}
    (hconfidence : PolynomiallyBounded (fun n => (params n).confidence))
    (hdensity : PolynomiallyBounded (fun n => (params n).densityBound))
    (hrate : PolynomiallyBounded (fun n => (params n).rateBound))
    (hgap : PolynomiallyBounded inverseGap) (hbudget : ∀ n, n ≤ (params n).confidence) :
    ∀ᶠ n in atTop, failureBound (params n) (inverseGap n) ≤
      1 / (2 * (params n).predictionInverseTolerance) := by
  have hfailure := failureBound_negligible hconfidence hdensity hrate hgap hbudget
  have htolerance : PolynomiallyBounded (fun n => 2 * (params n).predictionInverseTolerance) := by
    unfold Parameters.predictionInverseTolerance Parameters.inverseRate Parameters.denominator
    fun_prop
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    hfailure.eventually_le_inv_polynomial (fun _ => by unfold failureBound; positivity)
      htolerance (fun n => Nat.mul_pos (by decide) (params n).predictionInverseTolerance_pos)

section Correctness

variable {α : Type} [Fintype α]

/-- A noticeable sequence gap supplies the actual loop contract. Both the sampled descriptions
and their orientations fit the declared code bound, so truncation preserves their predictions. -/
theorem learn_goodPredictor_error (source : ProbComp α) (observe : α → Word) (truth : α → Bool)
    (evaluate : Word → Word → Bool) (base : Word) (count c d width inverseGap : ℕ)
    (params : Parameters) (state : State) (test : List (Word × Bool) → ProbComp Bool)
    (hparams : params.Valid) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, (observe value).length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width + 1 ≤ params.codeBound)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => evaluate code (observe value)) <$>
        candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
          base count c d width params state) =
        ProbComp.eval (maskedSequencePredictor source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
          count test (observe value)))
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap ≤
      |winProbability (OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
          >>= test) -
        winProbability (OracleComp.replicate count (maskedSample source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))) >>= test)|) :
    ((ProbComp.eval (learn evaluate ((fun x => (observe x, truth x)) <$> source)
      base count c d width inverseGap params state)).toOuterMeasure
      {code | ¬ state.GoodPredictor (ProbComp.eval source)
        (fun code x => signedPredict evaluate code (observe x)) truth params code}).toReal ≤
      (((params.confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) *
        (1 / 2 : ℝ) ^ params.confidence := by
  let descriptions := candidates (signedPredict evaluate)
    ((fun x => (observe x, truth x)) <$> source) base count c d width params state
  let weights := fun x => mask (signedPredict evaluate) params state (observe x, truth x)
  have hsize : ∀ code ∈ (ProbComp.eval descriptions).support,
      code.length ≤ SavedPrediction.codeBound base.length count c d width := by
    apply candidates_length_le
    intro sample hsample
    simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hsample
    obtain ⟨value, hvalue, rfl⟩ := hsample
    exact hwidth value hvalue
  have hbias : (1 : ℝ) / inverseGap ≤ |winProbability (descriptions >>= fun code =>
      weightedTrial source weights (fun x => pure (evaluate code (observe x) == truth x))) -
        1 / 2| := by
    have hcount : (0 : ℝ) < dyadicSize count := by exact_mod_cast dyadicSize_pos count
    rw [maskedSequence_validation_gap source observe truth weights count test descriptions
      evaluate hrealize, abs_mul, abs_of_pos hcount] at hdistinguish
    apply (mul_le_mul_iff_right₀ hcount).mp
    simpa only [mul_one_div] using hdistinguish
  have h := Boosting.learn_goodPredictor_error_pow descriptions source weights
    (fun code x => evaluate code (observe x)) truth state params hparams inverseGap _ hgap hgamma
    hsize hbound (fun x => mask_probability _ _ _ _) hbias
  have hsigned : signedPredict (fun code x => evaluate code (observe x)) =
      fun code x => signedPredict evaluate code (observe x) := rfl
  rw [hsigned] at h
  simpa only [learn, descriptions, weights, weightedTrial, bind_map_left] using h

/-- Distinguishing every dense masked sequence yields a predictor beating `delta / 2`, up to
the single explicit failure bound. The learner here is the executable saved-description program. -/
theorem predict_error (source : ProbComp α) (observe : α → Word) (truth : α → Bool)
    (evaluate : Word → Word → Bool) (base : Word) (count c d width inverseGap : ℕ)
    (params : Parameters) (test : List (Word × Bool) → ProbComp Bool)
    (hparams : params.Valid) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, (observe value).length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width + 1 ≤ params.codeBound)
    (hrealize : ∀ state value, value ∈ (ProbComp.eval source).support →
      ProbComp.eval ((fun code => evaluate code (observe value)) <$>
        candidates (signedPredict evaluate) ((fun x => (observe x, truth x)) <$> source)
          base count c d width params state) =
        ProbComp.eval (maskedSequencePredictor source observe truth
          (fun x => mask (signedPredict evaluate) params state (observe x, truth x))
          count test (observe value)))
    (hdistinguish : ∀ state : State,
      params.delta ≤ density (ProbComp.eval source) params.rate
        (fun x => state.margin (fun code x => signedPredict evaluate code (observe x)) truth x -
          state.threshold) →
      (dyadicSize count : ℝ) / inverseGap ≤
        |winProbability (OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
            >>= test) -
          winProbability (OracleComp.replicate count (maskedSample source observe truth
            (fun x => mask (signedPredict evaluate) params state (observe x, truth x))) >>=
              test)|) :
    (ProbComp.eval (do
      let x ← source
      (fun answer => answer == truth x) <$> predict evaluate
        ((fun x => (observe x, truth x)) <$> source) base count c d width inverseGap params
        (observe x)) false).toReal ≤
      params.delta / 2 - 1 / params.predictionInverseTolerance +
        failureBound params inverseGap := by
  have h := Boosting.train_predict_error source observe truth (signedPredict evaluate)
    (learn evaluate ((fun x => (observe x, truth x)) <$> source)
      base count c d width inverseGap params) params hparams (by positivity)
    (fun state hdense => learn_goodPredictor_error source observe truth evaluate base
      count c d width inverseGap params state test hparams hgap hgamma hwidth hbound
        (hrealize state) (hdistinguish state hdense))
  have hbudget : params.delta / 2 - 1 / params.predictionInverseTolerance +
      params.clock * (2 * (1 / 2 : ℝ) ^ params.confidence +
        (((params.confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) *
          (1 / 2 : ℝ) ^ params.confidence) +
      (dyadicSize params.predictionGridBound + 1) * (1 / 2 : ℝ) ^ params.confidence =
        params.delta / 2 - 1 / params.predictionInverseTolerance +
          failureBound params inverseGap := by
    unfold failureBound
    push_cast
    ring
  rw [hbudget] at h
  simpa only [predict, ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind] using h

end Correctness

end Cslib.Crypto.Pseudoentropy.SequenceLearner
