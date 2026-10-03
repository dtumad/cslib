/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Loop
public import Cslib.Computability.Probabilistic.Selection

/-!
# Learning a predictor from sampled descriptions

Validation samples a labeled source example and its weight coin. On acceptance it checks the
prediction; otherwise it returns a fresh fair bit. The resulting acceptance probability measures
weighted prediction bias without rejection sampling. Candidate generation and validation remain
ordinary probabilistic programs with separately synthesized strict PPT certificates.

## References

* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
  the uniform hard-core construction and its learner calls.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the prediction reduction following Game 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  The weighted validation and explicit candidate selection implement the learner for our
  fresh-mask version of the reduction.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability

variable {α : Type}

/-- Run a trial on a freshly weighted example, with a fair baseline when its weight coin fails. -/
noncomputable def weightedTrial (source : ProbComp α) (mask test : α → ProbComp Bool) :
    ProbComp Bool := do
  let value ← source
  let active ← mask value
  if active then test value else OracleComp.uniform Bool

private theorem gate_probability (mask test : ProbComp Bool) :
    winProbability (mask >>= fun active => if active then test else OracleComp.uniform Bool) =
      1 / 2 + winProbability mask * (winProbability test - 1 / 2) := by
  have htotal := PMF.sum_toReal (ProbComp.eval mask)
  simp only [Fintype.sum_bool] at htotal
  simp only [winProbability_bind, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hfair : winProbability (OracleComp.uniform Bool) = 1 / 2 := by
    simp [winProbability, Game.winProbability, OracleComp.uniform, PMF.uniformOfFintype_apply]
  rw [hfair]
  change _ = 1 / 2 + (ProbComp.eval mask true).toReal * _
  nlinarith

/-- Acceptance above a fair baseline is exactly the mask-weighted trial bias. -/
theorem weightedTrial_probability [Fintype α] (source : ProbComp α)
    (mask test : α → ProbComp Bool) :
    winProbability (weightedTrial source mask test) = 1 / 2 +
      ∑ value, (ProbComp.eval source value).toReal *
        (winProbability (mask value) * (winProbability (test value) - 1 / 2)) := by
  rw [weightedTrial, winProbability_bind]
  simp_rw [gate_probability]
  simpa only [one_mul] using PMF.sum_affine (ProbComp.eval source) (1 / 2) 1
    (fun value => winProbability (mask value) * (winProbability (test value) - 1 / 2))

/-- Weighted validation is strict PPT, including examples on which the weight coin fails. -/
theorem weightedTrial_isPPT {Param : Type} {input : Param ↪ Word} {sample : α ↪ Word}
    {source : Param → ProbComp α} {mask test : Param → α → ProbComp Bool}
    (hsource : IsPPTOn input sample source)
    (hmask : IsPPTOn (pairEncoding input sample) boolEncoding
      (fun pair => mask pair.1 pair.2))
    (htest : IsPPTOn (pairEncoding input sample) boolEncoding
      (fun pair => test pair.1 pair.2)) :
    IsPPTOn input boolEncoding (fun a => weightedTrial (source a) (mask a) (test a)) := by
  unfold weightedTrial
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptWeightedTrial : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``weightedTrial, ``weightedTrial_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hsource => solve | aesop (rule_sets := [PPT, PolyTime])))

/-- Saved predictor randomness can be sampled before or after the validation example and
weight coin. Thus validation measures the original randomized predictor's weighted bias. -/
theorem eval_weightedTrial_bind {Code : Type} (candidates : ProbComp Code) (source : ProbComp α)
    (mask : α → ProbComp Bool) (test : Code → α → ProbComp Bool) :
    ProbComp.eval (candidates >>= fun code => weightedTrial source mask (test code)) =
      ProbComp.eval (weightedTrial source mask (fun value => candidates >>= fun code =>
        test code value)) := by
  simp only [weightedTrial, ProbComp.eval_bind]
  rw [PMF.bind_comm]
  congr 1
  funext value
  rw [PMF.bind_comm]
  congr 1
  funext active
  cases active <;> simp only [Bool.false_eq_true, ite_false, ite_true, PMF.bind_const,
    ProbComp.eval_bind]

/-- Complementing the trial negates its weighted bias. The rejected branch remains fair. -/
theorem weightedTrial_not (source : ProbComp α) (mask test : α → ProbComp Bool) :
    winProbability (weightedTrial source mask (fun value => Bool.not <$> test value)) =
      1 - winProbability (weightedTrial source mask test) := by
  have hfair : ProbComp.eval (Bool.not <$> OracleComp.uniform Bool) =
      ProbComp.eval (OracleComp.uniform Bool) := by
    ext bit
    cases bit <;> simp [ProbComp.eval_map, OracleComp.uniform, PMF.map_apply,
      PMF.uniformOfFintype_apply]
  have hlaw : ProbComp.eval (weightedTrial source mask (fun value => Bool.not <$> test value)) =
      ProbComp.eval (Bool.not <$> weightedTrial source mask test) := by
    simp only [weightedTrial, map_bind, ProbComp.eval_bind]
    congr 1
    funext value
    congr 1
    funext active
    cases active <;> simp only [Bool.false_eq_true, ite_false, ite_true, hfair]
  simpa only [winProbability, hlaw, ProbComp.eval_map] using
    Game.winProbability_not (ProbComp.eval (weightedTrial source mask test))

/-- A deterministic predictor's validation rate is one half plus half its weighted correlation. -/
theorem weightedTrial_correlation [Fintype α] (source : ProbComp α)
    (mask : α → ProbComp Bool) (predict truth : α → Bool) :
    winProbability (weightedTrial source mask (fun value => pure (predict value == truth value))) =
      1 / 2 + (∑ value, (ProbComp.eval source value).toReal *
        (winProbability (mask value) * signedVote (predict value) (truth value))) / 2 := by
  rw [weightedTrial_probability, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro value _
  cases predict value <;> cases truth value <;>
    simp [signedVote, winProbability, Game.winProbability] <;> ring

/-- Add a fresh fair orientation bit to a sampled predictor description. -/
noncomputable def randomSign (candidates : ProbComp Word) : ProbComp Word := do
  let negate ← OracleComp.uniform Bool
  (negate :: ·) <$> candidates

/-- A leading sign bit complements a trial's answer; the remaining word is its original code. -/
def signedTest (test : Word → ProbComp Bool) (code : Word) : ProbComp Bool :=
  (fun accept => if code.headD false then !accept else accept) <$> test code.tail

/-- Interpret the same leading sign bit when evaluating the final deterministic predictor. -/
def signedPredict (predict : Word → α → Bool) (code : Word) (value : α) : Bool :=
  if code.headD false then !predict code.tail value else predict code.tail value

@[simp] theorem signedTest_false (test : Word → ProbComp Bool) (code : Word) :
    signedTest test (false :: code) = test code := by simp [signedTest]

@[simp] theorem signedTest_true (test : Word → ProbComp Bool) (code : Word) :
    signedTest test (true :: code) = Bool.not <$> test code := by simp [signedTest]

/-- Either sign of an average validation bias supplies a noticeable chance of drawing a
positively biased signed candidate. The sign choice is made by the program's fair coin. -/
theorem randomSign_good_probability (candidates : ProbComp Word) (test : Word → ProbComp Bool)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (|winProbability (candidates >>= test) - 1 / 2| - ε) / 2 ≤
      ((ProbComp.eval (randomSign candidates)).toOuterMeasure
        {code | 1 / 2 + ε ≤ winProbability (signedTest test code)}).toReal := by
  let threshold := 1 / 2 + ε
  let positive := ((ProbComp.eval candidates).toOuterMeasure
    {code | threshold ≤ winProbability (test code)}).toReal
  let negative := ((ProbComp.eval candidates).toOuterMeasure
    {code | threshold ≤ 1 - winProbability (test code)}).toReal
  have hthreshold : 0 ≤ threshold := by dsimp [threshold]; linarith
  have hpositive : winProbability (candidates >>= test) - threshold ≤ positive := by
    simpa only [winProbability, Game.winProbability, ProbComp.eval_bind,
      PMF.toOuterMeasure_apply_singleton, positive] using
      PMF.toOuterMeasure_rate_ge (ProbComp.eval candidates) (fun code => ProbComp.eval (test code))
        {true} hthreshold
  have hnegative : 1 - winProbability (candidates >>= test) - threshold ≤ negative := by
    have h := PMF.toOuterMeasure_rate_ge (ProbComp.eval candidates)
      (fun code => ProbComp.eval (Bool.not <$> test code)) {true} hthreshold
    have h' : winProbability (candidates >>= fun code => Bool.not <$> test code) - threshold ≤
      ((ProbComp.eval candidates).toOuterMeasure
        {code | threshold ≤ winProbability (Bool.not <$> test code)}).toReal := by
      simpa only [winProbability, Game.winProbability, ProbComp.eval_bind,
        PMF.toOuterMeasure_apply_singleton] using h
    simpa only [← map_bind, winProbability_not, negative] using h'
  have hlaw : ((ProbComp.eval (randomSign candidates)).toOuterMeasure
      {code | threshold ≤ winProbability (signedTest test code)}).toReal =
      (positive + negative) / 2 := by
    simp only [randomSign, ProbComp.eval_bind, OracleComp.uniform, ProbComp.eval_sample,
      PMF.toOuterMeasure_bind_toReal, ProbComp.eval_map, PMF.toOuterMeasure_map_apply,
      Fintype.sum_bool, PMF.uniformOfFintype_apply]
    norm_num [positive, negative, Set.preimage_ofPred_eq, winProbability_not]
    ring
  rw [hlaw]
  have hpos : 0 ≤ positive := ENNReal.toReal_nonneg
  have hneg : 0 ≤ negative := ENNReal.toReal_nonneg
  dsimp only [threshold] at hpositive hnegative
  rcases le_total 0 (winProbability (candidates >>= test) - 1 / 2) with hsign | hsign
  · rw [abs_of_nonneg hsign]
    linarith
  · rw [abs_of_nonpos hsign]
    linarith

/-- A bounded learner samples both orientations and selects by repeated validation trials. -/
noncomputable def learn (candidates : ProbComp Word) (test : Word → ProbComp Bool)
    (confidence inverseGap : ℕ) : ProbComp Word :=
  OracleComp.sampleBest ((confidence + 1) * (4 * inverseGap) ^ 2)
    ((confidence + 1) * (8 * inverseGap) ^ 2) (randomSign candidates) (signedTest test) []

/-- An inverse-polynomial average validation bias, of either sign, yields a positively biased
predictor except with an explicit exponentially small discovery-and-selection error. -/
theorem learn_error_pow (candidates : ProbComp Word) (test : Word → ProbComp Bool)
    (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hbias : (1 : ℝ) / inverseGap ≤ |winProbability (candidates >>= test) - 1 / 2|) :
    ((ProbComp.eval (learn candidates test confidence inverseGap)).toOuterMeasure
      {code | ¬ 1 / 2 + 1 / (4 * inverseGap) ≤ winProbability (signedTest test code)}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  have hgap' : (0 : ℝ) < inverseGap := by exact_mod_cast hgap
  have hgood := randomSign_good_probability candidates test (ε := 1 / (2 * inverseGap))
    (by positivity)
  have hprob : (1 : ℝ) / (4 * inverseGap) ≤
      ((ProbComp.eval (randomSign candidates)).toOuterMeasure
        {code | 1 / 2 + 1 / (2 * inverseGap) ≤ winProbability (signedTest test code)}).toReal := by
    have hquarter : ((1 : ℝ) / inverseGap - 1 / (2 * inverseGap)) / 2 =
        1 / (4 * inverseGap) := by field_simp; ring
    rw [← hquarter]
    exact (by linarith : ((1 : ℝ) / inverseGap - 1 / (2 * inverseGap)) / 2 ≤
      (|winProbability (candidates >>= test) - 1 / 2| - 1 / (2 * inverseGap)) / 2).trans hgood
  have h := ProbComp.sampleBest_error_pow (randomSign candidates) (signedTest test) []
    confidence (4 * inverseGap) (8 * inverseGap) (by positivity) (by positivity)
    (1 / 2 + 1 / (2 * inverseGap)) (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, winProbability, Game.winProbability] using hprob)
  have hthreshold : (1 : ℝ) / 2 + 1 / (2 * inverseGap) - 2 / (8 * inverseGap) =
      1 / 2 + 1 / (4 * inverseGap) := by field_simp; ring
  simpa only [learn, Nat.cast_mul, Nat.cast_ofNat, hthreshold, winProbability, Game.winProbability]
    using h

/-- The selected orientation is used by the final predictor, and its validation rate is the
same rate estimated during learning. -/
theorem signedTest_weightedTrial (source : ProbComp α) (mask : α → ProbComp Bool)
    (predict : Word → α → Bool) (truth : α → Bool) (code : Word) :
    winProbability (signedTest (fun code => weightedTrial source mask
      (fun value => pure (predict code value == truth value))) code) =
      winProbability (weightedTrial source mask
        (fun value => pure (signedPredict predict code value == truth value))) := by
  have hnot : (fun value => pure ((!predict code.tail value) == truth value) : α → ProbComp Bool) =
      fun value => Bool.not <$> pure (predict code.tail value == truth value) := by
    funext value
    cases predict code.tail value <;> cases truth value <;> rfl
  cases hsign : code.headD false with
  | false =>
    simp only [signedTest, signedPredict, hsign, Bool.false_eq_true, ite_false, id_map']
  | true =>
    simp only [signedTest, signedPredict, hsign, ite_true, winProbability_not]
    rw [hnot, weightedTrial_not]

/-- The learned deterministic predictor has positive weighted correlation. The advantage
hypothesis concerns the original candidate distribution, before choosing an orientation. -/
theorem learn_correlation_error_pow [Fintype α] (candidates : ProbComp Word)
    (source : ProbComp α) (mask : α → ProbComp Bool)
    (predict : Word → α → Bool) (truth : α → Bool)
    (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hbias : (1 : ℝ) / inverseGap ≤ |winProbability (candidates >>= fun code =>
      weightedTrial source mask (fun value => pure (predict code value == truth value))) - 1 / 2|) :
    ((ProbComp.eval (learn candidates (fun code => weightedTrial source mask
      (fun value => pure (predict code value == truth value)))
        confidence inverseGap)).toOuterMeasure
        {code | ¬ 1 / (2 * inverseGap) ≤ ∑ value, (ProbComp.eval source value).toReal *
          (winProbability (mask value) * signedVote (signedPredict predict code value)
            (truth value))}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  have h := learn_error_pow candidates (fun code => weightedTrial source mask
    (fun value => pure (predict code value == truth value))) confidence inverseGap hgap hbias
  refine le_trans ?_ h
  apply ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro code hbad hgood
  rw [signedTest_weightedTrial, weightedTrial_correlation] at hgood
  apply hbad
  have hscale : (1 : ℝ) / (2 * inverseGap) = 2 * (1 / (4 * inverseGap)) := by
    field_simp
    ring
  linarith

/-- Each orientation adds exactly one bit, and empirical selection preserves this bound even
when its statistical tests fail. The empty fallback also satisfies it. -/
theorem learn_length_le (candidates : ProbComp Word) (test : Word → ProbComp Bool)
    (confidence inverseGap bound : ℕ)
    (hbound : ∀ code ∈ (ProbComp.eval candidates).support, code.length ≤ bound)
    {code : Word} (hcode : code ∈ (ProbComp.eval
      (learn candidates test confidence inverseGap)).support) : code.length ≤ bound + 1 := by
  rcases ProbComp.sampleBest_support _ _ _ _ _ hcode with hdefault | hsample
  · simp [hdefault]
  · simp only [randomSign, ProbComp.eval_bind, ProbComp.eval_map, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hsample
    obtain ⟨sign, _, original, horiginal, rfl⟩ := hsample
    simpa only [List.length_cons] using Nat.add_le_add_right (hbound original horiginal) 1

/-- The concrete learner meets the boosting loop's contract for the truncated description.
Its validation mask is the current soft weight, and its target correlation covers `gamma`.
The remaining cryptographic premise is the candidate distribution's noticeable validation bias. -/
theorem learn_goodPredictor_error_pow [Fintype α] (candidates : ProbComp Word)
    (source : ProbComp α) (mask : α → ProbComp Bool)
    (predict : Word → α → Bool) (truth : α → Bool) (state : State) (params : Parameters)
    (hparams : params.Valid) (inverseGap bound : ℕ) (hgap : 0 < inverseGap)
    (hgamma : params.gamma ≤ 1 / (2 * inverseGap))
    (hbound : ∀ code ∈ (ProbComp.eval candidates).support, code.length ≤ bound)
    (hcodeBound : bound + 1 ≤ params.codeBound)
    (hmask : ∀ value, winProbability (mask value) = weight params.rate
      (state.margin (signedPredict predict) truth value - state.threshold))
    (hbias : (1 : ℝ) / inverseGap ≤ |winProbability (candidates >>= fun code =>
      weightedTrial source mask (fun value => pure (predict code value == truth value))) - 1 / 2|) :
    ((ProbComp.eval (learn candidates (fun code => weightedTrial source mask
      (fun value => pure (predict code value == truth value)))
        params.confidence inverseGap)).toOuterMeasure
      {code | ¬ state.GoodPredictor (ProbComp.eval source) (signedPredict predict) truth
        params code}).toReal ≤ (((params.confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) *
        (1 / 2 : ℝ) ^ params.confidence := by
  have h := learn_correlation_error_pow candidates source mask predict truth params.confidence
    inverseGap hgap hbias
  refine le_trans ?_ h
  apply ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  rintro code ⟨hbad, hcode⟩ hcorrelation
  apply hbad
  have hsize := learn_length_le candidates _ params.confidence inverseGap bound hbound hcode
  simp only [State.GoodPredictor, List.take_of_length_le (hsize.trans hcodeBound)]
  simp_rw [hmask] at hcorrelation
  have hdensity := (density_mem_Icc (ProbComp.eval source) params.rate
    (fun value => state.margin (signedPredict predict) truth value - state.threshold)).2
  exact ((mul_le_of_le_one_right hparams.gamma_pos.le hdensity).trans hgamma).trans hcorrelation

/-- Adding a random orientation preserves the sampler's strict PPT certificate. -/
theorem randomSign_isPPT {Param : Type} {input : Param ↪ Word} {source : Param → ProbComp Word}
    (hsource : IsPPTOn input wordEncoding source) :
    IsPPTOn input wordEncoding (fun a => randomSign (source a)) := by
  unfold randomSign
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptRandomSign : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``randomSign, ``randomSign_isPPT)]

/-- Validation of signed descriptions is strict PPT for any supplied efficient trial. -/
theorem signedTest_isPPT {Param : Type} {input : Param ↪ Word}
    {test : Param → Word → ProbComp Bool} {code : Param → Word}
    (htest : IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun pair => test pair.1 pair.2)) (hcode : IsPolyTime input code) :
    IsPPTOn input boolEncoding (fun a => signedTest (test a) (code a)) := by
  unfold signedTest
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSignedTest : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``signedTest, ``signedTest_isPPT)]

/-- Reading the orientation and running the saved evaluator remains deterministic polynomial
time on every description, including malformed or truncated ones. -/
theorem signedPredict_isPolyTime {input : α ↪ Word} {predict : Word → α → Bool}
    (hpredict : IsPolyTime (pairEncoding wordEncoding input)
      (fun pair => [predict pair.1 pair.2])) :
    IsPolyTime (pairEncoding wordEncoding input)
      (fun pair => [signedPredict predict pair.1 pair.2]) := by
  unfold signedPredict
  polytime

/-- The complete learner is strict PPT in its input, confidence, and inverse bias parameters. -/
theorem learn_isPPT {Param : Type} {input : Param ↪ Word}
    {candidates : Param → ProbComp Word} {test : Param → Word → ProbComp Bool}
    {confidence inverseGap : Param → ℕ}
    (hcandidates : IsPPTOn input wordEncoding candidates)
    (htest : IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun pair => test pair.1 pair.2))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (confidence a)))
    (hgap : IsPolyTime input (fun a => unaryEncoding (inverseGap a))) :
    IsPPTOn input wordEncoding (fun a =>
      learn (candidates a) (test a) (confidence a) (inverseGap a)) := by
  unfold learn
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptLearn : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``learn, ``learn_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hcandidates => solve | aesop (rule_sets := [PPT, PolyTime])))

end Cslib.Crypto.Pseudoentropy.Boosting
