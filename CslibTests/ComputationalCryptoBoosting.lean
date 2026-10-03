/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Loop
public import Cslib.Computability.Probabilistic.Repeat

/-!
# Hard-core boosting regressions

These examples check clipping, weighted prediction, equality at the boosting clock boundary,
exact dyadic sampling, and independent repeated trials. The trial counter has a synthesized
strict PPT certificate and an accuracy theorem with exponentially small failure probability.
Density and majority decisions compose an arbitrary certified training sampler. Their proofs
exercise rational guards and the error bound for the executable majority predictor; the complete
uniform hard-core reduction remains a separate obligation.
The clocked-loop example instantiates a perfect learner on visible labels and checks both its
strict PPT certificate and its exponentially small total failure bound.
-/

public section

open Cslib Cslib.Probability Cslib.Crypto.Pseudoentropy.Boosting Cslib.Probability.PMF

namespace CslibTests.ComputationalCryptoBoosting

/-- Both endpoints of the linear segment agree with the adjoining constant regions. -/
theorem clipping_endpoints :
    weight (1 / 4) 0 = 1 ∧ weight (1 / 4) 4 = 0 ∧ potential (1 / 4) 4 = 0 := by
  norm_num [weight, potential]

/-- The three-to-one majority has correlation `1 / 2` on the initial full-density measure. -/
theorem three_correct_votes_progress :
    averagePotential (PMF.uniformOfFintype (Fin 4)) (1 / 2)
      (fun x => if x = 0 then -1 else 1) ≤ 3 / 4 := by
  let source := PMF.uniformOfFintype (Fin 4)
  have h := add_predictor_progress source (γ := 1 / 2) (δ := 1) (by norm_num) (by norm_num)
    (fun _ => 0) (fun x => if x = 0 then -1 else 1)
    (fun x => by split_ifs <;> norm_num) (by simp)
    (by norm_num [source, weight, Fin.sum_univ_succ, PMF.uniformOfFintype_apply])
  norm_num [source] at h
  exact h

/-- A synthetic real-valued trace attains equality in the charged progress estimate and in
the final margin bound. In particular, the clock lemma needs no strict inequality or `δ < 1`.
This tests the analytic contract, without claiming that this trace came from a weak learner. -/
theorem clock_boundary_can_be_tight :
    (∑ x : Bool, (PMF.uniformOfFintype Bool x).toReal * (1 : ℝ)) * (4 * (1 * 1 ^ 2 / 8)) ≤
      ∑ x : Bool, (PMF.uniformOfFintype Bool x).toReal * ((1 : ℝ) * (4 / 8)) := by
  let source := PMF.uniformOfFintype Bool
  have hpotential (i : ℕ) :
      averagePotential source 1 (fun _ => (i : ℝ) / 8 - i) = 1 / 2 + 7 * i / 8 := by
    have hi : (i : ℝ) / 8 - i ≤ 0 := by have := Nat.cast_nonneg (α := ℝ) i; linarith
    simp only [averagePotential, potential_of_nonpos 1 hi, ← Finset.sum_mul, sum_toReal, one_mul]
    ring
  exact dense_margin_of_iterations source (γ := 1) (δ := 1) (by norm_num) (by norm_num)
    (fun i _ => (i : ℝ) / 8) (fun i => i) 4 (by simp) (by simp) (by norm_num)
    (by
      intro i _
      simp only [mul_one, hpotential]
      push_cast
      ring_nf
      rfl)
    (by norm_num) (fun _ => 1) (fun _ => by constructor <;> norm_num)
    (by simp only [mul_one, sum_toReal, le_refl])

private theorem dyadicSize_three : dyadicSize 3 = 4 := by decide

/-- A one-vote positive margin at rate `1 / 4` has acceptance probability exactly `3 / 4`. -/
theorem sampled_weight_three_quarters :
    (ProbComp.eval (sampleWeight 3 1 0 [true, true, false] true) true).toReal = 3 / 4 := by
  rw [eval_sampleWeight_true]
  norm_num [weight, voteMargin, dyadicSize_three, List.count_cons]

/-- Large numerators saturate at one, and zero numerators always reject. -/
theorem dyadic_coin_endpoints :
    ProbComp.eval (sampleDyadicCoin 3 0) true = 0 ∧
      ProbComp.eval (sampleDyadicCoin 3 9) true = 1 := by
  norm_num [eval_sampleDyadicCoin_true, dyadicSize_three, ENNReal.div_self]

/-- Two fresh biased draws both accept with probability `9 / 16`, rather than sharing one draw. -/
theorem repeated_coins_are_independent :
    (ProbComp.eval (OracleComp.replicate 2 (sampleDyadicCoin 3 3)) [true, true]).toReal =
      9 / 16 := by
  have h := ProbComp.eval_replicate_apply_ofFn (sampleDyadicCoin 3 3)
    (fun _ : Fin 2 => true)
  norm_num [List.ofFn_succ, eval_sampleDyadicCoin_true, dyadicSize_three] at h
  rw [h]
  norm_num

/-- Sixty-four independent weight trials estimate `3 / 4` to tolerance `1 / 4`, with the
correct Hoeffding exponent. -/
theorem repeated_weight_estimate :
    ((ProbComp.eval (OracleComp.countTrue 64
      (sampleWeight 3 1 0 [true, true, false] true))).toOuterMeasure
        {successes | (1 : ℝ) / 4 ≤ |(successes : ℝ) / 64 - 3 / 4|}).toReal ≤
      2 * Real.exp (-8) := by
  have h := ProbComp.countTrue_average_deviation 64 (by norm_num)
    (sampleWeight 3 1 0 [true, true, false] true) (ε := 1 / 4) (by norm_num)
  norm_num [sampled_weight_three_quarters] at h ⊢
  exact h

/-- A client estimator uses a cubic trial budget to obtain inverse-linear accuracy with
exponentially small failure. -/
noncomputable def weightTrials (n : ℕ) (votes : Word) (truth : Bool) : ProbComp ℕ :=
  OracleComp.countTrue ((n + 1) ^ 3) (sampleWeight n 1 0 votes truth)

/-- Every loop, vote count, arithmetic operation, and sampled bit is covered by the certificate. -/
theorem weightTrials_isPPT :
    IsPPTOn (pairEncoding unaryEncoding (pairEncoding wordEncoding boolEncoding)) unaryEncoding
      (fun input => weightTrials input.1 input.2.1 input.2.2) := by
  unfold weightTrials
  ppt

/-- The same certified program estimates the mathematical soft weight to inverse-linear
tolerance, with failure at most `2⁻ⁿ`. -/
theorem weightTrials_accurate (n : ℕ) (votes : Word) (truth : Bool) :
    ((ProbComp.eval (weightTrials n votes truth)).toOuterMeasure
      {successes | (1 : ℝ) / (n + 1) ≤ |(successes : ℝ) / (n + 1) ^ 3 -
        weight (1 / dyadicSize n) (2 * (votes.count truth : ℝ) - votes.length)|}).toReal ≤
      (1 / 2 : ℝ) ^ n := by
  have h := ProbComp.countTrue_average_deviation_pow n (n + 1) (by lia)
    (sampleWeight n 1 0 votes truth)
  simpa [weightTrials, pow_succ, mul_comm, eval_sampleWeight_true, voteMargin] using h

/-- Ties use the documented false output and count as nonpositive margins for either label. -/
theorem majority_tie : majority [true, false] = false ∧
    nonpositiveMargin [true, false] true = true ∧
      nonpositiveMargin [true, false] false = true := by decide

/-- A training source supplies vote words and their labels; the stopping test has density `1/2`.
All probability estimation and rational comparisons are ordinary program combinators. -/
noncomputable def majorityStop (n : ℕ) (training : ProbComp (Word × Bool)) : ProbComp Bool :=
  testMajority n 64 1 2 ((fun pair => nonpositiveMargin pair.1 pair.2) <$> training)

/-- A supplied training sampler composes without exposing its machine or saved-coin evaluator. -/
theorem majorityStop_isPPT {training : ℕ → ProbComp (Word × Bool)}
    (htraining : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) training) :
    IsPPTOn unaryEncoding boolEncoding (fun n => majorityStop n (training n)) := by
  unfold majorityStop
  fail_if_success (clear htraining; ppt)
  ppt

/-- A returned stopping decision certifies majority error at most `7/32`; continuation certifies
nonpositive-margin mass at least `3/16`, except with exponentially small failure. -/
theorem majorityStop_sound (n : ℕ) (training : ProbComp (Word × Bool)) :
    ((ProbComp.eval (majorityStop n training)).toOuterMeasure {stop | ¬ if stop then
      ((ProbComp.eval training).toOuterMeasure {pair | majority pair.1 ≠ pair.2}).toReal ≤ 7 / 32
      else (3 : ℝ) / 16 ≤ ((ProbComp.eval training).toOuterMeasure
        {pair | voteMargin pair.1 pair.2 ≤ 0}).toReal}).toReal ≤ (1 / 2 : ℝ) ^ n := by
  have h := testMajority_source_sound training Prod.fst Prod.snd n 64 1 2
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [majorityStop] at h ⊢
  exact h

/-- A density test composes the same training sampler with exact dyadic weight trials. -/
noncomputable def densityShift (n : ℕ) (training : ProbComp (Word × Bool)) : ProbComp Bool :=
  testShift n 256 1 2 1 4 do
    let (votes, truth) ← training
    sampleWeight 3 1 0 votes truth

/-- The entire sampled density decision has a synthesized strict PPT certificate. -/
theorem densityShift_isPPT {training : ℕ → ProbComp (Word × Bool)}
    (htraining : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) training) :
    IsPPTOn unaryEncoding boolEncoding (fun n => densityShift n (training n)) := by
  unfold densityShift
  ppt

/-- Density `1/2`, rate `1/2`, and a 128-round clock. Eight extra confidence bits pay for the
two tests in every round. Empty descriptions suffice for the observation-reading evaluator. -/
def perfectParameters (n : ℕ) : Parameters := ⟨n + 8, 1, 0, 0, 0⟩

private theorem dyadicSize_zero : dyadicSize 0 = 2 := by decide

private theorem perfectParameters_valid (n : ℕ) : (perfectParameters n).Valid := by
  norm_num [Parameters.Valid, perfectParameters, Parameters.denominator, dyadicSize_zero]

/-- Here the observation reveals the label, so reading its first bit is a perfect predictor.
This supplies a concrete, satisfiable learner contract without assuming cryptographic hardness. -/
def visibleLabel (_code observation : Word) : Bool := observation.headD false

/-- The actual sampled boosting program, with a learner that returns the empty description. -/
noncomputable def perfectTrainingLoop (n : ℕ) : ProbComp State :=
  run visibleLabel ((fun bit : Bool => ([bit], bit)) <$> OracleComp.uniform Bool)
    (fun _ => pure []) (perfectParameters n)

/-- The evaluator, two sampled guards, adaptive state, and complete loop are all strict PPT. -/
theorem perfectTrainingLoop_isPPT : IsPPTOn unaryEncoding State.encoding perfectTrainingLoop := by
  unfold perfectTrainingLoop
  apply run_isPPT
  · unfold visibleLabel
    polytime
  · ppt
  · ppt
  all_goals dsimp only [perfectParameters]; polytime

private theorem visibleLabel_good (source : PMF Bool) (n : ℕ) (state : State) (code : Word) :
    State.GoodPredictor source (fun code bit => visibleLabel code [bit]) id
      (perfectParameters n) state code := by
  norm_num [State.GoodPredictor, visibleLabel, signedVote, Parameters.gamma, Parameters.delta,
    Parameters.rate, Parameters.inverseRate, Parameters.denominator, perfectParameters,
    dyadicSize_zero, density]

/-- The zero-error learner leaves only the two sampled guard errors per round, totaling `2⁻ⁿ`. -/
theorem perfectTrainingLoop_sound (n : ℕ) :
    ((ProbComp.eval (perfectTrainingLoop n)).toOuterMeasure
      {state | ¬ State.Successful (PMF.uniformOfFintype Bool)
        (fun code bit => visibleLabel code [bit]) id (perfectParameters n) state}).toReal ≤
      (1 / 2 : ℝ) ^ n := by
  have h := run_sound (OracleComp.uniform Bool) (fun bit => [bit]) id visibleLabel
    (fun _ => pure []) (perfectParameters n) (perfectParameters_valid n)
    (error := 0) le_rfl (by
      intro state _
      simp [ProbComp.eval_pure, visibleLabel_good])
  have hbudget : (perfectParameters n).clock *
      (2 * (1 / 2 : ℝ) ^ (perfectParameters n).confidence + 0) = (1 / 2 : ℝ) ^ n := by
    norm_num [Parameters.clock, Parameters.inverseRate, Parameters.denominator,
      perfectParameters, dyadicSize_zero, pow_add]
    ring
  rw [hbudget] at h
  have huniform : ProbComp.eval (OracleComp.uniform Bool) = PMF.uniformOfFintype Bool := by
    simp [OracleComp.uniform]
  rw [huniform] at h
  simpa only [perfectTrainingLoop, id_eq] using h

/-- The resource bound holds even for an arbitrary learner returning arbitrarily long words.
Every stored description is truncated before the next iteration. -/
theorem clocked_state_bound (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (n : ℕ) (state : State)
    (hstate : state ∈ (ProbComp.eval (run evaluate source learn (perfectParameters n))).support) :
    (State.encoding state).length ≤ 388 := by
  have h := (run_bounded evaluate source learn (perfectParameters n)
    state hstate).length_encoding_le
  simpa [Parameters.clock, Parameters.inverseRate, Parameters.denominator, perfectParameters,
    dyadicSize_zero] using h

end CslibTests.ComputationalCryptoBoosting
