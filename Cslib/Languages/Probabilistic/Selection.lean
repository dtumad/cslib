/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Concentration
public import Cslib.Languages.Probabilistic.Iteration

/-!
# Selecting a candidate by repeated trials

`OracleComp.selectBest count trials test` estimates the acceptance probability of each candidate
below `count` and returns the candidate with the largest success count. It is an ordinary bounded
program. The correctness rule charges one estimation failure per candidate and loses twice the
estimation tolerance relative to the best candidate. No independence between estimates is needed
by the selection argument; each estimate uses the independent trials in `countTrue`.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u

variable {Query : Type u} {Response : Query → Type u}

/-- Update the next index, best index, and best success count, preferring later indices on ties. -/
def selectUpdate (state : ℕ × ℕ × ℕ) (successes : ℕ) : ℕ × ℕ × ℕ :=
  (state.1 + 1, if state.2.2 ≤ successes then (state.1, successes) else state.2)

/-- Estimate one candidate and update the running empirical maximum. -/
def selectStep (trials : ℕ) (test : ℕ → OracleComp Query Response Bool)
    (state : ℕ × ℕ × ℕ) : OracleComp Query Response (ℕ × ℕ × ℕ) :=
  selectUpdate state <$> countTrue trials (test state.1)

/-- Return an index with the largest observed success count.
When there are no candidates, return zero. -/
def selectBest (count trials : ℕ) (test : ℕ → OracleComp Query Response Bool) :
    OracleComp Query Response ℕ :=
  (fun state => state.2.1) <$> iterate count (selectStep trials test) (0, 0, 0)

end OracleComp

namespace ProbComp

/-- Candidate selection keeps both indices within the elapsed count and the success count within
the trial budget on every execution, regardless of statistical estimation errors. -/
theorem selectStep_bounded (trials : ℕ) (test : ℕ → ProbComp Bool) (i : ℕ)
    (state : ℕ × ℕ × ℕ) (hstate : state.1 = i ∧ state.2.1 ≤ i ∧ state.2.2 ≤ trials)
    (next : ℕ × ℕ × ℕ) (hnext : next ∈ (eval (OracleComp.selectStep trials test state)).support) :
    next.1 = i + 1 ∧ next.2.1 ≤ i + 1 ∧ next.2.2 ≤ trials := by
  rw [OracleComp.selectStep, eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨successes, hsuccesses, rfl⟩ := hnext
  have hbound := countTrue_le trials (test state.1) hsuccesses
  dsimp only [OracleComp.selectUpdate]
  split_ifs <;> simp_all
  lia

private def SelectionInvariant (trials : ℕ) (rate : ℕ → ℝ) (ε : ℝ)
    (i : ℕ) (state : ℕ × ℕ × ℕ) : Prop :=
  state.1 = i ∧ (i = 0 → state.2 = (0, 0)) ∧
    (0 < i → state.2.1 < i ∧ (state.2.2 : ℝ) / trials ≤ rate state.2.1 + ε) ∧
    ∀ j < i, rate j ≤ (state.2.2 : ℝ) / trials + ε

private theorem SelectionInvariant.update {trials i : ℕ} {rate : ℕ → ℝ} {ε : ℝ}
    {state : ℕ × ℕ × ℕ} (hstate : SelectionInvariant trials rate ε i state)
    (successes : ℕ) (haccurate : |(successes : ℝ) / trials - rate i| ≤ ε) :
    SelectionInvariant trials rate ε (i + 1) (OracleComp.selectUpdate state successes) := by
  obtain ⟨hindex, hzero, hchosen, hall⟩ := hstate
  obtain ⟨hlower, hupper⟩ := abs_le.mp haccurate
  have htrials : (0 : ℝ) ≤ trials := by positivity
  dsimp only [SelectionInvariant, OracleComp.selectUpdate]
  split_ifs with hscore
  · have hcompare : (state.2.2 : ℝ) / trials ≤ successes / trials :=
      div_le_div_of_nonneg_right (by exact_mod_cast hscore) htrials
    refine ⟨by lia, by simp, fun _ => ⟨by simp; lia, ?_⟩, ?_⟩
    · simpa only [hindex] using (show (successes : ℝ) / trials ≤ rate i + ε by linarith)
    · intro j hj
      by_cases hji : j < i
      · have := hall j hji
        dsimp only
        linarith
      · have : j = i := by lia
        subst j
        dsimp only
        linarith
  · have hi : 0 < i := by
      by_contra h
      have hz := hzero (by lia)
      simp [hz] at hscore
    have hcompare : (successes : ℝ) / trials ≤ state.2.2 / trials :=
      div_le_div_of_nonneg_right (by exact_mod_cast (show successes ≤ state.2.2 by lia)) htrials
    obtain ⟨hchosenIndex, hchosenRate⟩ := hchosen hi
    refine ⟨by lia, by simp, fun _ => ⟨by simp; lia, hchosenRate⟩, ?_⟩
    intro j hj
    by_cases hji : j < i
    · exact hall j hji
    · have : j = i := by lia
      subst j
      linarith

/-- If every empirical probability is accurate except with probability `error`, selection loses
at most twice the tolerance relative to every candidate, except with probability `count * error`.
The returned index is in range on this same event. -/
theorem selectBest_error_le (count trials : ℕ) (hcount : 0 < count)
    (test : ℕ → ProbComp Bool) {ε error : ℝ} (herror : 0 ≤ error)
    (hestimate : ∀ i < count,
      ((eval (OracleComp.countTrue trials (test i))).toOuterMeasure {successes |
        ε ≤ |(successes : ℝ) / trials - (eval (test i) true).toReal|}).toReal ≤ error) :
    ((eval (OracleComp.selectBest count trials test)).toOuterMeasure {chosen |
      ¬ (chosen < count ∧ ∀ i < count,
        (eval (test i) true).toReal ≤ (eval (test chosen) true).toReal + 2 * ε)}).toReal ≤
      count * error := by
  let rate := fun i => (eval (test i) true).toReal
  have hrun := iterate_failure_toReal_le_mul count (OracleComp.selectStep trials test)
    (0, 0, 0) (SelectionInvariant trials rate ε)
    (by simp [SelectionInvariant]) herror (by
      intro i hi state hstate
      rw [OracleComp.selectStep, eval_map, PMF.toOuterMeasure_map_apply]
      rw [hstate.1]
      refine le_trans ?_ (hestimate i hi)
      apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      apply MeasureTheory.measure_mono
      intro successes hbad
      by_contra haccurate
      exact hbad (hstate.update successes (le_of_lt (lt_of_not_ge haccurate))))
  rw [OracleComp.selectBest, eval_map, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ hrun
  apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro state hbad hstate
  obtain ⟨_, _, hchosen, hall⟩ := hstate
  obtain ⟨hindex, hselected⟩ := hchosen hcount
  apply hbad
  refine ⟨hindex, fun i hi => ?_⟩
  have := hall i hi
  dsimp only [rate] at *
  linarith

/-- A polynomial trial budget selects within twice the requested inverse tolerance of the best
candidate, with one exponentially small failure term per candidate. -/
theorem selectBest_error_pow (count confidence inverseTolerance : ℕ) (hcount : 0 < count)
    (htolerance : 0 < inverseTolerance) (test : ℕ → ProbComp Bool) :
    ((eval (OracleComp.selectBest count
      ((confidence + 1) * inverseTolerance ^ 2) test)).toOuterMeasure
      {chosen | ¬ (chosen < count ∧ ∀ i < count,
        (eval (test i) true).toReal ≤
          (eval (test chosen) true).toReal + 2 / inverseTolerance)}).toReal ≤
      count * (1 / 2 : ℝ) ^ confidence := by
  simpa only [mul_one_div] using selectBest_error_le count
    ((confidence + 1) * inverseTolerance ^ 2) hcount test (by positivity)
    (fun i _ => countTrue_average_deviation_pow confidence inverseTolerance htolerance (test i))

end ProbComp

end Cslib
