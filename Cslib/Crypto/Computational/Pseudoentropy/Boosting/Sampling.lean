/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.UniformNat
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Progress
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Vote
public import Cslib.Languages.Probabilistic.Concentration

/-!
# Sampling the soft weights of hard-core boosting

Votes are ordinary Boolean words. The number of correct votes, the threshold, and the dyadic
rate determine a natural-number numerator. Saturating subtraction implements both clipped
regions of the real weight curve; neither real arithmetic nor rejection sampling is needed.
`sampleWeight_isPPT` certifies the whole program through the shared programming combinators.
`sampleWeight_density_deviation` estimates the source-averaged density with a Hoeffding bound,
using a natural success counter and independent source examples.

Each call draws a fresh coin. An implementation of a random set must additionally cache answers
to repeated membership queries; this program alone is not such a stateful oracle.

## References

* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
  the measure in Figure 1 and its sampled implementation in Claims 2.6–2.8.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  We realize dyadic rates exactly with finite fair-bit sampling.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability

/-- The numerator of a clipped linear weight, computed entirely with natural numbers.
The excess of correct over incorrect votes is `2 * votes.count truth - votes.length` in
integer arithmetic; the inner natural subtraction keeps only its excess over the threshold. -/
def weightNumerator (denominator rateNumerator threshold : ℕ) (votes : Word) (truth : Bool) : ℕ :=
  denominator - rateNumerator * (2 * votes.count truth - (votes.length + threshold))

/-- Every generated numerator is within its denominator, including malformed parameter choices. -/
theorem weightNumerator_le (denominator rateNumerator threshold : ℕ) (votes : Word) (truth : Bool) :
    weightNumerator denominator rateNumerator threshold votes truth ≤ denominator :=
  Nat.sub_le _ _

/-- Saturating natural arithmetic exactly implements the clipped real-valued weight curve. -/
theorem weightNumerator_div (denominator rateNumerator threshold : ℕ)
    (hdenominator : 0 < denominator) (votes : Word) (truth : Bool) :
    (weightNumerator denominator rateNumerator threshold votes truth : ℝ) / denominator =
      weight (rateNumerator / denominator) (voteMargin votes truth - threshold) := by
  unfold voteMargin
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  by_cases hlow : 2 * votes.count truth ≤ votes.length + threshold
  · have hm : 2 * (votes.count truth : ℝ) - votes.length - threshold ≤ 0 := by
      have h : 2 * (votes.count truth : ℝ) ≤ votes.length + threshold := by exact_mod_cast hlow
      linarith
    rw [weight_of_nonpos (by positivity) hm]
    simp [weightNumerator, Nat.sub_eq_zero_of_le hlow, hdenominator.ne']
  · let excess := 2 * votes.count truth - (votes.length + threshold)
    have hexcess : (excess : ℝ) =
        2 * (votes.count truth : ℝ) - votes.length - threshold := by
      dsimp only [excess]
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    change (↑(denominator - rateNumerator * excess) : ℝ) / denominator = _
    rw [← hexcess, weight]
    have hnonneg : 0 ≤ (rateNumerator : ℝ) / denominator * excess := by positivity
    rw [min_eq_right (max_le (by norm_num) (by linarith))]
    by_cases hcap : rateNumerator * excess ≤ denominator
    · have hratio : (rateNumerator : ℝ) / denominator * excess ≤ 1 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hd).mpr
        simp only [one_mul]
        exact_mod_cast hcap
      rw [max_eq_right (by linarith), Nat.cast_sub hcap, Nat.cast_mul]
      field_simp
    · have hratio : 1 ≤ (rateNumerator : ℝ) / denominator * excess := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hd).mpr
        simp only [one_mul]
        exact_mod_cast (show denominator ≤ rateNumerator * excess by lia)
      rw [max_eq_left (by linarith), Nat.sub_eq_zero_of_le (by lia)]
      simp

/-- The weight's natural numerator is polynomial time in its complete encoded input. -/
theorem weightNumerator_isPolyTime {α : Type} {input : α ↪ Word}
    {denominator rateNumerator threshold : α → ℕ} {votes : α → Word} {truth : α → Bool}
    (hdenominator : IsPolyTime input (fun a => unaryEncoding (denominator a)))
    (hrate : IsPolyTime input (fun a => unaryEncoding (rateNumerator a)))
    (hthreshold : IsPolyTime input (fun a => unaryEncoding (threshold a)))
    (hvotes : IsPolyTime input votes) (htruth : IsPolyTime input (fun a => [truth a])) :
    IsPolyTime input (fun a => unaryEncoding
      (weightNumerator (denominator a) (rateNumerator a) (threshold a) (votes a) (truth a))) := by
  unfold weightNumerator
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] weightNumerator_isPolyTime

/-- Sample a fresh membership coin with the soft weight of this vote word. -/
noncomputable def sampleWeight (bound rateNumerator threshold : ℕ) (votes : Word) (truth : Bool) :
    ProbComp Bool :=
  sampleDyadicCoin bound (weightNumerator (dyadicSize bound) rateNumerator threshold votes truth)

/-- The program's acceptance probability is exactly the soft weight used in the potential proof. -/
theorem eval_sampleWeight_true (bound rateNumerator threshold : ℕ) (votes : Word) (truth : Bool) :
    (ProbComp.eval (sampleWeight bound rateNumerator threshold votes truth) true).toReal =
      weight (rateNumerator / dyadicSize bound) (voteMargin votes truth - threshold) := by
  rw [sampleWeight, eval_sampleDyadicCoin_true_toReal,
    Nat.min_eq_right (weightNumerator_le _ _ _ _ _)]
  exact weightNumerator_div _ _ _ (dyadicSize_pos bound) votes truth

/-- Sampling a source example and then its weight coin accepts with exactly the soft density. -/
theorem sampleWeight_density {α : Type*} [Fintype α] (source : PMF α)
    (bound rateNumerator threshold : ℕ) (votes : α → Word) (truth : α → Bool) :
    ((source.bind (fun x => ProbComp.eval
      (sampleWeight bound rateNumerator threshold (votes x) (truth x)))) true).toReal =
      density source (rateNumerator / dyadicSize bound)
        (fun x => voteMargin (votes x) (truth x) - threshold) := by
  rw [Cslib.Probability.PMF.bind_apply_toReal]
  simp only [eval_sampleWeight_true, density]

/-- Repeated source examples and fresh weight coins estimate the soft density. The executable
counter uses natural numbers; the empirical fraction occurs only in its specification. -/
theorem sampleWeight_density_deviation {α : Type} [Fintype α] (source : ProbComp α)
    (bound rateNumerator threshold : ℕ) (votes : α → Word) (truth : α → Bool)
    (count : ℕ) (hcount : 0 < count) {ε : ℝ} (hε : 0 ≤ ε) :
    ((ProbComp.eval (OracleComp.countTrue count (source >>= fun x =>
      sampleWeight bound rateNumerator threshold (votes x) (truth x)))).toOuterMeasure
        {successes | ε ≤ |(successes : ℝ) / count -
          density (ProbComp.eval source) (rateNumerator / dyadicSize bound)
            (fun x => voteMargin (votes x) (truth x) - threshold)|}).toReal ≤
      2 * Real.exp (-2 * count * ε ^ 2) := by
  simpa only [ProbComp.eval_bind, sampleWeight_density] using
    ProbComp.countTrue_average_deviation count hcount
      (source >>= fun x => sampleWeight bound rateNumerator threshold (votes x) (truth x)) hε

/-- Runtime-dependent parameters, votes, and labels compose to a uniform strict PPT sampler. -/
theorem sampleWeight_isPPT {α : Type} {input : α ↪ Word}
    {bound rateNumerator threshold : α → ℕ} {votes : α → Word} {truth : α → Bool}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hrate : IsPolyTime input (fun a => unaryEncoding (rateNumerator a)))
    (hthreshold : IsPolyTime input (fun a => unaryEncoding (threshold a)))
    (hvotes : IsPolyTime input votes) (htruth : IsPolyTime input (fun a => [truth a])) :
    IsPPTOn input boolEncoding (fun a =>
      sampleWeight (bound a) (rateNumerator a) (threshold a) (votes a) (truth a)) := by
  unfold sampleWeight
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptWeight : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``sampleWeight, ``sampleWeight_isPPT)]

end Cslib.Crypto.Pseudoentropy.Boosting
