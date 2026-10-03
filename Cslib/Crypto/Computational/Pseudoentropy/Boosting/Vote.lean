/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Tactic.PolyTime
public import Cslib.Probability.PMF

/-!
# Vote words and the majority predictor

The executable majority predictor needs only the vote word. Labels are used by its training
test, which checks whether the signed number of correct votes is nonpositive. The probability
of this event bounds the prediction error, including ties and the empty collection.

## References

* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
  Claim 2.16. [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  We state the non-strict error bound that also covers ties.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability

/-- Correct votes minus incorrect votes, represented as a real number for the analysis. -/
def voteMargin (votes : Word) (truth : Bool) : ℝ :=
  2 * (votes.count truth : ℝ) - votes.length

/-- A correct prediction contributes one to the margin; an incorrect prediction subtracts one. -/
def signedVote (vote truth : Bool) : ℝ := if vote = truth then 1 else -1

@[simp] theorem abs_signedVote (vote truth : Bool) : |signedVote vote truth| = 1 := by
  unfold signedVote
  split <;> norm_num

@[simp] theorem voteMargin_nil (truth : Bool) : voteMargin [] truth = 0 := by
  simp [voteMargin]

/-- Adding a predictor updates the margin by its signed prediction. -/
theorem voteMargin_cons (vote : Bool) (votes : Word) (truth : Bool) :
    voteMargin (vote :: votes) truth = voteMargin votes truth + signedVote vote truth := by
  by_cases h : vote = truth <;> simp [voteMargin, signedVote, h] <;> ring

/-- Whether the correct votes fail to form a strict majority. This test uses natural arithmetic. -/
def nonpositiveMargin (votes : Word) (truth : Bool) : Bool :=
  decide (2 * votes.count truth ≤ votes.length)

/-- The ordinary majority of a vote word, breaking ties in favor of false. -/
def majority (votes : Word) : Bool := decide (votes.length < 2 * votes.count true)

/-- The training test agrees exactly with the real margin event used by the potential proof. -/
theorem nonpositiveMargin_eq_true (votes : Word) (truth : Bool) :
    nonpositiveMargin votes truth = true ↔ voteMargin votes truth ≤ 0 := by
  simp only [nonpositiveMargin, decide_eq_true_eq, voteMargin, sub_nonpos]
  norm_cast

private theorem count_false_add_true (votes : Word) :
    votes.count false + votes.count true = votes.length := by
  induction votes with
  | nil => rfl
  | cons bit votes ih => cases bit <;> simp_all <;> lia

/-- Reversing the label negates the signed margin of the same observable vote word. -/
@[simp] theorem voteMargin_not (votes : Word) (truth : Bool) :
    voteMargin votes (!truth) = -voteMargin votes truth := by
  have htotal : (votes.count false : ℝ) + votes.count true = votes.length := by
    exact_mod_cast count_false_add_true votes
  cases truth <;> simp only [Bool.not_true, Bool.not_false, voteMargin] <;> linarith

/-- The magnitude of the signed margin is at most the number of votes. -/
theorem abs_voteMargin_le (votes : Word) (truth : Bool) :
    |voteMargin votes truth| ≤ votes.length := by
  have hcount : (votes.count truth : ℝ) ≤ votes.length := by
    exact_mod_cast (show votes.count truth ≤ votes.length from List.count_le_length)
  have hnonneg : (0 : ℝ) ≤ votes.count truth := by positivity
  rw [abs_le]
  constructor <;> dsimp only [voteMargin] <;> linarith

/-- A positive signed margin guarantees that the executable majority predicts the label. -/
theorem majority_eq_of_pos {votes : Word} {truth : Bool} (hmargin : 0 < voteMargin votes truth) :
    majority votes = truth := by
  have hcount : votes.length < 2 * votes.count truth := by
    have h : (votes.length : ℝ) < 2 * (votes.count truth : ℝ) := by
      dsimp only [voteMargin] at hmargin
      linarith
    exact_mod_cast h
  have htotal := count_false_add_true votes
  cases truth <;> simp_all [majority]
  lia

/-- The nonpositive-margin event bounds the majority predictor's error on any source. -/
theorem majority_error_le {α : Type*} (source : PMF α) (votes : α → Word) (truth : α → Bool) :
    (source.toOuterMeasure {x | majority (votes x) ≠ truth x}).toReal ≤
      (source.toOuterMeasure {x | voteMargin (votes x) (truth x) ≤ 0}).toReal := by
  apply ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro x hwrong
  by_contra hpositive
  exact hwrong (majority_eq_of_pos (lt_of_not_ge hpositive))

/-- Sampling the training test accepts with exactly the nonpositive-margin probability. -/
theorem map_nonpositiveMargin_true {α : Type*} (source : PMF α)
    (votes : α → Word) (truth : α → Bool) :
    (source.map (fun x => nonpositiveMargin (votes x) (truth x))) true =
      source.toOuterMeasure {x | voteMargin (votes x) (truth x) ≤ 0} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, nonpositiveMargin_eq_true, Set.mem_ofPred_eq]

/-- The majority predictor is polynomial time in an efficiently computed vote word. -/
theorem majority_isPolyTime {α : Type} {input : α ↪ Word} {votes : α → Word}
    (hvotes : IsPolyTime input votes) :
    IsPolyTime input (fun a => [majority (votes a)]) := by
  unfold majority
  polytime

/-- The training test is polynomial time in the vote word and its supplied label. -/
theorem nonpositiveMargin_isPolyTime {α : Type} {input : α ↪ Word}
    {votes : α → Word} {truth : α → Bool}
    (hvotes : IsPolyTime input votes) (htruth : IsPolyTime input (fun a => [truth a])) :
    IsPolyTime input (fun a => [nonpositiveMargin (votes a) (truth a)]) := by
  unfold nonpositiveMargin
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])]
  majority_isPolyTime nonpositiveMargin_isPolyTime

end Cslib.Crypto.Pseudoentropy.Boosting
