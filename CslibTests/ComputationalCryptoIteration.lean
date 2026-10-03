/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Adaptive
public import Cslib.Computability.Probabilistic.UniformNat

/-!
# Adaptive probabilistic programs with one invariant

The example's next action depends on previous random choices: append a fresh bit when the
current first bit is true, and prepend it otherwise. A length invariant proves both the
resource bound and the final postcondition. The two-step distribution distinguishes this
adaptive process from independent repetition.

A second loop remembers whether a rare failure has happened and stops drawing once it has.
Its local error bound composes without assuming independent rounds.
-/

public section

namespace CslibTests.ComputationalCryptoIteration

open Cslib Cslib.Probability

noncomputable section

/-- Choose where to place the next sampled bit using the current random state. -/
def adaptiveStep (word : Word) : ProbComp Word := do
  let bit ← OracleComp.uniform Bool
  return if word.headD false then word ++ [bit] else bit :: word

theorem adaptiveStep_isPPT : IsPPTOn wordEncoding wordEncoding adaptiveStep := by
  unfold adaptiveStep
  ppt

private theorem adaptiveStep_length (word next : Word)
    (hnext : next ∈ (ProbComp.eval (adaptiveStep word)).support) :
    next.length = word.length + 1 := by
  simp only [adaptiveStep, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
  obtain ⟨bit, _, rfl⟩ := hnext
  split <;> simp

/-- Run the adaptive update exactly `n` times. -/
def adaptiveLoop (n : ℕ) : ProbComp Word := OracleComp.iterate n adaptiveStep []

/-- One invariant certifies the loop's strict polynomial time and its exact final length. -/
theorem adaptiveLoop_spec : IsPPTOn unaryEncoding wordEncoding adaptiveLoop ∧
    ∀ n, ∀ word ∈ (ProbComp.eval (adaptiveLoop n)).support, word.length = n := by
  unfold adaptiveLoop
  exact IsPPTOn.iterate_spec (by polytime) (by polytime) adaptiveStep_isPPT
    (fun _ i word => word.length = i) (by simp)
    (by
      intro n i _ word hinvariant next hnext
      rw [adaptiveStep_length word next hnext, hinvariant])
    (size := id) (by fun_prop)
    (by intro n i word hi hinvariant; simpa [unaryEncoding, wordEncoding, hinvariant] using hi)

/-- The bounded-growth shortcut supplies the same efficiency certificate without a postcondition. -/
theorem adaptiveLoop_isPPT : IsPPTOn unaryEncoding wordEncoding adaptiveLoop := by
  unfold adaptiveLoop
  exact IsPPTOn.iterate_of_bounded_growth (by polytime) (by polytime) adaptiveStep_isPPT
    (growth := 1) (fun word next hnext => (adaptiveStep_length word next hnext).le)

/-- Both histories `false,true` and `true,false` end at `[true,false]`, giving mass `1/2`. -/
theorem adaptiveLoop_two : (ProbComp.eval (adaptiveLoop 2) [true, false]).toReal = 1 / 2 := by
  simp only [adaptiveLoop, OracleComp.iterate, adaptiveStep, ProbComp.eval_bind,
    ProbComp.eval_pure, OracleComp.uniform, ProbComp.eval_sample, PMF.pure_bind, PMF.bind_bind]
  norm_num [PMF.bind_apply, tsum_fintype, Fintype.sum_bool,
    PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- A failed run stays failed; otherwise a fresh draw fails with probability `1/16`. -/
def failureStep (failed : Bool) : ProbComp Bool :=
  if failed then pure true else sampleDyadicCoin 15 1

theorem failureStep_isPPT : IsPPTOn boolEncoding boolEncoding failureStep := by
  unfold failureStep
  ppt

/-- Recording failure never grows the Boolean state, so arbitrary unary loop counts are allowed. -/
theorem failureLoop_isPPT : IsPPTOn unaryEncoding boolEncoding
    (fun n => OracleComp.iterate n failureStep false) := by
  apply IsPPTOn.iterate_of_length_le (by polytime) (by polytime) failureStep_isPPT
  intro state next _
  simp [boolEncoding]

/-- A failure in any round has probability at most `n/16`, although later draws are skipped. -/
theorem failureLoop_error (n : ℕ) :
    ((ProbComp.eval (OracleComp.iterate n failureStep false)).toOuterMeasure
      {failed | failed ≠ false}).toReal ≤ n / 16 := by
  have hevent : {failed : Bool | failed ≠ false} = {true} := by ext failed; cases failed <;> simp
  have hsize : dyadicSize 15 = 16 := by decide
  have h := ProbComp.iterate_failure_toReal_le_mul n failureStep false
    (fun _ failed => failed = false) rfl (error := 1 / 16) (by norm_num)
    (by
      intro _ _ failed hfailed
      rw [hfailed, failureStep, ite_eq_right Bool.false_ne_true, hevent,
        PMF.toOuterMeasure_apply_singleton, eval_sampleDyadicCoin_true_toReal, hsize]
      norm_num)
  simpa only [div_eq_mul_inv, one_mul] using h

/-- The original input controls each round's sampling precision without becoming client state. -/
theorem capturedFailureLoop_isPPT : IsPPTOn unaryEncoding boolEncoding
    (fun n => OracleComp.iterate n
      (fun failed => if failed then pure true else sampleDyadicCoin ((n + 1) ^ 2) 1) false) := by
  have hstep : IsPPTOn (pairEncoding unaryEncoding boolEncoding) boolEncoding
      (fun pair => if pair.2 then pure true else sampleDyadicCoin ((pair.1 + 1) ^ 2) 1) := by ppt
  exact (IsPPTOn.iterate_with_spec (by polytime) (by polytime) hstep
    (fun _ _ _ => True) (by simp) (by simp)
    (size := fun _ => 1) (by fun_prop) (by simp [boolEncoding])).1

end

end CslibTests.ComputationalCryptoIteration
