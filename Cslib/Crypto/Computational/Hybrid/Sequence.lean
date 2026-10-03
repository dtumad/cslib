/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Game.Hybrid
public import Cslib.Computability.Probabilistic.Repeat
public import Cslib.Computability.Probabilistic.UniformNat

/-!
# Replacing independent samples one coordinate at a time

`sequenceHybrid` draws an initial segment from a replacement source and the remaining segment
from the original source. `spliceTest` samples the surrounding coordinates and inserts one
challenge into the resulting list. Its adjacent-game laws expose the usual hybrid proof without
tuple-index bookkeeping, and apply to arbitrary discrete sample types.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

variable {α : Type}

/-- Replace the initial `split` samples of an independent sequence. -/
def sequenceHybrid (replacement original : ProbComp α) (count split : ℕ) : ProbComp (List α) := do
  let front ← OracleComp.replicate split replacement
  let back ← OracleComp.replicate (count - split) original
  return front ++ back

/-- Simulate all surrounding coordinates and insert the supplied challenge between them. -/
def spliceTest (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) (challenge : α) : ProbComp Bool := do
  let front ← OracleComp.replicate before replacement
  let back ← OracleComp.replicate after original
  test (front ++ challenge :: back)

@[simp] theorem sequenceHybrid_zero (replacement original : ProbComp α) (count : ℕ) :
    sequenceHybrid replacement original count 0 = OracleComp.replicate count original := by
  simp [sequenceHybrid]

@[simp] theorem sequenceHybrid_self (replacement original : ProbComp α) (count : ℕ) :
    sequenceHybrid replacement original count count = OracleComp.replicate count replacement := by
  simp [sequenceHybrid]

/-- An original challenge supplies the first draw of the remaining original segment. -/
theorem eval_spliceTest_original (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval (original >>= spliceTest replacement original before after test) =
      ProbComp.eval (do
        let front ← OracleComp.replicate before replacement
        let back ← OracleComp.replicate (after + 1) original
        test (front ++ back)) := by
  simp only [spliceTest, OracleComp.replicate_succ, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- A replacement challenge supplies the last draw of the replacement segment. -/
theorem eval_spliceTest_replacement (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval (replacement >>= spliceTest replacement original before after test) =
      ProbComp.eval (do
        let front ← OracleComp.replicate (before + 1) replacement
        let back ← OracleComp.replicate after original
        test (front ++ back)) := by
  simp only [spliceTest, OracleComp.replicate_snoc, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def, List.append_assoc, List.singleton_append]
  exact PMF.bind_comm _ _ _

/-- Inserting an original challenge gives the earlier adjacent hybrid. -/
theorem eval_spliceTest_step_original (replacement original : ProbComp α) (count split : ℕ)
    (hsplit : split < count) (test : List α → ProbComp Bool) :
    ProbComp.eval (original >>= spliceTest replacement original split (count - split - 1) test) =
      ProbComp.eval (sequenceHybrid replacement original count split >>= test) := by
  rw [eval_spliceTest_original]
  have hcount : count - split - 1 + 1 = count - split := by lia
  simp only [hcount, sequenceHybrid, bind_assoc, pure_bind]

/-- Inserting a replacement challenge gives the later adjacent hybrid. -/
theorem eval_spliceTest_step_replacement (replacement original : ProbComp α) (count split : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval
        (replacement >>= spliceTest replacement original split (count - split - 1) test) =
      ProbComp.eval (sequenceHybrid replacement original count (split + 1) >>= test) := by
  rw [eval_spliceTest_replacement]
  simp only [sequenceHybrid, bind_assoc, pure_bind, Nat.sub_sub]

/-- Sample a coordinate uniformly from a dyadic range and run its adjacent-hybrid test.
Unused coordinates reject, so they contribute zero signed gap. -/
noncomputable def sequenceTest (replacement original : ProbComp α) (count : ℕ)
    (test : List α → ProbComp Bool) (challenge : α) : ProbComp Bool := do
  let split ← sampleDyadicIndex count
  if split < count then
    spliceTest replacement original split (count - split - 1) test challenge
  else pure false

private theorem eval_sequenceTest_bind (replacement original challenge : ProbComp α)
    (count : ℕ) (test : List α → ProbComp Bool) :
    ProbComp.eval (challenge >>= sequenceTest replacement original count test) =
      (PMF.uniformOfFintype (Fin (dyadicSize count))).bind (fun i =>
        if i.val < count then ProbComp.eval
          (challenge >>= spliceTest replacement original i.val (count - i.val - 1) test)
        else PMF.pure false) := by
  simp only [sequenceTest, ProbComp.eval_bind, eval_sampleDyadicIndex, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext i
  by_cases hi : i.val < count <;> simp only [hi, ite_true, ite_false, ProbComp.eval_pure,
    PMF.bind_const]

/-- One uniform single-sample distinguisher captures the entire sequence gap, with the linear
dyadic-range loss. The identity also covers zero repetitions. -/
theorem sequenceTest_gap (replacement original : ProbComp α) (count : ℕ)
    (test : List α → ProbComp Bool) :
    winProbability (OracleComp.replicate count original >>= test) -
        winProbability (OracleComp.replicate count replacement >>= test) =
      (dyadicSize count : ℝ) *
        (winProbability (original >>= sequenceTest replacement original count test) -
          winProbability (replacement >>= sequenceTest replacement original count test)) := by
  have horiginal := eval_sequenceTest_bind replacement original original count test
  have hreplacement := eval_sequenceTest_bind replacement original replacement count test
  simp only [eval_spliceTest_step_replacement] at hreplacement
  simp (config := { contextual := true }) only [eval_spliceTest_step_original] at horiginal
  have h := Game.winProbability_hybrid_average
    (fun i => ProbComp.eval (sequenceHybrid replacement original count i >>= test))
    count (dyadicSize count) (lt_dyadicSize count).le
  simpa only [sequenceHybrid_zero, sequenceHybrid_self, winProbability, horiginal, hreplacement]
    using h

/-- Efficient source programs and counts give an efficient independent hybrid sequence. -/
theorem sequenceHybrid_isPPT {Param : Type} {input : Param ↪ Word} {sample : α ↪ Word}
    {replacement original : Param → ProbComp α} {count split : Param → ℕ}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hsplit : IsPolyTime input (fun a => unaryEncoding (split a))) :
    IsPPTOn input (listEncoding sample)
      (fun a => sequenceHybrid (replacement a) (original a) (count a) (split a)) := by
  unfold sequenceHybrid
  ppt

/-- The inserted challenge and every simulated coordinate are charged by the strict PPT
certificate. The test may capture the complete original input. -/
theorem spliceTest_isPPT {Param : Type} {input : Param ↪ Word} {sample : α ↪ Word}
    {replacement original : Param → ProbComp α} {before after : Param → ℕ}
    {test : Param → List α → ProbComp Bool} {challenge : Param → α}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hbefore : IsPolyTime input (fun a => unaryEncoding (before a)))
    (hafter : IsPolyTime input (fun a => unaryEncoding (after a)))
    (htest : IsPPTOn (pairEncoding input (listEncoding sample)) boolEncoding
      (fun pair => test pair.1 pair.2))
    (hchallenge : IsPolyTime input (fun a => sample (challenge a))) :
    IsPPTOn input boolEncoding
      (fun a => spliceTest (replacement a) (original a) (before a) (after a)
        (test a) (challenge a)) := by
  unfold spliceTest
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSpliceTest : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``spliceTest, ``spliceTest_isPPT)]

/-- Random-coordinate hybrid reduction is uniformly strict PPT, including zero repetitions and
all rejected padding indices. -/
theorem sequenceTest_isPPT {Param : Type} {input : Param ↪ Word} {sample : α ↪ Word}
    {replacement original : Param → ProbComp α} {count : Param → ℕ}
    {test : Param → List α → ProbComp Bool} {challenge : Param → α}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (htest : IsPPTOn (pairEncoding input (listEncoding sample)) boolEncoding
      (fun pair => test pair.1 pair.2))
    (hchallenge : IsPolyTime input (fun a => sample (challenge a))) :
    IsPPTOn input boolEncoding
      (fun a => sequenceTest (replacement a) (original a) (count a) (test a) (challenge a)) := by
  unfold sequenceTest
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSequenceTest : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``sequenceTest, ``sequenceTest_isPPT)]

end Cslib.Crypto
