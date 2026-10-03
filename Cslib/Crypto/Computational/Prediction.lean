/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Tactic.PPT

/-!
# Predicting a bit from a distinguishing test

The reduction supplies a trial bit to a test and returns that bit on acceptance, or its complement
on rejection. Averaging over a fresh fair trial turns the test's signed distinguishing gap into
prediction bias. The test may capture any public observation; neither the hidden bit nor a
decision about masking that bit is an input to the predictor.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Game 5 and the following prediction reduction.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use acceptance of the real label as the positive sign convention.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Predict a trial bit on acceptance and its complement on rejection. -/
def trialPredictor (test : Bool → ProbComp Bool) (trial : Bool) : ProbComp Bool :=
  (fun accept => if accept then trial else !trial) <$> test trial

/-- A fresh fair trial gives a single uniform predictor from a bit test. -/
noncomputable def bitPredictor (test : Bool → ProbComp Bool) : ProbComp Bool := do
  let trial ← OracleComp.uniform Bool
  trialPredictor test trial

/-- The two fixed trials recover the test's signed distinguishing gap. -/
theorem trialPredictor_gap (test : Bool → ProbComp Bool) (truth : Bool) :
    winProbability (test truth) -
        (winProbability (test false) + winProbability (test true)) / 2 =
      (winProbability ((fun guess => guess == truth) <$> trialPredictor test false) +
        winProbability ((fun guess => guess == truth) <$> trialPredictor test true) - 1) / 2 := by
  cases truth with
  | false => simp [trialPredictor]; ring
  | true =>
    simp only [beq_true, trialPredictor, Bool.not_false, Bool.ite_true_right,
      Bool.decide_eq_true, Bool.or_false, Functor.map_map, Bool.not_true, Bool.ite_false_right,
      Bool.and_true, id_map']
    rw [winProbability_not]
    ring

/-- Randomizing the trial averages the two fixed predictors' correctness probabilities. -/
theorem winProbability_bitPredictor (test : Bool → ProbComp Bool) (truth : Bool) :
    winProbability ((fun guess => guess == truth) <$> bitPredictor test) =
      (winProbability ((fun guess => guess == truth) <$> trialPredictor test false) +
        winProbability ((fun guess => guess == truth) <$> trialPredictor test true)) / 2 := by
  simp only [bitPredictor, map_bind, OracleComp.uniform, winProbability_sample_bind]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]
  ring

/-- The randomized predictor's bias equals the gap between the real label and a fair label. -/
theorem bitPredictor_bias (test : Bool → ProbComp Bool) (truth : Bool) :
    winProbability ((fun guess => guess == truth) <$> bitPredictor test) - 1 / 2 =
      winProbability (test truth) -
        (winProbability (test false) + winProbability (test true)) / 2 := by
  rw [winProbability_bitPredictor, trialPredictor_gap]
  ring

/-- Trial prediction preserves strict PPT, charging for the supplied bit and the complete test. -/
theorem trialPredictor_isPPT {α : Type} {input : α ↪ Word}
    {test : α → Bool → ProbComp Bool} {trial : α → Bool}
    (htest : IsPPTOn (pairEncoding input boolEncoding) boolEncoding
      (fun pair => test pair.1 pair.2))
    (htrial : IsPolyTime input (fun a => [trial a])) :
    IsPPTOn input boolEncoding (fun a => trialPredictor (test a) (trial a)) := by
  unfold trialPredictor
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptTrialPredictor : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``trialPredictor, ``trialPredictor_isPPT)]

/-- A certified test gives a strict PPT predictor with no length-dependent choice of trial. -/
theorem bitPredictor_isPPT {α : Type} {input : α ↪ Word}
    {test : α → Bool → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding input boolEncoding) boolEncoding
      (fun pair => test pair.1 pair.2)) :
    IsPPTOn input boolEncoding (fun a => bitPredictor (test a)) := by
  unfold bitPredictor
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptBitPredictor : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``bitPredictor, ``bitPredictor_isPPT)]

end Cslib.Crypto
