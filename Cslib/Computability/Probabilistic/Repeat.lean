/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Repeat
public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Computability.Probabilistic.CoinTape
public import Cslib.Tactic.PPT

/-!
# Strict PPT bounded repetition

Repeating a closed PPT program an efficiently computed number of times is PPT. The proof uses
the existing saved-coin evaluator and deterministic collection combinators: one random tape is
split into equally sized independent blocks, then each block drives one evaluation. The client
program remains ordinary `OracleComp.replicate` and exposes none of this implementation.

The result encoding charges for the whole list. Output types need not be finite, and the
number of repetitions may depend on the complete input. The certificate covers count zero.
-/

@[expose] public section

namespace Cslib.Probability

/-- A runtime-bounded repetition of a uniform PPT program is uniformly strict PPT. -/
theorem IsPPTOn.replicate {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {program : α → ProbComp β} {count : α → ℕ}
    (hprogram : IsPPTOn input output program)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a))) :
    IsPPTOn input (listEncoding output) (fun a => OracleComp.replicate (count a) (program a)) := by
  obtain ⟨c, d, evaluate, hevaluate, hlaw⟩ := hprogram.exists_seeded_evaluator
  let budget (a : α) := c * ((input a).length + 1) ^ d
  let repeated (a : α) : ProbComp (List β) := do
    let coins ← OracleComp.sampleBits (count a * budget a)
    return (maskRows (count a) (budget a) coins).map (evaluate a)
  have hefficient : IsPPTOn input (listEncoding output) repeated := by
    unfold repeated budget
    ppt
  apply hefficient.congr
  intro a
  have hseed : ProbComp.eval (program a) =
      (PMF.uniformOfFintype (BitString (budget a))).map
        (fun bits => evaluate a (List.ofFn bits)) := by
    simpa only [uniformBits, PMF.map_comp, Function.comp_def, budget] using hlaw a
  rw [ProbComp.eval_replicate_of_uniform _ _ _ hseed]
  have hrows := congrArg (PMF.map (fun rows : Fin (count a) → BitString (budget a) =>
    List.ofFn (fun i => evaluate a (List.ofFn (rows i)))))
    (uniformBits_masksFromWord (count a) (budget a))
  rw [PMF.map_comp] at hrows
  simpa only [repeated, ProbComp.eval, OracleComp.eval_bind, OracleComp.eval_sampleBits,
    OracleComp.eval_pure, Function.comp_def, maskRows_eq_ofFn, List.map_ofFn, PMF.map]
    using hrows

/-- Boolean repetitions can use the ordinary word encoding directly. -/
theorem IsPPTOn.replicate_bool {α : Type} {input : α ↪ Word}
    {program : α → ProbComp Bool} {count : α → ℕ}
    (hprogram : IsPPTOn input boolEncoding program)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a))) :
    IsPPTOn input wordEncoding (fun a => OracleComp.replicate (count a) (program a)) := by
  simpa using (hprogram.replicate hcount).map (f := id)
    (isPolyTime_input (listEncoding boolEncoding)).decode_list_bool

/-- Counting successes in a polynomial number of independent trials is uniformly strict PPT. -/
theorem IsPPTOn.countTrue {α : Type} {input : α ↪ Word}
    {program : α → ProbComp Bool} {count : α → ℕ}
    (hprogram : IsPPTOn input boolEncoding program)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a))) :
    IsPPTOn input unaryEncoding (fun a => OracleComp.countTrue (count a) (program a)) := by
  have hrepeated := hprogram.replicate_bool hcount
  unfold OracleComp.countTrue
  ppt

/-- An empirical probability test is strict PPT when its trial, count, and rational threshold
are efficient. Cross-multiplication is charged through the unary arithmetic interface. -/
theorem IsPPTOn.testProbabilityLT {α : Type} {input : α ↪ Word}
    {program : α → ProbComp Bool} {count numerator denominator : α → ℕ}
    (hprogram : IsPPTOn input boolEncoding program)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hnumerator : IsPolyTime input (fun a => unaryEncoding (numerator a)))
    (hdenominator : IsPolyTime input (fun a => unaryEncoding (denominator a))) :
    IsPPTOn input boolEncoding (fun a =>
      OracleComp.testProbabilityLT (count a) (numerator a) (denominator a) (program a)) := by
  have htrials := hprogram.countTrue hcount
  unfold OracleComp.testProbabilityLT
  ppt

attribute [aesop safe apply (rule_sets := [PPT])]
  IsPPTOn.replicate IsPPTOn.replicate_bool IsPPTOn.countTrue

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptProbabilityTest : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``OracleComp.testProbabilityLT, ``IsPPTOn.testProbabilityLT)]

end Cslib.Probability
