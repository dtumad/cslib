/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Iteration
public import Cslib.Computability.Probabilistic.Parameter
public import Cslib.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

`polytime` composes proved efficiency rules for word programs. It handles constants, the input,
concatenation, fixed maps and substitutions, Boolean folds, filtering, head/tail, unary length,
and length-nonincreasing bounded loops. Local efficiency hypotheses are available as leaves.

All rules construct proofs of the machine-based `IsPolyTime` predicate. An unknown operation
requires a certificate; arbitrary Lean computation is not assigned unit cost. Loops that grow
their state can use `IsPolyTime.iterate_spec` with an explicit size invariant instead.
-/

public section

attribute [aesop norm simp (rule_sets := [PolyTime])]
  Cslib.Probability.boolEncoding
  Cslib.Probability.wordEncoding

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PolyTime])]
  Cslib.Probability.isPolyTime_const
  Cslib.Probability.isPolyTime_input
  Cslib.Probability.isPolyTime_flatMap
  Cslib.Probability.isPolyTime_map
  Cslib.Probability.isPolyTime_filter
  Cslib.Probability.isPolyTime_unaryLength
  Cslib.Probability.isPolyTime_tail
  Cslib.Probability.isPolyTime_head
  Cslib.Probability.isPolyTime_foldl_bool
  Cslib.Probability.isPolyTime_takeWhile
  Cslib.Probability.isPolyTime_dropWhile
  Cslib.Probability.isPolyTime_security
  Cslib.Probability.isPolyTime_auxiliaryInput

attribute [aesop safe apply (rule_sets := [PolyTime])]
  Cslib.Probability.IsPolyTime.append
  Cslib.Probability.IsPolyTime.flatMap
  Cslib.Probability.IsPolyTime.map
  Cslib.Probability.IsPolyTime.filter
  Cslib.Probability.IsPolyTime.unaryLength
  Cslib.Probability.IsPolyTime.tail
  Cslib.Probability.IsPolyTime.head
  Cslib.Probability.IsPolyTime.foldl_bool
  Cslib.Probability.IsPolyTime.iterate_of_length_le
  Cslib.Probability.IsPolyTime.takeWhile
  Cslib.Probability.IsPolyTime.dropWhile
  Cslib.Probability.IsPolyTime.parameterInput

attribute [aesop unsafe 50% apply (rule_sets := [PolyTime])]
  Cslib.Probability.IsPolyTime.comp

-- Aesop simplifies `headD` to this form before applying efficiency rules.
@[aesop safe apply (rule_sets := [PolyTime])]
private theorem headD_rule {α : Type} {encode : α → Cslib.Probability.Word}
    {f : α → Cslib.Probability.Word} (hf : Cslib.Probability.IsPolyTime encode f)
    (fallback : Bool) :
    Cslib.Probability.IsPolyTime encode (fun a => [(f a).head?.getD fallback]) := by
  simpa using hf.headD fallback

/-- Synthesize a polynomial-time word-program certificate from registered rules. -/
macro "polytime" : tactic => `(tactic| solve | aesop (rule_sets := [PolyTime]))
