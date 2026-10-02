/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Tactic.PPT

/-!
# Word programs with synthesized efficiency proofs

The client examples use ordinary list programs and value-level invariants. Their certificates
refer to the existing machine-based complexity predicate without exposing machine witnesses.
-/

public section

namespace CslibTests.ComputationalCryptoPrograms

open Cslib Cslib.Probability

/-- A composed word program needs only the registered primitive contracts. -/
def prepare (word : Word) : Word := word.filter id ++ word.tail.map not

theorem prepare_isPolyTime : IsPolyTime wordEncoding prepare := by
  unfold prepare
  polytime

/-- The loop count and the body are both certified; intermediate words only shrink. -/
theorem clear_isPolyTime :
    IsPolyTime wordEncoding (fun word : Word => List.tail^[word.length] word) := by
  polytime

/-- Local certificates are reused when a program calls a client-supplied algorithm. -/
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPolyTime wordEncoding (fun word => (f word).tail ++ (f word).map not) := by
  polytime

/-- Ordinary nested calls reuse both local certificates. -/
example (f g : Word → Word) (hf : IsPolyTime wordEncoding f) (hg : IsPolyTime wordEncoding g) :
    IsPolyTime wordEncoding (fun word => g (f word)) := by
  polytime

/-- The predictor's answer convention is efficient, including an empty answer. -/
example (evaluate : Word → Word) (hevaluate : IsPolyTime wordEncoding evaluate) :
    IsPolyTime wordEncoding (fun input => [(evaluate input).headD false]) := by
  polytime

/-- A Boolean accumulator gives an efficient parity computation through the finite-fold rule. -/
def parity (word : Word) : Bool := word.foldl Bool.xor false

theorem parity_isPolyTime : IsPolyTime wordEncoding (fun word => [parity word]) := by
  unfold parity
  polytime

/-- Calls can prepare every field of a nested argument tuple without exposing its encoding. -/
example (combine : Word → Word → Word → Word)
    (hcombine : IsPolyTime (pairEncoding wordEncoding (pairEncoding wordEncoding wordEncoding))
      (fun input => combine input.1 input.2.1 input.2.2)) :
    IsPolyTime wordEncoding (fun word => combine word.reverse word.tail word ++ word) := by
  fail_if_success (clear hcombine; polytime)
  polytime

/-- Word comparison checks lengths as well as bits, and still requires the supplied algorithm. -/
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPolyTime wordEncoding (fun word => [f word == word.tail]) := by
  fail_if_success (clear hf; polytime)
  polytime

/-- A fold can construct a growing accumulator using ordinary list syntax. -/
example : IsPolyTime wordEncoding (fun word : Word =>
    word.foldl (fun reversed bit => bit :: reversed) []) := by
  polytime

/-- The tactic infers constant growth from list constructors inside a nontrivial fold. -/
example : IsPolyTime wordEncoding (fun word : Word =>
    word.foldl (fun output bit => output.map not ++ [bit]) []) := by
  polytime

/-- Higher-order folds reuse a local step certificate and its growth contract. -/
example (step : Word → Bool → Word) (growth : ℕ)
    (hstep : IsPolyTime (pairEncoding wordEncoding boolEncoding)
      (fun pair => step pair.1 pair.2))
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    IsPolyTime wordEncoding (fun word => word.foldl step word) := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

/-- Mapping a client-supplied algorithm requires and reuses its certificate. -/
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPolyTime (listEncoding wordEncoding) (fun values =>
      listEncoding wordEncoding (values.map f)) := by
  fail_if_success (clear hf; polytime)
  polytime

/-- Collection combinators compose without separate bounds on the intermediate list. -/
example : IsPolyTime (listEncoding wordEncoding) (fun values =>
    listEncoding wordEncoding ((values.map (fun word => word.reverse ++ [true])).reverse)) := by
  polytime

/-- The decoder's one-bit extension of every guess is an ordinary `flatMap`. -/
example : IsPolyTime (listEncoding wordEncoding) (fun values =>
    listEncoding wordEncoding (values.flatMap (fun word => [false :: word, true :: word]))) := by
  polytime

/-- Coordinatewise mask operations compose with ordinary list programs. -/
example : IsPolyTime coinInputEncoding (fun pair =>
    pair.1.zipWith Bool.xor pair.2.reverse) := by
  polytime

/-- A mapped callback can capture the input's saved coins and call a supplied evaluator. -/
example (evaluate : Word → Word → Word)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2)) :
    IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun pair =>
      listEncoding wordEncoding (pair.2.map (fun query => evaluate pair.1 query))) := by
  fail_if_success (clear hevaluate; polytime)
  polytime

/-- A `flatMap` can capture runtime data while generating several outputs per element. -/
example : IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun pair =>
    listEncoding wordEncoding (pair.2.flatMap (fun word => [pair.1 ++ word, word]))) := by
  polytime

/-- Nested maps retain both the original input and the enclosing callback's argument. -/
example : IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun pair =>
    listEncoding (listEncoding wordEncoding) (pair.2.map (fun mask =>
      pair.2.map (fun guess => pair.1 ++ mask ++ guess)))) := by
  polytime

/-- Boolean callbacks produce a word of votes directly, including captured evaluator calls. -/
example (evaluate : Word → Word → Word)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2)) :
    IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun pair =>
      pair.2.map (fun query => (evaluate pair.1 query).headD false)) := by
  polytime

/-- A word-producing callback can be flattened into one ordinary output word. -/
example : IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun pair =>
    pair.2.flatMap (fun word => pair.1 ++ word)) := by
  polytime

/-- A collection predicate can capture a target word and call a certified function. -/
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding)) (fun input =>
      listEncoding wordEncoding (input.2.filter (fun word => f word == input.1))) := by
  fail_if_success (clear hf; polytime)
  polytime

/-- Both the prefix bit and the mapped word are runtime values. -/
example : IsPolyTime (pairEncoding boolEncoding wordEncoding) (fun pair =>
    pair.2.map (Bool.xor pair.1)) := by
  polytime

/-- Saved coins and a prepared argument can be passed to a certified two-argument routine. -/
example (evaluate : Word → Word → Word)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2)) :
    IsPolyTime coinInputEncoding (fun pair =>
      [(evaluate pair.1 (pair.2 ++ [true])).headD false]) := by
  polytime

/-- One prefix invariant establishes the fold's value and its polynomial-time certificate. -/
theorem reverseFold_spec :
    IsPolyTime wordEncoding (fun word : Word => word.foldl (fun output bit => bit :: output) []) ∧
      ∀ word : Word, word.foldl (fun output bit => bit :: output) [] = word.reverse := by
  have hstep : IsPolyTime (pairEncoding wordEncoding boolEncoding)
      (fun pair => pair.2 :: pair.1) := by polytime
  simpa [wordEncoding] using (isPolyTime_input wordEncoding).foldl_spec
    (stateEncoding := wordEncoding) (step := fun output bit => bit :: output)
    (isPolyTime_const wordEncoding []) hstep
    (fun _ consumed output => output = consumed.reverse)
    (by simp)
    (by intro original consumed output bit _ h; simp [h])
    (size := id) (by fun_prop)
    (by intro original consumed output hprefix h; simpa [wordEncoding, h] using hprefix.length_le)

/-- Polynomial unary arithmetic and logarithms compose from the security parameter. -/
example (degree : ℕ) : IsPolyTime parameterEncoding (fun pair =>
    List.replicate (Nat.log 2 (2 * pair.1 * (pair.1 + 1) ^ (2 * degree) + 1) + 1) true) := by
  polytime

/-- A variable exponent cannot be treated as a fixed-degree polynomial computation. -/
example : True := by
  fail_if_success
    have : IsPolyTime unaryEncoding (fun n => List.replicate (2 ^ n) true) := by polytime
  trivial

/-- Runtime slicing and branching charge for the computed indices and both branch algorithms. -/
example : IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun pair =>
    if pair.1 < pair.2.length then (pair.2.drop pair.1).take pair.1
    else List.replicate pair.1 false) := by
  polytime

/-- Range generation composes with arithmetic on the security parameter and data lengths. -/
example : IsPolyTime parameterEncoding (fun pair =>
    listEncoding unaryEncoding (List.range (pair.1 + pair.2.length))) := by
  polytime

/-- Both callbacks in a runtime conditional need certificates. -/
example (yes no : Word → Word) (hyes : IsPolyTime wordEncoding yes)
    (hno : IsPolyTime wordEncoding no) : IsPolyTime wordEncoding (fun word =>
      if word.headD false then yes word else no word) := by
  fail_if_success (clear hno; polytime)
  polytime

/-- Strict majority, including the tie convention, is an ordinary word program. -/
example : IsPolyTime wordEncoding (fun votes =>
    [decide (votes.length < 2 * (votes.filter id).length)]) := by
  polytime

/-- Polynomial bounds on compound costs reuse Mathlib's function-property automation. -/
example (size : ℕ → ℕ) (hsize : PolynomiallyBounded size) (c d : ℕ) :
    PolynomiallyBounded (fun n => c * (size n + 1) ^ d + n * size n + 7) := by
  fun_prop

/-- Polynomial-bound automation does not turn a variable exponent into a fixed degree. -/
example : True := by
  fail_if_success
    have : PolynomiallyBounded (fun n => 2 ^ n) := by fun_prop
  trivial

noncomputable section

/-- A sampled word can be processed by an ordinary deterministic program. -/
def sampledParity (n : ℕ) (_ : Word) : ProbComp Bool := do
  let word ← OracleComp.sampleBits n
  return word.foldl Bool.xor false

theorem sampledParity_isPPT : IsPPT boolEncoding sampledParity := by
  unfold sampledParity
  ppt

/-- Multiple random draws retain captured inputs and allow runtime-dependent sample lengths. -/
example : IsPPT wordEncoding (fun n input => do
    let flip ← OracleComp.uniform Bool
    let coins ← OracleComp.sample (uniformBits (n + input.length))
    return input ++ coins.map (Bool.xor flip)) := by
  ppt

/-- Runtime branching and a captured random tape compose a supplied algorithm's certificate. -/
example (evaluate : Word → Word → Word)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2)) :
    IsPPT wordEncoding (fun n input =>
      if input.length = n then do
        let coins ← OracleComp.sample (uniformBits (n + input.length))
        return evaluate coins input
      else pure []) := by
  fail_if_success (clear hevaluate; ppt)
  ppt

/-- Probabilistic programs can return typed tuples as well as words. -/
example : IsPPT (pairEncoding boolEncoding wordEncoding) (fun n input => do
    let flip ← OracleComp.uniform Bool
    let coins ← OracleComp.sampleBits (n + input.length)
    return (flip, coins ++ input)) := by
  ppt

/-- Typed probabilistic calls prepare their arguments from captured runtime data. -/
example (program : Word → Word → ProbComp Bool)
    (hprogram : IsPPTOn coinInputEncoding boolEncoding (fun pair => program pair.1 pair.2)) :
    IsPPT boolEncoding (fun n input => do
      let coins ← OracleComp.sampleBits n
      program coins (input ++ coins)) := by
  fail_if_success (clear hprogram; ppt)
  ppt

/-- The public security parameter and auxiliary input are available to deterministic code. -/
example : IsPPT wordEncoding (fun n input =>
    pure (List.replicate n true ++ input.tail)) := by
  ppt

/-- Calling an adversary on a freshly sampled word composes its existing certificate. -/
example (adversary : ℕ → Word → ProbComp Bool) (h : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (fun n _ => do
      let word ← OracleComp.sampleBits n
      adversary n word) := by
  ppt

/-- A missing adversary certificate is not synthesized from its Lean function type. -/
example (adversary : ℕ → Word → ProbComp Bool) (h : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding adversary := by
  fail_if_success (clear h; ppt)
  exact h

end

/-- A growing loop uses one local invariant for its output length and its polynomial-time proof. -/
theorem appendLoop_spec :
    IsPolyTime wordEncoding (fun word : Word =>
      (fun current => current ++ [true])^[word.length] word) ∧
      ∀ word : Word, ((fun current => current ++ [true])^[word.length] word).length =
        2 * word.length := by
  have hstep : IsPolyTime wordEncoding (fun word => word ++ [true]) := by polytime
  have h := (isPolyTime_input wordEncoding).iterate_spec
    (isPolyTime_unaryLength wordEncoding) hstep
    (fun original index current => current.length = original.length + index)
    (by simp [wordEncoding])
    (by intro original index current _ h; simp [h, Nat.add_assoc])
    ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id)
    (by intro original index current hi h; simp [wordEncoding] at hi ⊢; lia)
  refine ⟨h.1, fun word => ?_⟩
  simpa [wordEncoding, two_mul] using h.2 word

/-- Proof search must not invent an efficiency certificate for an arbitrary function. -/
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) : IsPolyTime wordEncoding f := by
  fail_if_success (clear hf; polytime)
  exact hf

/-- A fold whose accumulator doubles at every step is outside the finite-state rule. -/
example : True := by
  fail_if_success
    have : IsPolyTime wordEncoding (fun word : Word =>
        word.foldl (fun current _ => current ++ current) [true]) := by
      polytime
  trivial

end CslibTests.ComputationalCryptoPrograms
