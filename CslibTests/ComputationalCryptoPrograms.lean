/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Tactic.PPT

/-!
# Word programs with synthesized efficiency proofs

The client examples use ordinary list programs and value-level invariants. Their certificates
refer to the existing machine-based complexity predicate without exposing machine witnesses.
-/

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

noncomputable section

/-- A sampled word can be processed by an ordinary deterministic program. -/
def sampledParity (n : ℕ) (_ : Word) : ProbComp Bool := do
  let word ← OracleComp.sampleBits n
  return word.foldl Bool.xor false

theorem sampledParity_isPPT : IsPPT boolEncoding sampledParity := by
  unfold sampledParity
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
