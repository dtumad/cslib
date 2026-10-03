/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Encoding
public import Cslib.Computability.Probabilistic.Iteration
public import Mathlib.Data.Nat.Log

/-!
# Polynomial-time unary arithmetic

Unary encodings account for the complete size of natural-number inputs and outputs. Arithmetic
certificates compose through the ordinary program interface. Multiplication and subtraction reuse
bounded iteration, fixed powers reuse multiplication, and the base-two logarithm uses a halving
loop. Its invariant proves correctness and bounds the intermediate state.
-/

@[expose] public section

namespace Cslib.Probability

open Automata

variable {α : Type} {encode : α → Word} {f g : α → ℕ}

/-- Write any fixed bit an efficiently computed number of times. -/
theorem IsPolyTime.replicate (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (bit : Bool) : IsPolyTime encode (fun a => List.replicate (f a) bit) := by
  simpa only [List.map_replicate] using hf.map (fun _ => bit)

/-- Add two efficiently computed unary natural numbers. -/
theorem IsPolyTime.unary_add
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => List.replicate (f a + g a) true) := by
  simpa only [List.replicate_add] using hf.append hg

/-- Repeated addition computes a unary product in polynomial time. -/
theorem isPolyTime_unary_mul : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
    (fun pair => List.replicate (pair.1 * pair.2) true) := by
  let advance (state : ℕ × ℕ) := (state.1, state.2 + state.1)
  have hfirst := isPolyTime_fst unaryEncoding unaryEncoding
  have hsecond := isPolyTime_snd unaryEncoding unaryEncoding
  have hstep : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun state => pairEncoding unaryEncoding unaryEncoding (advance state)) :=
    hfirst.pair (left := unaryEncoding) (right := unaryEncoding) (hsecond.unary_add hfirst)
  have htrace (n index : ℕ) : advance^[index] (n, 0) = (n, index * n) := by
    induction index with
    | zero => simp
    | succ index ih => simp [Function.iterate_succ_apply', advance, ih, Nat.add_mul]
  have h := (hfirst.pair (left := unaryEncoding) (right := unaryEncoding)
    (g := fun _ => 0) (isPolyTime_const _ [])).iterate_encoded
    (stateEncoding := pairEncoding unaryEncoding unaryEncoding) (step := advance)
    hsecond hstep (size := fun n => 2 * n + n * n + 1) (by fun_prop) (by
      intro pair index hi
      rw [htrace]
      simp only [length_pairEncoding, unaryEncoding_apply, List.length_replicate]
      have hproduct := Nat.mul_le_mul
        (show index ≤ 2 * pair.1 + pair.2 + 1 by lia)
        (show pair.1 ≤ 2 * pair.1 + pair.2 + 1 by lia)
      lia)
  simpa only [htrace, unaryEncoding_apply, Nat.mul_comm] using h.snd

/-- Multiply two efficiently computed unary natural numbers. -/
theorem IsPolyTime.unary_mul
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => List.replicate (f a * g a) true) :=
  isPolyTime_unary_mul.comp_pair (left := unaryEncoding) (right := unaryEncoding)
    (f := fun m n => List.replicate (m * n) true) hf hg

/-- Raise an efficiently computed unary natural number to a fixed power. -/
theorem IsPolyTime.unary_pow (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (degree : ℕ) : IsPolyTime encode (fun a => List.replicate (f a ^ degree) true) := by
  induction degree with
  | zero => simpa using isPolyTime_const encode [true]
  | succ degree ih => simpa only [pow_succ] using ih.unary_mul hf

/-- Truncated unary subtraction is a length-nonincreasing loop. -/
theorem IsPolyTime.unary_sub
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => List.replicate (f a - g a) true) := by
  simpa only [List.tail_iterate, List.drop_replicate] using
    hf.iterate_of_length_le (step := List.tail) hg (isPolyTime_tail wordEncoding)
      (by intro word; simp)

/-- Cap an efficiently computed unary number by another efficiently computed bound. -/
theorem IsPolyTime.unary_min
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => List.replicate (min (f a) (g a)) true) := by
  simpa only [Nat.sub_sub_eq_min] using hf.unary_sub (hf.unary_sub hg)

/-- Compare efficiently computed unary numbers, returning one Boolean bit. -/
theorem IsPolyTime.unary_lt
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => [decide (f a < g a)]) := by
  have heq (m n : ℕ) : (List.replicate (n - m) true).headD false = decide (m < n) := by
    cases hsub : n - m with
    | zero =>
      have h : ¬m < n := by lia
      simp [h]
    | succ k =>
      have h : m < n := by lia
      simp [h, List.replicate_succ]
  simpa only [heq] using (hg.unary_sub hf).headD false

/-- Non-strict comparison of efficiently computed unary numbers. -/
theorem IsPolyTime.unary_le
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => [decide (f a ≤ g a)]) := by
  simpa only [List.map_cons, List.map_nil, ← decide_not, not_lt] using
    (hg.unary_lt hf).map not

/-- Test equality of efficiently computed unary numbers. -/
theorem IsPolyTime.unary_eq
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => [decide (f a = g a)]) := by
  have heq (m n : ℕ) : (!(decide (m < n)) && !(decide (n < m))) = decide (m = n) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    lia
  simpa only [heq] using
    ((hf.unary_lt hg).map not).bool₂ ((hg.unary_lt hf).map not) Bool.and

private def halve : DeterministicTransducer Bool Bool Bool where
  initial := false
  next keep _ := !keep
  output keep _ := if keep then [true] else []
  finish _ := []

/-- Discarding alternate unary digits computes division by two. -/
theorem isPolyTime_unary_div_two :
    IsPolyTime unaryEncoding (fun n => List.replicate (n / 2) true) := by
  have heval (n : ℕ) (keep : Bool) :
      halve.evalFrom keep (List.replicate n true) =
        List.replicate ((n + keep.toNat) / 2) true := by
    induction n generalizing keep with
    | zero => cases keep <;> rfl
    | succ n ih =>
      change (if keep then [true] else []) ++ halve.evalFrom (!keep) (List.replicate n true) = _
      rw [ih]
      cases keep <;> simp [Nat.add_assoc, List.replicate_succ]
  have h := halve.isPolyTime unaryEncoding
  change IsPolyTime unaryEncoding (fun n => halve.evalFrom false (List.replicate n true)) at h
  simpa only [heval, Bool.toNat_false, Nat.add_zero] using h

/-- Divide an efficiently computed unary natural number by two. -/
theorem IsPolyTime.unary_div_two (hf : IsPolyTime encode (fun a => List.replicate (f a) true)) :
    IsPolyTime encode (fun a => List.replicate (f a / 2) true) :=
  isPolyTime_unary_div_two.comp_encoded (encodeArg := unaryEncoding) hf

/-- Repeated halving divides by a power of two without constructing the divisor. -/
theorem IsPolyTime.unary_div_pow_two
    (hf : IsPolyTime encode (fun a => List.replicate (f a) true))
    (hg : IsPolyTime encode (fun a => List.replicate (g a) true)) :
    IsPolyTime encode (fun a => List.replicate (f a / 2 ^ g a) true) := by
  have hiterate (k n : ℕ) : (fun m : ℕ => m / 2)^[k] n = n / 2 ^ k := by
    induction k with
    | zero => simp
    | succ k ih => simp [Function.iterate_succ_apply', ih, Nat.div_div_eq_div_mul, pow_succ]
  simpa only [hiterate, unaryEncoding_apply] using
    hf.iterate_encoded_of_length_le (stateEncoding := unaryEncoding)
      hg isPolyTime_unary_div_two (by intro n; simpa using Nat.div_le_self n 2)

/-- Truncate an efficiently computed unary number to zero or one. -/
theorem IsPolyTime.unary_min_one (hf : IsPolyTime encode (fun a => List.replicate (f a) true)) :
    IsPolyTime encode (fun a => List.replicate (min (f a) 1) true) := by
  simpa only [List.take_replicate, Nat.min_comm] using hf.head

/-- Repeated halving computes the base-two logarithm, with the usual value zero at zero. One
invariant proves the answer and bounds the encoded loop state. The loop runs for at most `n`
iterations, so the uniform polynomial bound also covers small and zero inputs. -/
theorem isPolyTime_unary_log2 :
    IsPolyTime unaryEncoding (fun n => List.replicate (Nat.log 2 n) true) := by
  let measure (n : ℕ) := if n = 0 then 0 else Nat.log 2 n + 1
  have hmeasure (n : ℕ) : measure (n / 2) + min n 1 = measure n := by
    by_cases hn : n < 2
    · interval_cases n <;> norm_num [measure]
    · have hn0 : n ≠ 0 := by lia
      have hd0 : n / 2 ≠ 0 := by lia
      simp only [measure, ite_eq_right hn0, ite_eq_right hd0, Nat.min_eq_right (by lia : 1 ≤ n)]
      rw [Nat.log_of_one_lt_of_le (by decide : 1 < 2) (by lia : 2 ≤ n)]
  let advance (state : ℕ × ℕ) := (state.1 / 2, state.2 + min state.1 1)
  have hfirst := isPolyTime_fst unaryEncoding unaryEncoding
  have hsecond := isPolyTime_snd unaryEncoding unaryEncoding
  have hstep : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun state => pairEncoding unaryEncoding unaryEncoding (advance state)) :=
    hfirst.unary_div_two.pair (left := unaryEncoding) (right := unaryEncoding)
      (hsecond.unary_add hfirst.unary_min_one)
  have hloop := ((isPolyTime_input unaryEncoding).pair
    (left := unaryEncoding) (right := unaryEncoding) (g := fun _ => 0)
    (isPolyTime_const _ [])).iterate_encoded_spec
    (stateEncoding := pairEncoding unaryEncoding unaryEncoding) (step := advance)
    (isPolyTime_input unaryEncoding) hstep
    (fun n index state => state.1 ≤ n - index ∧ state.2 ≤ index ∧
      measure state.1 + state.2 = measure n)
    (by simp)
    (by
      intro n index state hi ⟨hremaining, hcount, hcorrect⟩
      have := hmeasure state.1
      dsimp only [advance]
      exact ⟨by lia, by lia, by lia⟩)
    (size := fun n => 3 * n + 1) (by fun_prop)
    (by
      intro n index state hi ⟨hremaining, hcount, _⟩
      simp only [length_pairEncoding, unaryEncoding_apply, List.length_replicate]
      lia)
  have hresult (n : ℕ) : (advance^[n] (n, 0)).2 - 1 = Nat.log 2 n := by
    obtain ⟨hremaining, _, hcorrect⟩ := hloop.2 n
    have hzero : (advance^[n] (n, 0)).1 = 0 := by lia
    rw [hzero] at hcorrect
    by_cases hn : n = 0 <;> simp_all [measure]
  simpa only [unaryEncoding_apply, List.tail_replicate, hresult] using hloop.1.snd.tail

/-- Compute the base-two logarithm of an efficiently computed unary number. -/
theorem IsPolyTime.unary_log2 (hf : IsPolyTime encode (fun a => List.replicate (f a) true)) :
    IsPolyTime encode (fun a => List.replicate (Nat.log 2 (f a)) true) :=
  isPolyTime_unary_log2.comp_encoded (encodeArg := unaryEncoding) hf

end Cslib.Probability
