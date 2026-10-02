/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Unary
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.UnaryRepeat
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Tactic.Linarith

/-!
# Constructing polynomial unary clocks

The coefficient and exponent belong to finite control. The input length is read by the machine,
and nested unary loops write the budget. No polynomial-sized word is given to the machine for free.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace PolynomialClock

/-- Emit a fixed number of true bits using a finite countdown in the control state. -/
@[simps] def constant (count : ℕ) : MultiTapeTM 0 Bool (Fin (count + 1)) where
  q₀ := ⟨count, by omega⟩
  tr remaining _ _ :=
    { inputTape := 0
      workTapes := Fin.elim0
      output := if remaining.val = 0 then none else some true
      state := if remaining.val = 0 then none
        else some ⟨remaining.val - 1, by have := remaining.isLt; omega⟩ }

theorem step_constant_succ (count remaining : ℕ) (h : remaining + 1 ≤ count)
    (input output : List Bool) :
    (constant count).step (wordsCfg input (some ⟨remaining + 1, by omega⟩) Fin.elim0 output) =
      wordsCfg input (some ⟨remaining, by omega⟩) Fin.elim0 (output ++ [true]) := by
  apply Cfg.ext_zero_tapes <;> simp [step, constant, wordsCfg, Action.apply]

theorem runFrom_constant_remaining (count : ℕ) (input : List Bool) (remaining : ℕ) :
    ∀ (h : remaining ≤ count) (output : List Bool),
      (constant count).runFrom
        (wordsCfg input (some ⟨remaining, by omega⟩) Fin.elim0 output) (remaining + 1) =
        wordsCfg input none Fin.elim0 (output ++ List.replicate remaining true) := by
  induction remaining with
  | zero =>
    intro h output
    rw [runFrom_one]
    apply Cfg.ext_zero_tapes <;> simp [step, constant, wordsCfg, Action.apply]
  | succ remaining ih =>
    intro h output
    rw [runFrom, Function.iterate_succ_apply, step_constant_succ count remaining h]
    change (constant count).runFrom
      (wordsCfg input (some ⟨remaining, by omega⟩) Fin.elim0 (output ++ [true]))
      (remaining + 1) = _
    rw [ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- The finite control of a fixed nest of unary loops. -/
def Control (coefficient : ℕ) : ℕ → Type
  | 0 => Fin (coefficient + 1)
  | degree + 1 => Control coefficient degree ⊕ Fin 3

instance (coefficient degree : ℕ) : Finite (Control coefficient degree) := by
  induction degree with
  | zero => change Finite (Fin (coefficient + 1)); infer_instance
  | succ degree ih =>
    change Finite (Control coefficient degree ⊕ Fin 3)
    let := ih
    infer_instance

/-- With `base` true bits on each work tape, write `coefficient * base ^ degree` true bits. -/
def loops (coefficient : ℕ) : (degree : ℕ) → MultiTapeTM degree Bool (Control coefficient degree)
  | 0 => constant coefficient
  | degree + 1 => (loops coefficient degree).repeatUnary

/-- A runtime bound for the fixed nest of loops. -/
def time (coefficient base : ℕ) : ℕ → ℕ
  | 0 => coefficient + 1
  | degree + 1 => base * (time coefficient base degree + 3) + 2

theorem iterate_append_replicate (length count : ℕ) (output : List Bool) :
    (fun output => output ++ List.replicate length true)^[count] output =
      output ++ List.replicate (count * length) true := by
  induction count generalizing output with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply, ih, List.append_assoc, ← List.replicate_add]
    rw [Nat.succ_mul, Nat.add_comm (count * length) length]

/-- Every loop nest restores its input and work heads and preserves the counter words. -/
theorem runFrom_loops (coefficient base degree : ℕ) (input output : List Bool) :
    (loops coefficient degree).runFrom
      (wordsCfg input (some (loops coefficient degree).q₀)
        (fun _ => List.replicate base true) output)
      (time coefficient base degree) =
      wordsCfg input none (fun _ => List.replicate base true)
        (output ++ List.replicate (coefficient * base ^ degree) true) := by
  induction degree generalizing output with
  | zero =>
    have hwords : (fun _ : Fin 0 => List.replicate base true) = Fin.elim0 := by
      funext i
      exact i.elim0
    simpa [loops, time, constant, Control, hwords] using
      runFrom_constant_remaining coefficient input coefficient le_rfl output
  | succ degree ih =>
    have hwords : Fin.lastCases (List.replicate base true)
        (fun _ : Fin degree => List.replicate base true) =
        (fun _ => List.replicate base true) := by
      funext i
      induction i using Fin.lastCases <;> simp
    simpa only [loops, time, Control, hwords, iterate_append_replicate, pow_succ,
      Nat.mul_left_comm base coefficient, Nat.mul_comm base (base ^ degree), Nat.mul_assoc] using
      runFrom_repeatUnary (loops coefficient degree) (fun _ => List.replicate base true)
        (fun output => output ++ List.replicate (coefficient * base ^ degree) true)
        (time coefficient base degree) ih base output

/-- The clock constructor itself has a polynomial runtime bound. -/
theorem time_le (coefficient base degree : ℕ) (hbase : 1 ≤ base) :
    time coefficient base degree ≤ 6 ^ degree * (coefficient + 1) * base ^ degree := by
  induction degree with
  | zero => simp [time]
  | succ degree ih =>
    have hpositive : 1 ≤ 6 ^ degree * (coefficient + 1) * base ^ degree := by
      have h₁ : 0 < (6 : ℕ) ^ degree := pow_pos (by omega) _
      have h₂ : 0 < base ^ degree := pow_pos (by omega) _
      exact Nat.mul_pos (Nat.mul_pos h₁ (by omega)) h₂
    have hscaled := Nat.mul_le_mul_left base ih
    have hnonzero := Nat.mul_le_mul_left base hpositive
    simp only [time, pow_succ]
    nlinarith

end PolynomialClock

/-- Construct a unary monomial budget from the ordinary input, starting with blank work tapes. -/
def polynomialClock (coefficient degree : ℕ) :
    MultiTapeTM degree Bool (Bool ⊕ PolynomialClock.Control coefficient degree) :=
  (initializeUnary degree).seq (PolynomialClock.loops coefficient degree)

/-- The budget constructor halts with exactly the requested unary word. Its scratch counters
and input head are restored, and its output can be redirected to a work tape. -/
theorem runFrom_polynomialClock (coefficient degree : ℕ) (input output : List Bool) :
    (polynomialClock coefficient degree).runFrom
      (wordsCfg input (some (polynomialClock coefficient degree).q₀) (fun _ => []) output)
      (2 * input.length + 2 + PolynomialClock.time coefficient (input.length + 1) degree) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true)
        (output ++ List.replicate (coefficient * (input.length + 1) ^ degree) true) := by
  let initializer := initializeUnary degree
  let generator := PolynomialClock.loops coefficient degree
  let cfg : Cfg degree Bool Bool input :=
    wordsCfg input (some initializer.q₀) (fun _ => []) output
  have hinit : initializer.runFrom cfg (2 * input.length + 2) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true) output := by
    simpa [initializer, cfg, initializeUnary] using runFrom_initializeUnary degree input output
  have hgenerate := PolynomialClock.runFrom_loops coefficient (input.length + 1) degree
    input output
  have hseq := runFrom_seq hinit rfl (by simpa using hgenerate) rfl
  exact hseq

/-- A monomial bound for constructing the budget, including initialization of all counters. -/
theorem polynomialClock_time_le (coefficient degree : ℕ) (length : ℕ) :
    2 * length + 2 + PolynomialClock.time coefficient (length + 1) degree ≤
      (6 ^ degree * (coefficient + 1) + 2) * (length + 1) ^ (degree + 1) := by
  have htime := PolynomialClock.time_le coefficient (length + 1) degree (by omega)
  have hpower : 1 ≤ (length + 1) ^ degree := Nat.one_le_pow _ _ (by omega)
  have hscale := Nat.mul_le_mul_left (length + 1) htime
  have hlength := Nat.mul_le_mul_left (length + 1) hpower
  rw [pow_succ]
  nlinarith

/-- The budget constructor also satisfies the monomial clock convention used by PPT. -/
theorem runFrom_polynomialClock_bound (coefficient degree : ℕ) (input output : List Bool) :
    (polynomialClock coefficient degree).runFrom
      (wordsCfg input (some (polynomialClock coefficient degree).q₀) (fun _ => []) output)
      ((6 ^ degree * (coefficient + 1) + 2) * (input.length + 1) ^ (degree + 1)) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true)
        (output ++ List.replicate (coefficient * (input.length + 1) ^ degree) true) := by
  rw [(polynomialClock coefficient degree).runFrom_eq_of_halt _
    (polynomialClock_time_le coefficient degree input.length)
    (by rw [runFrom_polynomialClock]; rfl), runFrom_polynomialClock]

end Turing.MultiTapeTM
