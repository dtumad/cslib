/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.Real.Sqrt

/-!
# Superpolynomial decay in the security parameter

Negligible advantages are functions of a natural security parameter with superpolynomial decay
(`Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))`). Taking square roots preserves
this (`Asymptotics.SuperpolynomialDecay.sqrt`), as does multiplying by a polynomially bounded
count (`Asymptotics.SuperpolynomialDecay.mul_polynomiallyBounded`), such as a number of queries.
-/

@[expose] public section

open Filter

namespace Asymptotics.SuperpolynomialDecay

variable {ε : ℕ → ℝ}

/-- Taking a square root preserves superpolynomial decay in the security parameter. -/
theorem sqrt (h : SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) ε) :
    SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) fun n => Real.sqrt (ε n) := by
  intro degree
  have hlimit := Real.continuous_sqrt.continuousAt.tendsto.comp (h (2 * degree))
  have hroot (n : ℕ) : Real.sqrt ((n : ℝ) ^ (2 * degree) * ε n) =
      (n : ℝ) ^ degree * Real.sqrt (ε n) := by
    rw [show (n : ℝ) ^ (2 * degree) = ((n : ℝ) ^ degree) ^ 2 by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  simpa only [Function.comp_def, hroot, Real.sqrt_zero] using hlimit

/-- Multiplying by a polynomially bounded count preserves superpolynomial decay in the security
parameter. -/
theorem mul_polynomiallyBounded (h : SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) ε)
    {count : ℕ → ℕ} (hcount : Cslib.PolynomiallyBounded count) :
    SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) fun n => (count n : ℝ) * ε n := by
  obtain ⟨c, d, hcount⟩ := hcount
  have hpoly := h.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d)
  apply hpoly.trans_abs_le
  intro n
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (count n) : (0 : ℝ) ≤ count n), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ c * ((n : ℝ) + 1) ^ d)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount n) (abs_nonneg _)

end Asymptotics.SuperpolynomialDecay
