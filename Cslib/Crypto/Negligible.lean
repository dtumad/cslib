/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligible functions

Negligible bounds are Mathlib's superpolynomial decay at natural security parameters. This module
collects comparison and square-root lemmas, and the geometric decay bound. Polynomial losses
use Mathlib's `SuperpolynomialDecay.polynomial_mul` directly. This module is independent of
probability distributions, games, and machine models.

The decay bound may depend on the whole algorithm. Security definitions quantify over that
algorithm before asserting negligibility; this module does not change that quantifier order.
-/

@[expose] public section

namespace Cslib.Crypto

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. This is Mathlib's superpolynomial decay, specialized to natural parameters. -/
abbrev Negligible (ε : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) ε

@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- Geometric decay with ratio strictly between minus one and one is negligible. -/
theorem negligible_geometric {ratio : ℝ} (h : |ratio| < 1) :
    Negligible (fun n => ratio ^ n) :=
  fun degree => tendsto_pow_const_mul_const_pow_of_abs_lt_one degree h

/-- A constant nonzero advantage is not negligible. -/
theorem not_negligible_const {c : ℝ} (hc : c ≠ 0) : ¬ Negligible (fun _ => c) := by
  intro h
  have ht : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds 0) := by simpa using h 0
  exact hc (tendsto_nhds_unique tendsto_const_nhds ht)

/-- A pointwise smaller nonnegative advantage is negligible. -/
theorem negligible_of_le {ε δ : ℕ → ℝ} (hδ : Negligible δ)
    (hε : ∀ n, 0 ≤ ε n) (hle : ∀ n, ε n ≤ δ n) : Negligible ε := by
  apply hδ.trans_abs_le
  intro n
  simpa only [abs_of_nonneg (hε n), abs_of_nonneg ((hε n).trans (hle n))] using hle n

/-- Taking a square root preserves negligible decay. -/
theorem Negligible.sqrt {ε : ℕ → ℝ} (h : Negligible ε) :
    Negligible (fun n => Real.sqrt (ε n)) := by
  intro degree
  have hlimit := Real.continuous_sqrt.continuousAt.tendsto.comp (h (2 * degree))
  have hroot (n : ℕ) : Real.sqrt ((n : ℝ) ^ (2 * degree) * ε n) =
      (n : ℝ) ^ degree * Real.sqrt (ε n) := by
    rw [show (n : ℝ) ^ (2 * degree) = ((n : ℝ) ^ degree) ^ 2 by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  simpa only [Function.comp_def, hroot, Real.sqrt_zero] using hlimit

/-- A polynomially bounded count preserves negligible error, even when only its growth bound
is known. Runtime certificates provide such bounds for an algorithm's query counts. -/
theorem Negligible.mul_polynomiallyBounded {ε : ℕ → ℝ} (h : Negligible ε)
    {count : ℕ → ℕ} (hcount : PolynomiallyBounded count) :
    Negligible (fun n => (count n : ℝ) * ε n) := by
  obtain ⟨c, d, hcount⟩ := hcount
  have hpoly := h.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d)
  apply hpoly.trans_abs_le
  intro n
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (count n) : (0 : ℝ) ≤ count n), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ c * ((n : ℝ) + 1) ^ d)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount n) (abs_nonneg _)

/-- A polynomial number of rejection samplings has negligible total cutoff error when the
attempt budget is at least the security parameter. Extra attempts may be chosen by the caller. -/
theorem negligible_sampling_error {draws attempts : ℕ → ℕ}
    (hdraws : PolynomiallyBounded draws) (hattempts : ∀ n, n ≤ attempts n) :
    Negligible (fun n => (draws n : ℝ) * (2⁻¹ : ℝ) ^ attempts n) := by
  apply negligible_of_le
    ((negligible_geometric (ratio := (2⁻¹ : ℝ)) (by norm_num)).mul_polynomiallyBounded hdraws)
    (fun _ => by positivity)
  intro n
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) (hattempts n))
    (Nat.cast_nonneg _)

end Cslib.Crypto
