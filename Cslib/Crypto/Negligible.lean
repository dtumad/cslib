/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Init
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

end Cslib.Crypto
