/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligible functions

Negligible bounds are Mathlib's superpolynomial decay at natural security parameters. This module
collects their closure under comparison, polynomially bounded losses, square roots, and changes
of parameter. It is independent of probability distributions, games, and machine models.

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

/-- Polynomially bounded factors preserve negligible decay, including for signed functions. -/
theorem Negligible.polynomiallyBounded_mul {ε : ℕ → ℝ} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ) * ε n) := by
  obtain ⟨c, d, hp⟩ := hp
  have hbound : Negligible (fun n => (c : ℝ) * ((n : ℝ) + 1) ^ d * ε n) := by
    convert hε.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d) using 1
    ext n
    simp
  apply hbound.trans_abs_le
  intro n
  simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (p n) : (0 : ℝ) ≤ p n),
    abs_of_nonneg (Nat.cast_nonneg c : (0 : ℝ) ≤ c),
    abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact_mod_cast hp n

open Filter Topology in
/-- Negligible decay survives reindexing when the new parameter tends to infinity and the old
parameter is polynomially bounded in it. The reindexing function need not be computable. -/
theorem Negligible.comp_of_polynomial_bound {ε : ℕ → ℝ} {index bound : ℕ → ℕ}
    (hε : Negligible ε) (hindex : Tendsto index atTop atTop)
    (hbound : PolynomiallyBounded bound) (hle : ∀ᶠ n in atTop, n ≤ bound (index n)) :
    Negligible (fun n => ε (index n)) := by
  have habs : Negligible (fun n => |ε n|) := hε.trans_abs_le (fun _ => by simp)
  intro degree
  have hlimit := (habs.polynomiallyBounded_mul (hbound.pow degree) 0).comp hindex
  simp only [pow_zero, one_mul, Nat.cast_pow, Function.comp_def] at hlimit
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlimit
  filter_upwards [hle] with n hn
  simp only [Function.comp_def, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  gcongr

open Filter in
/-- Negligible success is eventually smaller than the reciprocal of any positive
polynomially bounded loss. -/
theorem Negligible.eventually_le_inv_polynomial {ε : ℕ → ℝ} (hε : Negligible ε)
    {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (hpos : ∀ n, 0 < p n) :
    ∀ᶠ n in atTop, ε n ≤ 1 / (p n : ℝ) := by
  have h := hε.polynomiallyBounded_mul hp 0
  simp only [pow_zero, one_mul] at h
  filter_upwards [h.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn
  apply (le_div_iff₀ (by exact_mod_cast hpos n)).mpr
  simpa only [mul_comm] using hn

open Filter in
/-- Halving a unary security parameter preserves negligible decay. -/
theorem Negligible.div_two {ε : ℕ → ℝ} (h : Negligible ε) : Negligible (fun n => ε (n / 2)) := by
  apply h.comp_of_polynomial_bound (bound := fun n => 2 * (n + 1))
    (Nat.tendsto_div_const_atTop (by decide)) (by fun_prop)
  exact Eventually.of_forall (fun n => by lia)

end Cslib.Crypto
