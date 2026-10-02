/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Basic.Real.Basic

/-!
# Polynomially many game hops

The concrete hybrid inequality adds the advantages of adjacent games. The asymptotic theorem
requires a single negligible bound that works for every hop at each security parameter. Merely
assuming negligibility separately for each fixed hop does not suffice when the number of hops
grows with the parameter. The common bound may depend on the distinguisher.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.3.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped BigOperators

/-- Polynomial factors preserve a nonnegative negligible bound. -/
theorem negligible_polynomial_mul {ε : ℕ → ℝ} {p : ℕ → ℕ}
    (hε : Negligible ε) (hε₀ : ∀ n, 0 ≤ ε n) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ) * ε n) := by
  obtain ⟨c, d, hp⟩ := hp
  have hbound : Negligible (fun n => (c : ℝ) * ((n : ℝ) + 1) ^ d * ε n) := by
    convert hε.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d) using 1
    ext n
    simp
  apply negligible_of_le hbound (fun n => mul_nonneg (Nat.cast_nonneg _) (hε₀ n))
  intro n
  apply mul_le_mul_of_nonneg_right _ (hε₀ n)
  exact_mod_cast hp n

/-- The advantage between the endpoints is at most the sum of all adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → ProbComp Bool) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) := by
  induction hops with
  | zero => simp
  | succ hops ih =>
    calc
      advantage (games 0) (games (hops + 1)) ≤
          advantage (games 0) (games hops) + advantage (games hops) (games (hops + 1)) :=
        advantage_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1))) +
          advantage (games hops) (games (hops + 1)) := add_le_add ih le_rfl
      _ = _ := (Finset.sum_range_succ _ _).symm

/-- A common bound on each hop gives the usual linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → ProbComp Bool) (hops : ℕ) (ε : ℝ)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ (hops : ℝ) * ε := by
  calc
    advantage (games 0) (games hops) ≤
        ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) :=
      advantage_hybrid_le_sum games hops
    _ ≤ ∑ _i ∈ Finset.range hops, ε := Finset.sum_le_sum fun i hi =>
      hstep i (Finset.mem_range.mp hi)
    _ = _ := by simp

/-- Polynomially many hops with a common negligible bound have negligible total advantage. -/
theorem negligible_hybrid {games : ℕ → ℕ → ProbComp Bool} {hops : ℕ → ℕ} {ε : ℕ → ℝ}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε) (hε₀ : ∀ n, 0 ≤ ε n)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  negligible_of_le (negligible_polynomial_mul hε hε₀ hpoly)
    (fun _ => advantage_nonneg _ _) (fun n => advantage_hybrid_le _ _ _ (hstep n))

/-- A polynomial hybrid argument for ensembles. Each distinguisher may have its own negligible
bound, but that bound must cover all adjacent hybrids uniformly. -/
theorem ComputationallyIndistinguishable.hybrid {hybrids : ℕ → ℕ → PMF Word}
    {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary : Distinguisher, IsPPT boolEncoding adversary →
      ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧ ∀ n i, i < hops n →
        advantage (distinguishingGame (hybrids n i) (adversary n))
          (distinguishingGame (hybrids n (i + 1)) (adversary n)) ≤ ε n) :
    ComputationallyIndistinguishable (fun n => hybrids n 0) (fun n => hybrids n (hops n)) := by
  intro adversary hPPT
  obtain ⟨ε, hε, hε₀, hstep⟩ := hstep adversary hPPT
  exact negligible_hybrid
    (games := fun n i => distinguishingGame (hybrids n i) (adversary n)) hpoly hε hε₀ hstep

end Cslib.Crypto
