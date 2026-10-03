/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Game.Hybrid

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

/-- The advantage between program experiments is at most the sum of adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → ProbComp Bool) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) :=
  Game.advantage_hybrid_le_sum (fun i => ProbComp.eval (games i)) hops

/-- A common bound on each program hop gives linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → ProbComp Bool) (hops : ℕ) (ε : ℝ)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ (hops : ℝ) * ε :=
  Game.advantage_hybrid_le (fun i => ProbComp.eval (games i)) hops ε hstep

/-- Polynomially many program hops with a common negligible bound remain negligible. -/
theorem negligible_hybrid {games : ℕ → ℕ → ProbComp Bool} {hops : ℕ → ℕ} {ε : ℕ → ℝ}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  Game.negligible_hybrid (games := fun n i => ProbComp.eval (games n i)) hpoly hε hstep

/-- A polynomial hybrid argument for ensembles. Each distinguisher may have its own negligible
bound, but that bound must cover all adjacent hybrids uniformly. -/
theorem ComputationallyIndistinguishable.hybrid {hybrids : ℕ → ℕ → PMF Word}
    {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary : Distinguisher, IsPPT boolEncoding adversary →
      ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n i, i < hops n →
        advantage (distinguishingGame (hybrids n i) (adversary n))
          (distinguishingGame (hybrids n (i + 1)) (adversary n)) ≤ ε n) :
    ComputationallyIndistinguishable (fun n => hybrids n 0) (fun n => hybrids n (hops n)) := by
  intro adversary hPPT
  obtain ⟨ε, hε, hstep⟩ := hstep adversary hPPT
  exact negligible_hybrid
    (games := fun n i => distinguishingGame (hybrids n i) (adversary n)) hpoly hε hstep

end Cslib.Crypto
