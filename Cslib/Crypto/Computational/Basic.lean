/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Probability.PMF
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Computational security: negligible advantages and indistinguishability

Security is asymptotic in a unary security parameter, against uniform, strict PPT adversaries.
`Negligible` specializes Mathlib's superpolynomial decay. In particular, the negligible bound may
depend on the adversary: the adversary is quantified before asserting decay of its advantage.

Games are closed `ProbComp Bool` programs. `winProbability` is their probability of returning
`true`, and `advantage` is the absolute difference between two such probabilities. This is the
distinguishing convention, without the factor of one half used for guessing a hidden challenge bit.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. This is Mathlib's superpolynomial decay, specialized to natural parameters. -/
abbrev Negligible (ε : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) ε

@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

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

/-- The probability that a Boolean game returns `true`. -/
noncomputable def winProbability (game : ProbComp Bool) : ℝ :=
  (ProbComp.eval game true).toReal

theorem winProbability_nonneg (game : ProbComp Bool) : 0 ≤ winProbability game :=
  ENNReal.toReal_nonneg

/-- A finite random choice averages the continuation's winning probabilities. -/
theorem winProbability_sample_bind {α : Type} [Fintype α] (distribution : PMF α)
    (game : α → ProbComp Bool) :
    winProbability (OracleComp.sample distribution >>= game) =
      ∑ a, (distribution a).toReal * winProbability (game a) := by
  simp only [winProbability, ProbComp.eval_bind, ProbComp.eval_sample, PMF.bind_apply_toReal]

/-- Complementing a game's answer exchanges winning and losing. -/
@[simp] theorem winProbability_not (game : ProbComp Bool) :
    winProbability (Bool.not <$> game) = 1 - winProbability game := by
  have hsum : (ProbComp.eval game false).toReal + (ProbComp.eval game true).toReal = 1 := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    have h := (ProbComp.eval game).tsum_coe
    simp only [tsum_fintype, Fintype.sum_bool] at h
    rw [add_comm, h]
    simp
  simp [winProbability, PMF.map_apply, tsum_fintype] at *
  linarith

/-- Absolute difference in acceptance probabilities. -/
noncomputable def advantage (game₀ game₁ : ProbComp Bool) : ℝ :=
  |winProbability game₀ - winProbability game₁|

theorem advantage_nonneg (game₀ game₁ : ProbComp Bool) : 0 ≤ advantage game₀ game₁ :=
  abs_nonneg _

@[simp] theorem advantage_self (game : ProbComp Bool) : advantage game game = 0 := by
  simp [advantage]

theorem advantage_comm (game₀ game₁ : ProbComp Bool) :
    advantage game₀ game₁ = advantage game₁ game₀ := abs_sub_comm _ _

/-- Complementing both answers preserves distinguishing advantage. -/
@[simp] theorem advantage_not (game₀ game₁ : ProbComp Bool) :
    advantage (Bool.not <$> game₀) (Bool.not <$> game₁) = advantage game₀ game₁ := by
  simp only [advantage, winProbability_not]
  convert abs_sub_comm (winProbability game₁) (winProbability game₀) using 1
  congr 1
  ring

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (game₀ game₁ game₂ : ProbComp Bool) :
    advantage game₀ game₂ ≤ advantage game₀ game₁ + advantage game₁ game₂ :=
  abs_sub_le _ _ _

/-- A distinguisher receives the security parameter and a sampled word. -/
abbrev Distinguisher := ℕ → Word → ProbComp Bool

/-- Draw a sample and give it to a distinguisher. -/
noncomputable def distinguishingGame (distribution : PMF Word)
    (adversary : Word → ProbComp Bool) : ProbComp Bool := do
  let sample ← OracleComp.sample distribution
  adversary sample

/-- Postprocessing a distinguisher's answer postprocesses the entire game's answer. -/
theorem distinguishingGame_map (distribution : PMF Word) (adversary : Word → ProbComp Bool)
    (f : Bool → Bool) :
    distinguishingGame distribution (fun word => f <$> adversary word) =
      f <$> distinguishingGame distribution adversary := by
  simp [distinguishingGame]

/-- Two ensembles are computationally indistinguishable if each uniform PPT distinguisher has
negligible advantage. Time is polynomial in the parameter plus sample length. Sample lengths need
not be polynomial in the parameter; `PolynomiallyBoundedEnsemble` supplies that extra condition.
There is no requirement that either ensemble itself be efficiently sampled. -/
def ComputationallyIndistinguishable (X Y : ℕ → PMF Word) : Prop :=
  ∀ adversary : Distinguisher, IsPPT boolEncoding adversary →
    Negligible (fun n => advantage (distinguishingGame (X n) (adversary n))
      (distinguishingGame (Y n) (adversary n)))

theorem ComputationallyIndistinguishable.refl (X : ℕ → PMF Word) :
    ComputationallyIndistinguishable X X := by
  intro adversary _
  simp

theorem ComputationallyIndistinguishable.symm {X Y : ℕ → PMF Word}
    (h : ComputationallyIndistinguishable X Y) : ComputationallyIndistinguishable Y X := by
  intro adversary hPPT
  simpa only [advantage_comm] using h adversary hPPT

/-- A two-hop hybrid argument, reusing the same distinguisher in each hop. -/
theorem ComputationallyIndistinguishable.trans {X Y Z : ℕ → PMF Word}
    (hXY : ComputationallyIndistinguishable X Y) (hYZ : ComputationallyIndistinguishable Y Z) :
    ComputationallyIndistinguishable X Z := by
  intro adversary hPPT
  exact negligible_of_le ((hXY adversary hPPT).add (hYZ adversary hPPT))
    (fun _ => advantage_nonneg _ _) (fun _ => advantage_triangle _ _ _)

end Cslib.Crypto
