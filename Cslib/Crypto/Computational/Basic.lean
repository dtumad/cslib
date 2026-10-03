/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Crypto.Game
public import Cslib.Probability.PMF

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

/-- The probability that a Boolean game returns `true`. -/
noncomputable def winProbability (game : ProbComp Bool) : ℝ :=
  Game.winProbability (ProbComp.eval game)

theorem winProbability_nonneg (game : ProbComp Bool) : 0 ≤ winProbability game :=
  ENNReal.toReal_nonneg

/-- Implication between deterministic winning conditions gives a probability bound. -/
theorem winProbability_pure_mono {first second : Bool} (h : first = true → second = true) :
    winProbability (pure first) ≤ winProbability (pure second) := by
  cases first <;> cases second <;> simp_all [winProbability, Game.winProbability]

/-- Replacing each reachable continuation by one with larger success probability can only
increase the success probability of the complete game. -/
theorem winProbability_bind_mono {α : Type} (program : ProbComp α)
    {first second : α → ProbComp Bool}
    (h : ∀ a ∈ (ProbComp.eval program).support,
      winProbability (first a) ≤ winProbability (second a)) :
    winProbability (program >>= first) ≤ winProbability (program >>= second) := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  simp only [ProbComp.eval_bind, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ (ProbComp.eval program).support
  · apply mul_le_mul_right
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp (h a ha)
  · simp only [(PMF.apply_eq_zero_iff _ _).mpr ha, zero_mul, le_refl]

/-- A finite random choice averages the continuation's winning probabilities. -/
theorem winProbability_sample_bind {α : Type} [Fintype α] (distribution : PMF α)
    (game : α → ProbComp Bool) :
    winProbability (OracleComp.sample distribution >>= game) =
      ∑ a, (distribution a).toReal * winProbability (game a) := by
  simp only [winProbability, ProbComp.eval_bind, ProbComp.eval_sample, PMF.bind_apply_toReal]

/-- Complementing a game's answer exchanges winning and losing. -/
@[simp] theorem winProbability_not (game : ProbComp Bool) :
    winProbability (Bool.not <$> game) = 1 - winProbability game := by
  simpa only [winProbability, ProbComp.eval_map] using Game.winProbability_not (ProbComp.eval game)

/-- Absolute difference in acceptance probabilities. -/
noncomputable def advantage (game₀ game₁ : ProbComp Bool) : ℝ :=
  Game.advantage (ProbComp.eval game₀) (ProbComp.eval game₁)

theorem advantage_nonneg (game₀ game₁ : ProbComp Bool) : 0 ≤ advantage game₀ game₁ :=
  abs_nonneg _

@[simp] theorem advantage_self (game : ProbComp Bool) : advantage game game = 0 := by
  simp [advantage]

theorem advantage_comm (game₀ game₁ : ProbComp Bool) :
    advantage game₀ game₁ = advantage game₁ game₀ := abs_sub_comm _ _

/-- Complementing both answers preserves distinguishing advantage. -/
@[simp] theorem advantage_not (game₀ game₁ : ProbComp Bool) :
    advantage (Bool.not <$> game₀) (Bool.not <$> game₁) = advantage game₀ game₁ := by
  simpa only [advantage, ProbComp.eval_map] using
    Game.advantage_not (ProbComp.eval game₀) (ProbComp.eval game₁)

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (game₀ game₁ game₂ : ProbComp Bool) :
    advantage game₀ game₂ ≤ advantage game₀ game₁ + advantage game₁ game₂ :=
  abs_sub_le _ _ _

/-- A distinguisher receives the security parameter and a sampled word. -/
abbrev Distinguisher := ℕ → Word → ProbComp Bool

/-- A family of randomized word tests is admissible when one uniform PPT algorithm realizes it.
Sampling a specified distribution here describes its semantics; `IsPPT` still requires a machine
realization and does not grant unit-cost sampling of arbitrary distributions. -/
def IsPPTTest (test : ℕ → Word → PMF Bool) : Prop :=
  IsPPT boolEncoding (fun n input => OracleComp.sample (test n input))

/-- Interpreting a program preserves exactly its uniform PPT restriction. -/
@[simp] theorem isPPTTest_eval {adversary : Distinguisher} :
    IsPPTTest (fun n input => ProbComp.eval (adversary n input)) ↔
      IsPPT boolEncoding adversary := by
  constructor <;> intro h
  · exact IsPPT.congr h (fun _ _ => ProbComp.eval_sample _)
  · exact h.congr (fun _ _ => (ProbComp.eval_sample _).symm)

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
  Game.Secure
    (fun adversary n => ProbComp.eval (distinguishingGame (X n) (adversary n)))
    (fun adversary n => ProbComp.eval (distinguishingGame (Y n) (adversary n)))
    (IsPPT boolEncoding)

/-- Program distinguishers and their semantic tests give the same security notion. -/
theorem computationallyIndistinguishable_iff_tests {X Y : ℕ → PMF Word} :
    ComputationallyIndistinguishable X Y ↔
      Game.Secure (fun test n => (X n).bind (test n))
        (fun test n => (Y n).bind (test n)) IsPPTTest := by
  constructor
  · intro h test hPPT
    simpa only [distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample] using
      h (fun n input => OracleComp.sample (test n input)) hPPT
  · intro h adversary hPPT
    simpa only [distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample] using
      h (fun n input => ProbComp.eval (adversary n input)) (isPPTTest_eval.mpr hPPT)

theorem ComputationallyIndistinguishable.refl (X : ℕ → PMF Word) :
    ComputationallyIndistinguishable X X := Game.Secure.refl _ _

theorem ComputationallyIndistinguishable.symm {X Y : ℕ → PMF Word}
    (h : ComputationallyIndistinguishable X Y) : ComputationallyIndistinguishable Y X :=
  Game.Secure.symm h

/-- A two-hop hybrid argument, reusing the same distinguisher in each hop. -/
theorem ComputationallyIndistinguishable.trans {X Y Z : ℕ → PMF Word}
    (hXY : ComputationallyIndistinguishable X Y) (hYZ : ComputationallyIndistinguishable Y Z) :
    ComputationallyIndistinguishable X Z := Game.Secure.trans hXY hYZ

end Cslib.Crypto
