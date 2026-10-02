/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Security of Boolean experiments

A `Game` is the distribution of a Boolean experiment. Its acceptance probability, distinguishing
advantage, and asymptotic security are independent of the language used to write the experiment.
`Game.Secure` restricts whole adversaries, which may themselves be families of tests. This lets
finite cryptographic primitives and uniform PPT programs share the same security definitions.

The advantage convention is the absolute difference of acceptance probabilities, as in
[BonehShoup2023], Section 3.1. Negligibility is Mathlib's superpolynomial decay.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

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

open Filter Topology in
/-- Halving a unary security parameter preserves negligible decay. -/
theorem Negligible.div_two {ε : ℕ → ℝ} (h : Negligible ε) : Negligible (fun n => ε (n / 2)) := by
  have hhalf : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (2 * b)] with n hn
    lia
  intro degree
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  have hdecay := h.polynomial_mul
    ((Polynomial.C (2 : ℝ) * (Polynomial.X + 1)) ^ degree)
  have hlimit := (hdecay 0).comp hhalf
  simp only [pow_zero, one_mul, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Function.comp_def] at hlimit
  apply squeeze_zero (fun _ => abs_nonneg _) ?_ (by simpa using hlimit.abs)
  intro n
  simp only [abs_mul, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n / 2 : ℕ) + 1)]
  gcongr
  have hn : n ≤ 2 * (n / 2 + 1) := by lia
  exact_mod_cast hn

/-- The distribution of the Boolean result of a security experiment. -/
abbrev Game := PMF Bool

namespace Game

/-- The probability that an experiment accepts. -/
noncomputable abbrev winProbability (game : Game) : ℝ := (game true).toReal

/-- The absolute difference of two experiments' acceptance probabilities. -/
noncomputable abbrev advantage (real ideal : Game) : ℝ :=
  |real.winProbability - ideal.winProbability|

/-- Distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (real ideal : Game) : 0 ≤ advantage real ideal := abs_nonneg _

/-- Equal experiments have zero advantage. -/
@[simp] theorem advantage_self (game : Game) : advantage game game = 0 := by
  simp [advantage]

/-- Swapping the experiments preserves advantage. -/
theorem advantage_comm (real ideal : Game) : advantage real ideal = advantage ideal real :=
  abs_sub_comm _ _

/-- Complementing a game's answer exchanges acceptance and rejection. -/
@[simp] theorem winProbability_not (game : Game) :
    winProbability (game.map Bool.not) = 1 - winProbability game := by
  have hsum : (game false).toReal + (game true).toReal = 1 := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    have h := game.tsum_coe
    simp only [tsum_fintype, Fintype.sum_bool] at h
    rw [add_comm, h]
    simp
  simp [winProbability, PMF.map_apply, tsum_fintype] at *
  linarith

/-- Complementing both answers preserves advantage. -/
@[simp] theorem advantage_not (real ideal : Game) :
    advantage (real.map Bool.not) (ideal.map Bool.not) = advantage real ideal := by
  simp only [advantage, winProbability_not]
  convert abs_sub_comm (winProbability ideal) (winProbability real) using 1
  congr 1
  ring

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (first middle last : Game) :
    advantage first last ≤ advantage first middle + advantage middle last := abs_sub_le _ _ _

/-- Distinguishing advantage is at most one. -/
theorem advantage_le_one (real ideal : Game) : advantage real ideal ≤ 1 := by
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one real true)
  have hideal := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one ideal true)
  simp only [ENNReal.toReal_one] at hreal hideal
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [@ENNReal.toReal_nonneg (real true),
    @ENNReal.toReal_nonneg (ideal true)]

/-- Comparing with certain rejection measures the probability of winning. -/
@[simp] theorem advantage_pure_false (game : Game) :
    advantage game (PMF.pure false) = winProbability game := by
  simp [advantage, winProbability]

/-- Comparing with a fair coin measures absolute prediction bias. -/
@[simp] theorem advantage_uniform_bool (game : Game) :
    advantage game (PMF.uniformOfFintype Bool) = |winProbability game - 1 / 2| := by
  simp [advantage, winProbability, PMF.uniformOfFintype_apply]

/-- Each admissible adversary has negligible advantage. The admissibility predicate applies
before the security parameter is supplied, so it can require one uniform algorithm. -/
def Secure {Adversary : Type*} (real ideal : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Prop :=
  ∀ adversary, Admissible adversary →
    Negligible (fun n => advantage (real adversary n) (ideal adversary n))

/-- A common bound on the advantage of all admissible adversaries at each parameter. -/
def SecureWithError {Adversary : Type*} (real ideal : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) (ε : ℕ → ℝ≥0) : Prop :=
  ∀ adversary, Admissible adversary →
    ∀ n, advantage (real adversary n) (ideal adversary n) ≤ ε n

/-- Restricting admissibility preserves a concrete security bound. -/
theorem SecureWithError.of_admissible {Adversary : Type*}
    {real ideal : Adversary → ℕ → Game} {Admissible Restricted : Adversary → Prop}
    {ε : ℕ → ℝ≥0} (h : SecureWithError real ideal Admissible ε)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    SecureWithError real ideal Restricted ε := fun adversary ha => h adversary (hsub adversary ha)

/-- Enlarging an error budget preserves its security guarantee. -/
theorem SecureWithError.mono {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε) (hle : ∀ n, ε n ≤ δ n) :
    SecureWithError real ideal Admissible δ :=
  fun adversary ha n => (h adversary ha n).trans (by exact_mod_cast hle n)

/-- Swapping the experiments preserves the same concrete error. -/
theorem SecureWithError.symm {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε) : SecureWithError ideal real Admissible ε := by
  intro adversary ha n
  simpa only [advantage_comm] using h adversary ha n

/-- Concrete security bounds add across a game hop. -/
theorem SecureWithError.trans {Adversary : Type*} {first middle last : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (hfirst : SecureWithError first middle Admissible ε)
    (hlast : SecureWithError middle last Admissible δ) :
    SecureWithError first last Admissible (fun n => ε n + δ n) := by
  intro adversary ha n
  exact (advantage_triangle _ _ _).trans (add_le_add (hfirst adversary ha n) (hlast adversary ha n))

/-- Restricting the admissible adversaries preserves security. -/
theorem Secure.of_admissible {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible Restricted : Adversary → Prop} (h : Secure real ideal Admissible)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    Secure real ideal Restricted := fun adversary ha => h adversary (hsub adversary ha)

/-- An experiment is secure relative to itself. -/
theorem Secure.refl {Adversary : Type*} (game : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Secure game game Admissible := by
  intro adversary _
  simp

/-- Swapping the experiments preserves security. -/
theorem Secure.symm {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (h : Secure real ideal Admissible) :
    Secure ideal real Admissible := by
  intro adversary ha
  simpa only [advantage_comm] using h adversary ha

/-- Security composes through an intermediate experiment. -/
theorem Secure.trans {Adversary : Type*} {first middle last : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (hfirst : Secure first middle Admissible)
    (hlast : Secure middle last Admissible) : Secure first last Admissible := by
  intro adversary ha
  exact negligible_of_le ((hfirst adversary ha).add (hlast adversary ha))
    (fun _ => advantage_nonneg _ _) (fun _ => advantage_triangle _ _ _)

/-- A reduction preserves security when it preserves admissibility and bounds advantage. -/
theorem Secure.of_reduction {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary → ∀ n,
      advantage (targetReal adversary n) (targetIdeal adversary n) ≤
        advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n)) :
    Secure targetReal targetIdeal TargetAdmissible := by
  intro adversary ha
  exact negligible_of_le (h _ (hadmissible adversary ha))
    (fun _ => advantage_nonneg _ _) (hbound adversary ha)

/-- A negligible common error bound implies asymptotic security. -/
theorem SecureWithError.secure {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε)
    (hε : Negligible (fun n => (ε n : ℝ))) : Secure real ideal Admissible := by
  intro adversary ha
  exact negligible_of_le hε (fun _ => advantage_nonneg _ _) (h adversary ha)

end Game
end Cslib.Crypto
