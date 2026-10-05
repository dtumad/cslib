/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Crypto.Negligible
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Security of Boolean experiments

A `Game` is a measure on Boolean outcomes. It may lose mass through nontermination.
Normalization is explicit where required. Acceptance probability, distinguishing advantage, and
asymptotic security are independent of the language used to write the experiment.
`Game.Secure` restricts whole adversaries, which may themselves be families of tests. This lets
finite cryptographic primitives and uniform PPT programs share the same security definitions.

The advantage convention is the absolute difference of acceptance probabilities, as in
[BonehShoup2023], Section 3.1. Negligibility is Mathlib's superpolynomial decay.
-/

@[expose] public section

namespace Cslib.Crypto

open MeasureTheory ProbabilityTheory
open scoped NNReal symmDiff

/-- The distribution of the Boolean result of a security experiment. -/
abbrev Game := Measure Bool

namespace Game

/-- The probability that an experiment accepts. -/
noncomputable abbrev winProbability (game : Game) : ℝ := game.real {true}

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

/-- Complementing an answer preserves missing mass from nontermination. -/
theorem winProbability_not_of_isFiniteMeasure (game : Game) [IsFiniteMeasure game] :
    winProbability (game.map Bool.not) = game.real Set.univ - winProbability game := by
  have hpre : Bool.not ⁻¹' {true} = ({true} : Set Bool)ᶜ := by
    ext b
    cases b <;> simp
  simp only [winProbability, measureReal_def,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), hpre]
  exact measureReal_compl (measurableSet_singleton _)

/-- Complementing a lossless game's answer exchanges acceptance and rejection. -/
@[simp] theorem winProbability_not (game : Game) [IsProbabilityMeasure game] :
    winProbability (game.map Bool.not) = 1 - winProbability game := by
  rw [winProbability_not_of_isFiniteMeasure, probReal_univ]

/-- Complementing both lossless answers preserves advantage. -/
@[simp] theorem advantage_not (real ideal : Game)
    [IsProbabilityMeasure real] [IsProbabilityMeasure ideal] :
    advantage (real.map Bool.not) (ideal.map Bool.not) = advantage real ideal := by
  simp only [advantage, winProbability_not]
  convert abs_sub_comm (winProbability ideal) (winProbability real) using 1
  congr 1
  ring

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (first middle last : Game) :
    advantage first last ≤ advantage first middle + advantage middle last := abs_sub_le _ _ _

/-- A joint execution bounds distinguishing advantage by the probability that its results
disagree. The coupling is an ordinary finite measure with the two games as its marginals. -/
theorem advantage_le_disagreement (joint : Measure (Bool × Bool)) [IsFiniteMeasure joint] :
    advantage (joint.map Prod.fst) (joint.map Prod.snd) ≤ joint.real {p | p.1 ≠ p.2} := by
  simp only [advantage, winProbability, measureReal_def,
    Measure.map_apply measurable_fst (measurableSet_singleton _),
    Measure.map_apply measurable_snd (measurableSet_singleton _)]
  have hset : (Prod.fst ⁻¹' ({true} : Set Bool)) ∆ (Prod.snd ⁻¹' ({true} : Set Bool)) =
      {p : Bool × Bool | p.1 ≠ p.2} := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp [Set.mem_symmDiff]
  rw [← hset]
  exact abs_measureReal_sub_le_measureReal_symmDiff
    MeasurableSet.of_discrete.nullMeasurableSet MeasurableSet.of_discrete.nullMeasurableSet

/-- Subprobability experiments have distinguishing advantage at most one. -/
theorem advantage_le_one (real ideal : Game)
    (hreal : real Set.univ ≤ 1) (hideal : ideal Set.univ ≤ 1) :
    advantage real ideal ≤ 1 := by
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ {true})).trans hreal)
  have hi := ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ {true})).trans hideal)
  simp only [ENNReal.toReal_one] at hr hi
  change |(real {true}).toReal - (ideal {true}).toReal| ≤ 1
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [@ENNReal.toReal_nonneg (real {true}),
    @ENNReal.toReal_nonneg (ideal {true})]

/-- Comparing with certain rejection measures the probability of winning. -/
@[simp] theorem advantage_dirac_false (game : Game) :
    advantage game (Measure.dirac false) = winProbability game := by
  simp [advantage, winProbability, measureReal_def]

/-- Comparing with a fair coin measures absolute prediction bias. -/
theorem advantage_uniform_bool (game : Game) :
    advantage game (uniformOn Set.univ) = |winProbability game - 1 / 2| := by
  simp only [advantage, winProbability, measureReal_def, uniformOn_univ,
    Measure.count_singleton, Fintype.card_bool]
  norm_num

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

/-- A uniform reduction may incur polynomial loss and negligible implementation error.
Both bounds may depend on the whole adversary, before the security parameter is supplied. -/
theorem Secure.of_reduction_with_error {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (loss : Target → ℕ → ℕ) (error : Target → ℕ → ℝ)
    (hloss : ∀ adversary, TargetAdmissible adversary → PolynomiallyBounded (loss adversary))
    (herror : ∀ adversary, TargetAdmissible adversary → Negligible (error adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary → ∀ n,
      advantage (targetReal adversary n) (targetIdeal adversary n) ≤
        loss adversary n *
          advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n) +
            error adversary n) :
    Secure targetReal targetIdeal TargetAdmissible := by
  intro adversary ha
  exact negligible_of_le
    (((h _ (hadmissible adversary ha)).mul_polynomiallyBounded (hloss adversary ha)).add
      (herror adversary ha)) (fun _ => advantage_nonneg _ _) (hbound adversary ha)

/-- Square-root loss, as in a forking reduction, also preserves asymptotic security. Cutoff
errors can occur in the original experiment and inside the reduction. -/
theorem Secure.of_reduction_sqrt {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (loss : Target → ℕ → ℕ) (gameError reductionError : Target → ℕ → ℝ)
    (hloss : ∀ adversary, TargetAdmissible adversary → PolynomiallyBounded (loss adversary))
    (hgameError : ∀ adversary, TargetAdmissible adversary → Negligible (gameError adversary))
    (hreductionError : ∀ adversary, TargetAdmissible adversary →
      Negligible (reductionError adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary → ∀ n,
      advantage (targetReal adversary n) (targetIdeal adversary n) ≤ gameError adversary n +
        Real.sqrt (loss adversary n *
          (advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n) +
            reductionError adversary n))) :
    Secure targetReal targetIdeal TargetAdmissible := by
  intro adversary ha
  exact negligible_of_le
    ((hgameError adversary ha).add
      ((Negligible.mul_polynomiallyBounded
        ((h _ (hadmissible adversary ha)).add (hreductionError adversary ha))
        (hloss adversary ha)).sqrt)) (fun _ => advantage_nonneg _ _) (hbound adversary ha)

/-- A negligible common error bound implies asymptotic security. -/
theorem SecureWithError.secure {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε)
    (hε : Negligible (fun n => (ε n : ℝ))) : Secure real ideal Admissible := by
  intro adversary ha
  exact negligible_of_le hε (fun _ => advantage_nonneg _ _) (h adversary ha)

end Game
end Cslib.Crypto
