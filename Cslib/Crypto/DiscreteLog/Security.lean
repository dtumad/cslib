/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.DiscreteLog
public import Cslib.Crypto.Game
public import Cslib.Computability.PolynomialTime.Deterministic
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Closed

/-!
# Discrete-logarithm guessing probability and computational security

The always-zero adversary has a uniform deterministic machine. Its exact success probability
therefore derives the inverse-cardinality assumption used in collision and forking bounds.
-/

public section

namespace Cslib.Crypto.DiscreteLog

open PFunctor MeasureTheory ProbabilityTheory Turing.MultiTapePTM Turing.MultiTapeTM

/-- A fixed scalar guesses exactly one of the uniformly sampled secrets. -/
theorem denote_experiment_const {P : PFunctor.{0, 0}} {F G : Type}
    [SMul F G] [DecidableEq G] [Finite F]
    [MeasurableSpace F] [MeasurableSingletonClass F]
    [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
    (μ : (op : P.A) → Measure (P.B op)) (sample : P.FreeM F) (g : G) (guess : F)
    (hg : Function.Injective (fun secret : F => secret • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ (experiment sample g (fun _ => pure (some guess))) {true} =
      (Nat.card F : ENNReal)⁻¹ := by
  let := Fintype.ofFinite F
  simp only [experiment, pure_bind, Option.any_some]
  rw [← map_eq_pure_bind, ← FreeM.map_eq_map,
    FreeM.denote_map _ _ _ Measurable.of_discrete, hsample,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hset : (fun secret : F => decide (guess • g = secret • g)) ⁻¹' {true} = {guess} := by
    ext secret
    simp [hg.eq_iff, eq_comm]
  rw [hset]
  simp [uniformOn_univ, Nat.card_eq_fintype_card]

/-- Inverse scalar-space size is negligible under uniform discrete-logarithm hardness.
This needs only an efficient representation of zero, not a uniform scalar sampler. -/
theorem negligible_inv_card_of_secure {F G : ℕ → Type} [∀ n, Zero (F n)]
    [∀ n, SMul (F n) (G n)] [∀ n, DecidableEq (G n)] [∀ n, Finite (F n)]
    [∀ n, MeasurableSpace (F n)] [∀ n, MeasurableSingletonClass (F n)]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    (g : ∀ n, G n)
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word)
    (hg : ∀ n, Function.Injective (fun secret : F n => secret • g n))
    (hzero : IsPolyTime unaryEncoding (fun n => scalar n 0))
    (hsecure : Game.Secure
      (fun (adversary : ∀ n, G n → (effects Empty).FreeM (Option (F n))) n =>
        (uniformOn (Set.univ : Set (F n))).bind (fun secret =>
          (FreeM.denote coinMeasure (adversary n (secret • g n))).map
            (fun out => out.any (fun value => decide (value • g n = secret • g n)))))
      (fun _ _ => Measure.dirac false)
      (fun adversary => IsPPT (sigmaEncoding unaryEncoding element) wordEncoding
        (fun input => optionEncoding (scalar input.1) <$> adversary input.1 input.2))) :
    Negligible (fun n => (Nat.card (F n) : ℝ)⁻¹) := by
  have hguess : IsPPT (sigmaEncoding unaryEncoding element) wordEncoding
      (fun input => optionEncoding (scalar input.1) <$>
        (pure (some 0) : (effects Empty).FreeM (Option (F input.1)))) := by
    simp only [map_pure]
    exact ((hzero.comp_encoded
      (isPolyTime_input (sigmaEncoding unaryEncoding element)).sigma_fst).option_some).isPPT
  have h := hsecure (fun _ _ => pure (some 0)) hguess
  have heq (n : ℕ) : ((uniformOn (Set.univ : Set (F n))).bind (fun secret =>
      (FreeM.denote coinMeasure (pure (some (0 : F n)))).map
        (fun out => out.any (fun value => decide (value • g n = secret • g n))))) {true} =
        (Nat.card (F n) : ENNReal)⁻¹ := by
    let := Fintype.ofFinite (F n)
    simp only [FreeM.denote_pure,
      Measure.map_dirac, Option.any_some,
      Measure.bind_dirac_eq_map _ Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
    have hset : (fun secret : F n => decide ((0 : F n) • g n = secret • g n)) ⁻¹' {true} =
        {0} := by ext secret; simp [(hg n).eq_iff, eq_comm]
    rw [hset]
    simp [uniformOn_univ, Nat.card_eq_fintype_card]
  simpa only [Game.advantage_dirac_false, Game.winProbability, measureReal_def, heq,
    ENNReal.toReal_inv, ENNReal.toReal_natCast] using h

end Cslib.Crypto.DiscreteLog
