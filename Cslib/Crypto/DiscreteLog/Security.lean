/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.DiscreteLog.Probability
public import Cslib.Crypto.Game
public import Cslib.Computability.PolynomialTime.Deterministic
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.PolynomialTime.Sigma

/-!
# Discrete-logarithm hardness implies negligible guessing probability

The always-zero adversary has a uniform deterministic machine. Its exact success probability
therefore derives the inverse-cardinality assumption used in collision and forking bounds.
-/

public section

namespace Cslib.Crypto.DiscreteLog

open PFunctor MeasureTheory ProbabilityTheory Turing.MultiTapePTM Turing.MultiTapeTM

/-- Inverse scalar-space size is negligible under uniform discrete-logarithm hardness.
This needs only an efficient representation of zero, not a uniform scalar sampler. -/
theorem negligible_inv_card_of_secure {F G : ℕ → Type} [∀ n, Zero (F n)]
    [∀ n, SMul (F n) (G n)] [∀ n, DecidableEq (G n)] [∀ n, Finite (F n)]
    [∀ n, MeasurableSpace (F n)] [∀ n, MeasurableSingletonClass (F n)]
    {P : ℕ → PFunctor.{0, 0}}
    [∀ n op, MeasurableSpace ((P n).B op)]
    [∀ n op, DiscreteMeasurableSpace ((P n).B op)]
    {Oracle : Type} [Finite Oracle]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    (μ : ∀ n op, Measure ((P n).B op))
    (ambient : ∀ n op, (P n).FreeM ((effects Oracle).B op))
    (sample : ∀ n, (P n).FreeM (F n)) (g : ∀ n, G n)
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word)
    (hg : ∀ n, Function.Injective (fun secret : F n => secret • g n))
    (hsample : ∀ n, FreeM.denote (μ n) (sample n) = uniformOn Set.univ)
    (hzero : IsPolyTime unaryEncoding (fun n => scalar n 0))
    (hsecure : Game.Secure
      (fun (adversary : ∀ n, G n → (effects Oracle).FreeM (Option (F n))) n =>
        FreeM.denote (μ n) (experiment (sample n) (g n)
          (fun pk => (adversary n pk).liftM (ambient n))))
      (fun _ _ => Measure.dirac false)
      (fun adversary => IsPPT (sigmaEncoding unaryEncoding element) wordEncoding
        (fun input => optionEncoding (scalar input.1) <$> adversary input.1 input.2))) :
    Negligible (fun n => (Nat.card (F n) : ℝ)⁻¹) := by
  have hguess : IsPPT (sigmaEncoding unaryEncoding element) wordEncoding
      (fun input => optionEncoding (scalar input.1) <$>
        (pure (some 0) : (effects Oracle).FreeM (Option (F input.1)))) := by
    simp only [map_pure]
    exact ((hzero.comp_encoded
      (isPolyTime_input (sigmaEncoding unaryEncoding element)).sigma_fst).option_some).isPPT
  have h := hsecure (fun _ _ => pure (some 0)) hguess
  have heq (n : ℕ) := denote_experiment_const (μ n) (sample n) (g n) (0 : F n)
    (hg n) (hsample n)
  simpa only [Game.advantage_dirac_false, FreeM.liftM_pure, Game.winProbability,
    measureReal_def, heq, ENNReal.toReal_inv, ENNReal.toReal_natCast] using h

end Cslib.Crypto.DiscreteLog
