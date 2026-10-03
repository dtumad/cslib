/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Computability.Probabilistic.Encoding
public import Cslib.Computability.Probabilistic.Sampling
public import Cslib.Probability.Entropy

/-!
# Samplable pseudoentropy pairs

A pair consists of a public observation and a hidden bit. The observation has a finite type
at each parameter and an injective word encoding, so its conditional entropy is unambiguous.
A strict PPT sampler realizes the joint law exactly.

`SamplablePair.HasGap` says that every uniform PPT predictor eventually has signed correlation
at most `1 - H(hidden | observation) - gap`. This is the entropy threshold used in the
OWF-to-PRG construction; merely being hard to predict is not sufficient.

This interface records the joint law and its sampler. `Pseudoentropy.Seed` exposes the sampler's
saved fair-bit tape as a uniform seed and accounts for every bit, including unused randomness.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Definitions 3 and 4.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use a sampler presentation and uniform strict PPT predictors. The signed correlation is
  twice success probability minus one, as in the write-up.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter

/-- Predict the hidden bit from the public component of a sampled pair. -/
noncomputable def predictionGame (sample : ℕ → ProbComp (Word × Bool))
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let pair ← sample n
  let guess ← adversary n pair.1
  return guess == pair.2

/-- A finite joint law together with its exact strict PPT word sampler. -/
structure SamplablePair where
  /-- The public information available at each parameter. -/
  Observation : ℕ → Type
  /-- Its alphabet is finite, without requiring a computable enumeration. -/
  [finite : ∀ n, Finite (Observation n)]
  /-- Encoding preserves all the public information. -/
  encode : ∀ n, Observation n ↪ Word
  /-- The public observation and hidden bit. -/
  joint : ∀ n, PMF (Observation n × Bool)
  /-- An executable sampler using only fair coins. -/
  sample : ℕ → ProbComp (Word × Bool)
  /-- Its complete running time is bounded by one polynomial. -/
  efficient : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) sample
  /-- The sampler realizes the finite joint law exactly. -/
  eval_sample : ∀ n, ProbComp.eval (sample n) =
    (joint n).map (fun pair => (encode n pair.1, pair.2))

attribute [instance] SamplablePair.finite

namespace SamplablePair

/-- Every uniform PPT predictor stays below the conditional-entropy threshold by this gap.
The threshold beyond which the inequality holds may depend on the predictor. -/
def HasGap (pair : SamplablePair) (gap : ℕ → ℝ) : Prop :=
  ∀ adversary : Distinguisher, IsPPT boolEncoding adversary →
    ∀ᶠ n in atTop, 2 * winProbability (predictionGame pair.sample adversary n) - 1 ≤
      1 - PMF.conditionalEntropy (pair.joint n) - gap n

/-- The pseudoentropy threshold equivalently lower-bounds each efficient predictor's error. -/
theorem HasGap.eventually_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (adversary : Distinguisher)
    (hefficient : IsPPT boolEncoding adversary) :
    ∀ᶠ n in atTop, (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
      (ProbComp.eval (predictionGame pair.sample adversary n) false).toReal := by
  filter_upwards [hgap adversary hefficient] with n hn
  have hsum := PMF.sum_toReal (ProbComp.eval (predictionGame pair.sample adversary n))
  simp only [Fintype.sum_bool] at hsum
  simp only [winProbability, Game.winProbability] at hn
  linarith

/-- A fair-bit predictor has zero correlation, so entropy plus the prediction gap cannot
eventually exceed one. -/
theorem HasGap.eventually_entropy_add_gap_le_one {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) :
    ∀ᶠ n in atTop, PMF.conditionalEntropy (pair.joint n) + gap n ≤ 1 := by
  have h := hgap (fun _ _ => OracleComp.uniform Bool) (isPPTOn_uniformBool _)
  have hfair (n : ℕ) : winProbability
      (predictionGame pair.sample (fun _ _ => OracleComp.uniform Bool) n) = 1 / 2 := by
    simp [winProbability, Game.winProbability, predictionGame, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.bind_apply, PMF.map_apply, OracleComp.uniform,
      PMF.uniformOfFintype_apply, ENNReal.tsum_mul_right, PMF.tsum_coe]
  filter_upwards [h] with n hn
  rw [hfair] at hn
  linarith

/-- A smaller requested gap follows from any larger proved gap. -/
theorem HasGap.mono {pair : SamplablePair} {gap smaller : ℕ → ℝ} (h : pair.HasGap gap)
    (hle : ∀ n, smaller n ≤ gap n) : pair.HasGap smaller := by
  intro adversary hPPT
  filter_upwards [h adversary hPPT] with n hn
  exact hn.trans (sub_le_sub_left (hle n) _)

end SamplablePair

end Cslib.Crypto.Pseudoentropy
