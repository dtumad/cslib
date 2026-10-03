/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Basic
public import Cslib.Crypto.Game.Hybrid
public import Cslib.Computability.Probabilistic.Selection

/-!
# Uniform bounds for indexed predictors

An efficient sampler supplies fresh labeled examples for empirical predictor selection. A single
uniform predictor then performs almost as well as every candidate in a polynomial-size family.
Consequently a pseudoentropy gap bounds all candidates simultaneously, with any prescribed
inverse-polynomial slack. The bound allows the best candidate to vary arbitrarily with the
security parameter; that choice is never supplied to the algorithm.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  This empirical selection step prepares the uniform treatment of the entropy guesses in that
  proof. Its quantitative bound uses the shared concentration and candidate-selection rules.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter

/-- Compare predictors on fresh labeled samples, then use the chosen predictor on the challenge.
The challenge's hidden label is never an input to this program. -/
def selectPredictor (count trials : ℕ) (source : ProbComp (Word × Bool))
    (predict : ℕ → Word → ProbComp Bool) (observation : Word) : ProbComp Bool := do
  let chosen ← OracleComp.selectBest count trials (fun i => do
    let sample ← source
    (fun answer => answer == sample.2) <$> predict i sample.1)
  predict chosen observation

/-- Empirical prediction is strict PPT when the sampler, indexed predictors, and counts are
efficient. All callbacks may capture the original input. -/
theorem selectPredictor_isPPT {α : Type} {input : α ↪ Word}
    {count trials : α → ℕ} {source : α → ProbComp (Word × Bool)}
    {predict : α → ℕ → Word → ProbComp Bool} {observation : α → Word}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (htrials : IsPolyTime input (fun a => unaryEncoding (trials a)))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hpredict : IsPPTOn (pairEncoding (pairEncoding input unaryEncoding) wordEncoding)
      boolEncoding (fun x => predict x.1.1 x.1.2 x.2))
    (hobservation : IsPolyTime input observation) :
    IsPPTOn input boolEncoding (fun a =>
      selectPredictor (count a) (trials a) (source a) (predict a) (observation a)) := by
  unfold selectPredictor
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSelectPredictor : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``selectPredictor, ``selectPredictor_isPPT)]

/-- Selection is independent of the challenge, so its final correctness game is a fresh trial
of the selected candidate. -/
theorem eval_predictionGame_selectPredictor (sample : ℕ → ProbComp (Word × Bool))
    (predict : ℕ → ℕ → Word → ProbComp Bool) (count trials : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (predictionGame sample (fun n =>
      selectPredictor (count n) (trials n) (sample n) (predict n)) n) =
      ProbComp.eval (OracleComp.selectBest (count n) (trials n)
        (fun i => predictionGame sample (fun n => predict n i) n) >>=
          fun i => predictionGame sample (fun n => predict n i) n) := by
  simp only [predictionGame, selectPredictor, bind_pure_comp, ProbComp.eval_bind,
    ProbComp.eval_map, PMF.map_bind]
  rw [PMF.bind_comm (ProbComp.eval (sample n))]

/-- The selected predictor's error is bounded by every candidate's error plus estimation and
selection losses, with the challenge sampled independently of all validation samples. -/
theorem selectPredictor_error_le (sample : ℕ → ProbComp (Word × Bool))
    (predict : ℕ → ℕ → Word → ProbComp Bool) (count confidence inverseTolerance : ℕ → ℕ)
    (n i : ℕ) (hi : i < count n) (htolerance : 0 < inverseTolerance n) :
    (ProbComp.eval (predictionGame sample (fun n => selectPredictor (count n)
      ((confidence n + 1) * inverseTolerance n ^ 2) (sample n) (predict n)) n) false).toReal ≤
        (ProbComp.eval (predictionGame sample (fun n => predict n i) n) false).toReal +
          2 / inverseTolerance n + count n * (1 / 2 : ℝ) ^ confidence n := by
  rw [eval_predictionGame_selectPredictor]
  exact ProbComp.selectBest_test_error_le (count n) (confidence n) (inverseTolerance n)
    htolerance (fun i => predictionGame sample (fun n => predict n i) n) i hi

namespace SamplablePair

/-- A pseudoentropy gap bounds every member of a uniformly efficient polynomial-size family
at once, allowing any efficient inverse-polynomial slack. No computable choice of index is
assumed, and the eventual threshold is common to all indices at each parameter. -/
theorem HasGap.eventually_indexed_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (predict : ℕ → ℕ → Word → ProbComp Bool)
    (hpredict : IsPPTOn
      (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding) boolEncoding
      (fun x => predict x.1.1 x.1.2 x.2))
    {count inverseTolerance : ℕ → ℕ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (htolerance : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseTolerance n)))
    (hpos : ∀ n, 0 < inverseTolerance n) :
    ∀ᶠ n in atTop, ∀ i < count n,
      (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
        (ProbComp.eval (predictionGame pair.sample (fun n => predict n i) n) false).toReal +
          1 / inverseTolerance n := by
  have hsource := pair.efficient
  have hefficient : IsPPT boolEncoding (fun n => selectPredictor (count n)
      ((n + 1) * (4 * inverseTolerance n) ^ 2) (pair.sample n) (predict n)) := by
    ppt
  have hselected := hgap.eventually_error_ge _ hefficient
  have hdecay := negligible_polynomial_mul
    (negligible_geometric (ratio := (1 / 2 : ℝ)) (by norm_num)) (fun _ => by positivity)
    hcount.polynomiallyBounded
  have hsmall := hdecay.eventually_le_inv_polynomial (fun _ => by positivity)
    (show PolynomiallyBounded (fun n => 2 * inverseTolerance n) from
      (PolynomiallyBounded.const 2).mul htolerance.polynomiallyBounded)
    (fun n => Nat.mul_pos (by decide) (hpos n))
  filter_upwards [hselected, hsmall] with n hn hsmall
  intro i hi
  have herror := selectPredictor_error_le pair.sample predict count id
    (fun n => 4 * inverseTolerance n) n i hi (by have := hpos n; positivity)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall herror
  have hprecision : 2 / (4 * (inverseTolerance n : ℝ)) +
      1 / (2 * inverseTolerance n) = 1 / inverseTolerance n := by ring
  dsimp only [id_eq] at herror
  linarith

end SamplablePair

end Cslib.Crypto.Pseudoentropy
