/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.OneWay
public import Cslib.Crypto.Computational.Prediction
public import Cslib.Crypto.Computational.PseudorandomGenerator
public import Cslib.Computability.Probabilistic.Input
public import Cslib.Computability.Probabilistic.PolynomialTime

/-!
# Hard-core predicates and one-bit expansion

A hard-core predicate is efficiently computable from a seed but unpredictable from its image.
Security quantifies over uniform PPT predictors. We use absolute bias from one half; fixed
Boolean complementation is PPT, so this also rules out reliable anticorrelation.

The reduction appends a trial bit, runs a distinguisher, and predicts that bit if the distinguisher
accepts, or its complement otherwise. We analyze the two fixed trial bits together. Each gives a
single uniform PPT predictor, so the proof never chooses a different predictor at each parameter.
The distinguishing gap is the average of their signed prediction biases.

Concatenation of polynomial-time computations supplies the generator's efficiency certificate.
Thus a one-way permutation equipped with a hard-core predicate yields a one-bit PRG.
`GoldreichLevin.HardCore` constructs the predicate from one-wayness and completes OWP-to-PRG.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
* Luca Trevisan, *CS276 Lecture 13: Pseudorandom Generators*, scribed by Siu-On Chan,
  Theorem 2 and its prediction reduction.
  [Notes](https://lucatrevisan.wordpress.com/2009/03/16/cs276-lecture-13-pseudorandom-generators/).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Predict a predicate of a uniform seed, given only its image and the security parameter. -/
noncomputable def predictionGame (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let seed ← OracleComp.sample (uniformBits n)
  let guess ← adversary n (f seed)
  return guess == predicate seed

/-- Absolute prediction bias above or below a fair guess. -/
noncomputable def predictionAdvantage (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) : ℝ :=
  |winProbability (predictionGame f predicate adversary n) - 1 / 2|

/-- An efficient predicate whose value is computationally hidden by `f`. -/
structure HardCore (f : Word → Word) (predicate : Word → Bool) : Prop where
  /-- Computing the predicate from the seed uses a fixed polynomial-time machine. -/
  polyTime : IsPolyTime id (fun seed => [predicate seed])
  /-- A predictor's correctness is indistinguishable from a fair coin. -/
  secure : Game.Secure (fun adversary n => ProbComp.eval (predictionGame f predicate adversary n))
    (fun _ _ => PMF.uniformOfFintype Bool) (IsPPT boolEncoding)

/-- The shared security property gives negligible absolute prediction bias. -/
theorem HardCore.unpredictable {f : Word → Word} {predicate : Word → Bool}
    (h : HardCore f predicate) (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) :
    Negligible (predictionAdvantage f predicate adversary) := by
  change Negligible (fun n => |winProbability (predictionGame f predicate adversary n) - 1 / 2|)
  simpa only [Game.advantage_uniform_bool, winProbability] using
    h.secure adversary hPPT

/-- Construct a hard-core predicate from its efficient evaluation and prediction bound. -/
theorem HardCore.of_unpredictable {f : Word → Word} {predicate : Word → Bool}
    (hpoly : IsPolyTime id (fun seed => [predicate seed]))
    (h : ∀ adversary : Distinguisher, IsPPT boolEncoding adversary →
      Negligible (predictionAdvantage f predicate adversary)) : HardCore f predicate := by
  refine ⟨hpoly, fun adversary hPPT => ?_⟩
  have hnegl := h adversary hPPT
  change Negligible (fun n => |winProbability (predictionGame f predicate adversary n) - 1 / 2|)
    at hnegl
  simpa only [Game.advantage_uniform_bool, winProbability] using hnegl

/-- Use acceptance of an appended trial bit to predict the hidden predicate. -/
def hardCorePredictor (adversary : Distinguisher) (trial : Bool) : Distinguisher :=
  fun n image => trialPredictor (fun bit => adversary n (image ++ [bit])) trial

/-- The reduction has a machine certificate, including construction of the extended input. -/
theorem hardCorePredictor_isPPT {adversary : Distinguisher}
    (h : IsPPT boolEncoding adversary) (trial : Bool) :
    IsPPT boolEncoding (hardCorePredictor adversary trial) :=
  (h.snoc_input trial).map_bool (fun accept => if accept then trial else !trial)

/-- The ideal hybrid replaces the hidden predicate by an independent fair bit. -/
noncomputable def hardCoreIdeal (f : Word → Word) (n : ℕ) : PMF Word :=
  (uniformBits n).bind (fun seed =>
    (PMF.uniformOfFintype Bool).map (fun bit => f seed ++ [bit]))

private theorem real_probability (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    winProbability (prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n) =
      ∑ bits : Fin n → Bool, ((PMF.uniformOfFintype (Fin n → Bool)) bits).toReal *
        winProbability (adversary n (f (List.ofFn bits) ++ [predicate (List.ofFn bits)])) := by
  simp only [prgRealGame, distinguishingGame, generatorEnsemble, PRG.Generator.outputDist,
    PRG.Generator.coe_mk, uniformBits, winProbability,
    ProbComp.eval_bind, ProbComp.eval_sample, PMF.bind_map, Function.comp_def,
    PMF.bind_apply_toReal]

private theorem ideal_probability (f : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    winProbability (distinguishingGame (hardCoreIdeal f n) (adversary n)) =
      ∑ bits : Fin n → Bool, ((PMF.uniformOfFintype (Fin n → Bool)) bits).toReal *
        ((winProbability (adversary n (f (List.ofFn bits) ++ [false])) +
          winProbability (adversary n (f (List.ofFn bits) ++ [true]))) / 2) := by
  simp only [distinguishingGame, hardCoreIdeal, uniformBits, winProbability,
    ProbComp.eval_bind, ProbComp.eval_sample, PMF.bind_map, PMF.bind_bind, Function.comp_def,
    PMF.bind_apply_toReal]
  apply Finset.sum_congr rfl
  intro bits _
  simp [PMF.uniformOfFintype_apply]
  ring

private theorem prediction_probability (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    winProbability (predictionGame f predicate adversary n) =
      ∑ bits : Fin n → Bool, ((PMF.uniformOfFintype (Fin n → Bool)) bits).toReal *
        winProbability ((fun guess => guess == predicate (List.ofFn bits)) <$>
          adversary n (f (List.ofFn bits))) := by
  simp only [predictionGame, uniformBits, winProbability, Game.winProbability, ProbComp.eval_bind,
    ProbComp.eval_sample, PMF.bind_map, Function.comp_def, ProbComp.eval_map, ProbComp.eval_pure]
  rw [PMF.bind_apply_toReal]
  rfl

/-- The distinguishing gap is the average signed bias of the two uniform predictors. -/
theorem hardCore_gap (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    winProbability (prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n) -
        winProbability (distinguishingGame (hardCoreIdeal f n) (adversary n)) =
      (winProbability (predictionGame f predicate (hardCorePredictor adversary false) n) +
        winProbability (predictionGame f predicate (hardCorePredictor adversary true) n) - 1) /
        2 := by
  have hstep (seed : Word) :=
    trialPredictor_gap (fun trial => adversary n (f seed ++ [trial])) (predicate seed)
  rw [real_probability, ideal_probability, prediction_probability, prediction_probability,
    ← Finset.sum_sub_distrib]
  simp only [hardCorePredictor]
  simp_rw [← mul_sub, hstep]
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_sub, mul_add, mul_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, PMF.sum_toReal]

/-- Distinguishing the real predicate from a fair bit is bounded by the average prediction bias. -/
theorem hardCore_advantage_le (f : Word → Word) (predicate : Word → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    advantage (prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n)
        (distinguishingGame (hardCoreIdeal f n) (adversary n)) ≤
      (predictionAdvantage f predicate (hardCorePredictor adversary false) n +
        predictionAdvantage f predicate (hardCorePredictor adversary true) n) / 2 := by
  rw [advantage, Game.advantage, ← winProbability, ← winProbability, hardCore_gap]
  let left := winProbability (predictionGame f predicate (hardCorePredictor adversary false) n)
  let right := winProbability (predictionGame f predicate (hardCorePredictor adversary true) n)
  change |(left + right - 1) / 2| ≤ (|left - 1 / 2| + |right - 1 / 2|) / 2
  rw [show left + right - 1 = (left - 1 / 2) + (right - 1 / 2) by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)

/-- A hard-core predicate can be replaced by an independent fair bit in every PPT test. -/
theorem HardCore.indistinguishable {f : Word → Word} {predicate : Word → Bool}
    (h : HardCore f predicate) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (hardCoreIdeal f) := by
  intro adversary hPPT
  have hleft := h.unpredictable _ (hardCorePredictor_isPPT hPPT false)
  have hright := h.unpredictable _ (hardCorePredictor_isPPT hPPT true)
  apply negligible_of_le ((hleft.add hright).const_mul (2 : ℝ)⁻¹)
    (fun _ => advantage_nonneg _ _)
  intro n
  simpa only [prgRealGame, Pi.add_apply, div_eq_mul_inv, mul_comm] using
    hardCore_advantage_le f predicate adversary n

/-- When the function preserves uniform seeds, the ideal hard-core hybrid is uniform. -/
theorem HardCore.indistinguishable_of_uniform {f : Word → Word} {predicate : Word → Bool}
    (h : HardCore f predicate) (huniform : ∀ n, (uniformBits n).map f = uniformBits n) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (fun n => uniformBits (n + 1)) := by
  have hideal : hardCoreIdeal f = fun n => uniformBits (n + 1) := by
    funext n
    change (uniformBits n).bind
      ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
    rw [← PMF.bind_map, huniform]
    exact (uniformBits_snoc n).symm
  rw [← hideal]
  exact h.indistinguishable

/-- Appending a hard-core predicate to an efficient length-preserving function that preserves
uniform seeds gives a one-bit PRG. One-wayness is used in constructing the hard-core predicate. -/
theorem HardCore.pseudorandomGenerator {f : Word → Word} {predicate : Word → Bool}
    (h : HardCore f predicate) (hf : IsPolyTime id f)
    (hlen : ∀ word, (f word).length = word.length)
    (huniform : ∀ n, (uniformBits n).map f = uniformBits n) :
    PseudorandomGenerator (fun seed => f seed ++ [predicate seed]) (fun n => n + 1) := by
  refine PseudorandomGenerator.of_indistinguishable (hf.append h.polyTime) ?_ Nat.lt_succ_self
    (h.indistinguishable_of_uniform huniform)
  intro seed
  simp [hlen]

/-- For a one-way permutation, the ideal hybrid is uniform at the expanded length. -/
theorem OneWayPermutation.hardCore_indistinguishable {f : Word → Word}
    {predicate : Word → Bool} (hf : OneWayPermutation f) (h : HardCore f predicate) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (fun n => uniformBits (n + 1)) :=
  h.indistinguishable_of_uniform hf.uniformBits_map

/-- A one-way permutation with a hard-core predicate gives a polynomial-time one-bit PRG. -/
theorem OneWayPermutation.pseudorandomGenerator_of_hardCore {f : Word → Word}
    {predicate : Word → Bool} (hf : OneWayPermutation f) (h : HardCore f predicate) :
    PseudorandomGenerator (fun seed => f seed ++ [predicate seed]) (fun n => n + 1) :=
  h.pseudorandomGenerator hf.oneWay.polyTime hf.length_eq hf.uniformBits_map

end Cslib.Crypto
