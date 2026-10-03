/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.UniformNat
public import Cslib.Crypto.Computational.Prediction
public import Cslib.Crypto.Game.Hybrid

/-!
# A uniform bound over polynomially many tests

For efficiently samplable indistinguishable ensembles, one uniform indexed test has a negligible
advantage bound covering every polynomially bounded index. The index need not be computable.
The reduction samples an index and calibrates its test with fresh real-or-ideal reference data.
Its advantage is exactly the average of the squared indexed advantages, so signs cannot cancel.

This supplies the uniformity argument needed when extending the seed-length schedule in the
OWF-to-PRG construction to every length. The underlying construction follows Thomas Holenstein,
*Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness*,
TCC 2006, Section 5, [write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
The squared-gap calculation here is an elementary consequence of `bitPredictor_bias`.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

namespace UniformChoice

/-- Sample an index and calibrate its test using a fresh real-or-ideal reference sample. -/
noncomputable def test (bound : ℕ) (real ideal : ProbComp Word)
    (adversary : ℕ → Word → ProbComp Bool) (challenge : Word) : ProbComp Bool := do
  let index ← sampleDyadicIndex bound
  calibratedTest (real >>= adversary index) (ideal >>= adversary index)
    (adversary index challenge)

/-- The reduction charges for the sampled index, reference sample, and both adversary calls. -/
theorem test_isPPT {α : Type} {input : α ↪ Word}
    {bound : α → ℕ} {real ideal : α → ProbComp Word}
    {adversary : α → ℕ → Word → ProbComp Bool}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hreal : IsPPTOn input wordEncoding real)
    (hideal : IsPPTOn input wordEncoding ideal)
    (hadversary : IsPPTOn (pairEncoding (pairEncoding input unaryEncoding) wordEncoding)
      boolEncoding (fun a => adversary a.1.1 a.1.2 a.2)) :
    IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun a => test (bound a.1) (real a.1) (ideal a.1) (adversary a.1) a.2) := by
  unfold test
  ppt

/-- Sampling the challenge commutes with the independent index and calibration trial. -/
theorem eval_bind_test (bound : ℕ) (real ideal source : ProbComp Word)
    (adversary : ℕ → Word → ProbComp Bool) :
    ProbComp.eval (source >>= test bound real ideal adversary) =
      (PMF.uniformOfFintype (Fin (dyadicSize bound))).bind (fun index =>
        ProbComp.eval (calibratedTest (real >>= adversary index.val)
          (ideal >>= adversary index.val) (source >>= adversary index.val))) := by
  simp only [test, ProbComp.eval_bind, eval_sampleDyadicIndex, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext index
  simp only [calibratedTest, ProbComp.eval_bind, ProbComp.eval_map, map_bind]
  rw [PMF.bind_comm]

/-- Averaging calibrated tests averages their squared advantages, with no cancellation. -/
theorem advantage_eq (bound : ℕ) (real ideal : ProbComp Word)
    (adversary : ℕ → Word → ProbComp Bool) :
    advantage (real >>= test bound real ideal adversary)
      (ideal >>= test bound real ideal adversary) =
        (∑ index : Fin (dyadicSize bound),
          advantage (real >>= adversary index.val) (ideal >>= adversary index.val) ^ 2) /
            dyadicSize bound := by
  have hgap := fun index : Fin (dyadicSize bound) =>
    calibratedTest_gap (real >>= adversary index.val) (ideal >>= adversary index.val)
  simp only [winProbability] at hgap
  rw [advantage, Game.advantage, eval_bind_test, eval_bind_test,
    Game.winProbability_uniform, Game.winProbability_uniform]
  simp only [Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib, hgap]
  exact abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _))

/-- Each squared indexed advantage is bounded by the sampling range times the reduction's
advantage. The chosen index is used only in this inequality. -/
theorem advantage_sq_le (bound : ℕ) (real ideal : ProbComp Word)
    (adversary : ℕ → Word → ProbComp Bool) {index : ℕ} (hindex : index ≤ bound) :
    advantage (real >>= adversary index) (ideal >>= adversary index) ^ 2 ≤
      dyadicSize bound * advantage (real >>= test bound real ideal adversary)
        (ideal >>= test bound real ideal adversary) := by
  have hpos : (0 : ℝ) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  rw [advantage_eq, mul_div_cancel₀ _ hpos.ne']
  exact Finset.single_le_sum (fun i _ => sq_nonneg
    (advantage (real >>= adversary i.val) (ideal >>= adversary i.val)))
      (Finset.mem_univ (⟨index, hindex.trans_lt (lt_dyadicSize bound)⟩ : Fin (dyadicSize bound)))

end UniformChoice

/-- For samplable ensembles, uniform indistinguishability controls every polynomially bounded
index of a single PPT test. One negligible bound works for all indices, including choices that
are not computable. The two sampling hypotheses are needed by the calibration reduction. -/
theorem ComputationallyIndistinguishable.uniform_bound
    {real ideal : ℕ → ProbComp Word} {bound : ℕ → ℕ}
    (hsecure : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (real n)) (fun n => ProbComp.eval (ideal n)))
    (hreal : IsPPTOn unaryEncoding wordEncoding real)
    (hideal : IsPPTOn unaryEncoding wordEncoding ideal)
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)))
    (adversary : ℕ → ℕ → Word → ProbComp Bool)
    (hadversary : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun a => adversary a.1.1 a.1.2 a.2)) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧ ∀ n index, index ≤ bound n →
      advantage (real n >>= adversary n index) (ideal n >>= adversary n index) ≤ ε n := by
  let reduction := fun n => UniformChoice.test (bound n) (real n) (ideal n) (adversary n)
  have hefficient := UniformChoice.test_isPPT hbound hreal hideal hadversary
  have hreduce : IsPPT boolEncoding reduction := by
    unfold reduction
    ppt
  have hnegligible : Negligible (fun n =>
      advantage (real n >>= reduction n) (ideal n >>= reduction n)) := by
    simpa only [distinguishingGame, advantage, ProbComp.eval_bind, ProbComp.eval_sample]
      using hsecure reduction hreduce
  have hscaled := hnegligible.polynomiallyBounded_mul
    (dyadicSize_polynomiallyBounded.comp hbound.polynomiallyBounded)
  refine ⟨_, hscaled.sqrt, fun _ => Real.sqrt_nonneg _, fun n index hindex => ?_⟩
  exact Real.le_sqrt_of_sq_le (UniformChoice.advantage_sq_le (bound n)
    (real n) (ideal n) (adversary n) hindex)

end Cslib.Crypto
