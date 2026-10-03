/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Masking

/-!
# Masked-coordinate prediction examples

The examples check hidden-label-dependent masks, fresh randomness on repeated inputs, signed
hybrid cancellation, the loss from unused sampled indices, and strict PPT composition with
arbitrary certified training sources and distinguishers.
-/

public section

namespace CslibTests.ComputationalCryptoMasking

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto Cslib.Crypto.Pseudoentropy

/-- Masking only the hidden true label still contributes at least half a bit of entropy.
The public observation is constant, so the mask is not determined by that observation. -/
theorem hidden_label_mask_entropy :
    (1 : ℝ) / 2 ≤ conditionalEntropy (ProbComp.eval
      (maskedSample (OracleComp.uniform Bool) (fun _ => ()) id (fun bit => pure bit))) := by
  have h := maskedSample_entropy_ge (OracleComp.uniform Bool) (fun _ => ()) id (fun bit => pure bit)
  simpa [OracleComp.uniform, Fintype.sum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply] using h

/-- The same false label is independently replaced twice; both outputs are true with probability
`1/16`. Reusing a cached randomized label would instead give probability `1/4`. -/
theorem repeated_masks_are_fresh :
    (ProbComp.eval (OracleComp.replicate 2
      (maskBit (OracleComp.uniform Bool) false)) [true, true]).toReal = 1 / 16 := by
  have h := ProbComp.eval_replicate_apply_ofFn
    (maskBit (OracleComp.uniform Bool) false) (fun _ : Fin 2 => true)
  norm_num [List.ofFn_succ] at h
  rw [h]
  norm_num [ENNReal.toReal_mul, eval_maskBit_apply, OracleComp.uniform, PMF.uniformOfFintype_apply]

/-- A fresh weighted mask may capture the input parameter while sampling labeled vote words. -/
noncomputable def maskedTraining (n : ℕ) (source : ProbComp (Word × Bool)) :
    ProbComp (Word × Bool) :=
  maskedSample source Prod.fst Prod.snd
    (fun pair => Boosting.sampleWeight n 1 0 pair.1 pair.2)

/-- The entire masked sampler has a synthesized strict PPT certificate. -/
theorem maskedTraining_isPPT {source : ℕ → ProbComp (Word × Bool)}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source) :
    IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding)
      (fun n => maskedTraining n (source n)) := by
  unfold maskedTraining
  ppt

/-- Conditional Boolean outputs and negation compose with arbitrary certified subprograms. -/
theorem conditional_bit_isPPT {α : Type} {input : α ↪ Word} {program : α → ProbComp Bool}
    {bit : α → Bool} (hprogram : IsPPTOn input boolEncoding program)
    (hbit : IsPolyTime input (fun a => [bit a])) :
    IsPPTOn input boolEncoding (fun a =>
      (fun accept => if accept then !bit a else bit a) <$> program a) := by ppt

private theorem dyadicSize_two : dyadicSize 2 = 4 := by decide

/-- At zero repetitions every sampled index rejects, without using either source or the test. -/
theorem empty_sequence_test (replacement original : ProbComp Word)
    (test : List Word → ProbComp Bool) (challenge : Word) :
    ProbComp.eval (sequenceTest replacement original 0 test challenge) = PMF.pure false := by
  simp only [sequenceTest, Nat.not_lt_zero, ite_false, ProbComp.eval_bind, ProbComp.eval_pure]
  exact PMF.bind_const _ _

/-- The two parity hops have opposite signs. Both reduced games accept with probability `1/4`,
including the two rejected padding indices; selecting an absolute best hop would lose this law. -/
theorem opposite_hops_cancel (challenge : Bool) :
    winProbability (sequenceTest (pure true) (pure false) 2
      (fun bits => pure (bits.foldl Bool.xor false)) challenge) = 1 / 4 := by
  simp only [sequenceTest, winProbability, Game.winProbability, ProbComp.eval_bind,
    eval_sampleDyadicIndex, PMF.bind_map, Function.comp_def, bind_apply_toReal,
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change (∑ i : Fin 4, _) = _
  cases challenge <;>
    norm_num [dyadicSize_two, Fin.sum_univ_succ, PMF.uniformOfFintype_apply,
      spliceTest, OracleComp.replicate, ProbComp.eval_pure]

/-- At one coordinate, reading a constant true label distinguishes the original sample from a
fully masked one. The extra padding index makes the reduced predictor correct with probability
`3/4`, checking both the sign and the factor in the reduction. -/
theorem single_coordinate_prediction :
    winProbability (maskedSequencePredictor (pure true) (fun _ => ()) id (fun _ => pure true)
      1 (fun pairs => pure ((pairs.headD ((), false)).2)) ()) = 3 / 4 := by
  have htrue : winProbability (pure true) = 1 := by
    simp [winProbability, Game.winProbability]
  have hfair : winProbability (OracleComp.uniform Bool) = 1 / 2 := by
    simp [winProbability, Game.winProbability, OracleComp.uniform, PMF.uniformOfFintype_apply]
  have h := maskedSequence_prediction_gap (pure true) (fun _ => ()) id (fun _ => pure true)
    1 (fun pairs => pure ((pairs.headD ((), false)).2))
  norm_num [OracleComp.replicate, maskedSample, maskBit, htrue, hfair,
    Fintype.sum_bool, PMF.pure_apply, show dyadicSize 1 = 2 by decide] at h ⊢
  linarith

/-- The complete coordinate predictor trains on labeled vote words, while its input is only an
observation. Its repetition count and soft weights depend on the unary parameter. -/
noncomputable def coordinatePrediction (source : ℕ → ProbComp (Word × Bool))
    (test : ℕ → List (Word × Bool) → ProbComp Bool) (n : ℕ) (observation : Word) : ProbComp Bool :=
  maskedSequencePredictor (source n) Prod.fst Prod.snd
    (fun pair => Boosting.sampleWeight n 1 0 pair.1 pair.2) ((n + 1) ^ 2) (test n) observation

/-- Both supplied algorithms retain their uniform certificates through the whole reduction. -/
theorem coordinatePrediction_isPPT {source : ℕ → ProbComp (Word × Bool)}
    {test : ℕ → List (Word × Bool) → ProbComp Bool}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source)
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun pair => test pair.1 pair.2)) :
    IsPPTOn (pairEncoding unaryEncoding wordEncoding) boolEncoding
      (fun pair => coordinatePrediction source test pair.1 pair.2) := by
  unfold coordinatePrediction
  ppt

end CslibTests.ComputationalCryptoMasking
