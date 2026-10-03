/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Learning
public import Cslib.Crypto.Computational.Hybrid.SavedPrediction

/-!
# Masked-coordinate prediction examples

The examples check hidden-label-dependent masks, fresh randomness on repeated inputs, signed
hybrid cancellation, the loss from unused sampled indices, and strict PPT composition with
arbitrary certified training sources and distinguishers. Saved descriptions preserve the same
prediction law, and their size contract justifies truncation before storage. The concrete learner
composes these descriptions with fresh validation, including negatively biased candidates.
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

/-- Freeze the training examples and test coins. The chosen width bounds future observations;
the sampler remains strict PPT even if a training example exceeds that width. -/
noncomputable def coordinateDescriptions (source : ℕ → ProbComp (Word × Bool))
    (c d n : ℕ) : ProbComp Word :=
  SavedPrediction.sample wordEncoding (unaryEncoding n) (maskedTraining n (source n)) (source n)
    ((n + 1) ^ 2) c d ((n + 1) ^ 3)

/-- Ordinary client programs can sample predictor descriptions using `ppt`. -/
theorem coordinateDescriptions_isPPT {source : ℕ → ProbComp (Word × Bool)}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source) (c d : ℕ) :
    IsPPTOn unaryEncoding wordEncoding (coordinateDescriptions source c d) := by
  have hmasked := maskedTraining_isPPT hsource
  unfold coordinateDescriptions
  ppt

/-- One uniform deterministic evaluator replays the coordinate predictor at every bounded
observation. Its code does not contain the source program or its captured boosting state. -/
theorem coordinateDescriptions_realize {test : ℕ → List (Word × Bool) → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (predict : Word → Word → Bool),
      IsPolyTime coinInputEncoding (fun pair => [predict pair.1 pair.2]) ∧
      ∀ source n observation, observation.length ≤ (n + 1) ^ 3 →
        ProbComp.eval ((fun code => predict code observation) <$>
          coordinateDescriptions source c d n) =
          ProbComp.eval (coordinatePrediction source test n observation) := by
  obtain ⟨c, d, predict, hefficient, hlaw⟩ := SavedPrediction.exists_evaluator htest
  refine ⟨c, d, predict, hefficient, ?_⟩
  intro source n observation hwidth
  simpa [coordinateDescriptions, coordinatePrediction, maskedSequencePredictor, maskedTraining,
    wordEncoding] using hlaw n (maskedTraining n (source n)) (source n) ((n + 1) ^ 2)
      ((n + 1) ^ 3) observation hwidth

/-- Sample descriptions and learn a signed predictor using fresh labeled validation examples. -/
noncomputable def coordinateLearner (source : ℕ → ProbComp (Word × Bool))
    (c d : ℕ) (predict : Word → Word → Bool) (n : ℕ) : ProbComp Word :=
  Boosting.learn (coordinateDescriptions source c d n)
    (fun code => Boosting.weightedTrial (source n)
      (fun pair => Boosting.sampleWeight n 1 0 pair.1 pair.2)
      (fun pair => pure (predict code pair.1 == pair.2))) ((n + 1) ^ 2) ((n + 1) ^ 3)

/-- Sampling, orientation, and validation require no machine bookkeeping in client proofs. -/
theorem coordinateLearner_isPPT {source : ℕ → ProbComp (Word × Bool)}
    {predict : Word → Word → Bool}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source)
    (hpredict : IsPolyTime coinInputEncoding (fun pair => [predict pair.1 pair.2])) (c d : ℕ) :
    IsPPTOn unaryEncoding wordEncoding (coordinateLearner source c d predict) := by
  have hdescriptions := coordinateDescriptions_isPPT hsource c d
  unfold coordinateLearner
  apply Boosting.learn_isPPT hdescriptions <;> ppt

/-- The evaluator extracted from an arbitrary certified distinguisher supplies the learner's
validation identity. The source's hidden label is never passed to that evaluator. -/
theorem saved_descriptions_supply_validation_gap
    {test : ℕ → List (Word × Bool) → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding unaryEncoding
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
        (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (predict : Word → Word → Bool),
      IsPolyTime coinInputEncoding (fun pair => [predict pair.1 pair.2]) ∧
      ∀ (n count width : ℕ) (source : ProbComp Bool) (observe : Bool → Word)
          (mask : Bool → ProbComp Bool), (∀ bit, (observe bit).length ≤ width) →
        let original := (fun bit => (observe bit, bit)) <$> source
        let masked := maskedSample source observe id mask
        let candidates := SavedPrediction.sample wordEncoding (unaryEncoding n)
          masked original count c d width
        winProbability (OracleComp.replicate count original >>= test n) -
            winProbability (OracleComp.replicate count masked >>= test n) =
          (dyadicSize count : ℝ) * (winProbability (candidates >>= fun code =>
            Boosting.weightedTrial source mask
              (fun bit => pure (predict code (observe bit) == bit))) - 1 / 2) := by
  obtain ⟨c, d, predict, hefficient, hlaw⟩ := SavedPrediction.exists_evaluator htest
  refine ⟨c, d, predict, hefficient, ?_⟩
  intro n count width source observe mask hwidth
  apply maskedSequence_validation_gap source observe id mask
  intro bit _
  simpa only [maskedSequencePredictor, wordEncoding, Function.Embedding.refl_apply, id_eq] using
    hlaw n (maskedSample source observe id mask) ((fun bit => (observe bit, bit)) <$> source)
      count width (observe bit) (hwidth bit)

/-- Validation selects the complementary orientation when every original predictor is wrong.
This exercises negative bias, rather than assuming the successful sign as advice. -/
theorem learner_corrects_negative_bias (confidence : ℕ) :
    ((ProbComp.eval (Boosting.learn (pure []) (fun _ => pure false) confidence 2)).toOuterMeasure
      {code | Boosting.signedPredict (fun _ (_ : Unit) => false) code () ≠ true}).toReal ≤
      ((confidence + 1) * 64 + 1) * (1 / 2 : ℝ) ^ confidence := by
  have h := Boosting.learn_error_pow (pure []) (fun _ => pure false) confidence 2 (by decide)
    (by norm_num [winProbability, Game.winProbability])
  convert h using 2
  · congr 2
    ext code
    simp only [Boosting.signedPredict, Boosting.signedTest]
    cases hsign : code.headD false <;> norm_num [winProbability, Game.winProbability]
  · push_cast
    ring

/-- The boosting loop may truncate every returned code without changing any prediction, once
its bound covers the saved descriptions. This holds for arbitrary source programs and codes. -/
theorem saved_prediction_survives_truncation
    (replacement original : ProbComp (Word × Bool)) (base observation : Word)
    (count c d width bound : ℕ) (predict : Word → Word → Bool)
    (hreplacement : ∀ value ∈ (ProbComp.eval replacement).support, value.1.length ≤ width)
    (horiginal : ∀ value ∈ (ProbComp.eval original).support, value.1.length ≤ width)
    (hbound : SavedPrediction.codeBound base.length count c d width ≤ bound) :
    ProbComp.eval ((fun code => predict (code.take bound) observation) <$>
      SavedPrediction.sample wordEncoding base replacement original count c d width) =
      ProbComp.eval ((fun code => predict code observation) <$>
        SavedPrediction.sample wordEncoding base replacement original count c d width) := by
  simp only [ProbComp.eval_map, PMF.map]
  apply PMF.bind_congr_on_support
  intro code hcode
  have hsize := SavedPrediction.length_sample_le wordEncoding base replacement original
    count c d width hreplacement horiginal hcode
  simp only [Function.comp_def, List.take_of_length_le (hsize.trans hbound)]

end CslibTests.ComputationalCryptoMasking
