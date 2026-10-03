/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.HashReduction
public import Cslib.Crypto.Computational.Pseudoentropy.Basic
public import Cslib.Crypto.Computational.GoldreichLevin.WordDecoder
public import Cslib.Crypto.Computational.OneWay

/-!
# The hashed parity inverter as a PPT word program

The reduction samples one saved predictor tape, a hash length, a matrix, a guessed digest, and
decoder masks. It then invokes the shared word decoder with the public fields and coins captured
by its callback. All sampling uses fair bits, with a fixed polynomial bound for every input.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 4, Lemma 4.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  `HashReduction` supplies the finite bound for our public matrix family and enlarged dyadic
  range. This module implements its inverter using the existing word and saved-coin interfaces.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open Probability GoldreichLevin

/-- One polynomial tape budget covers all digest lengths and parity queries for an image. -/
def coinBudget (c d n imageLength : ℕ) : ℕ :=
  c * (2 * imageLength + 2 * (hashCount n * n) + 4 * hashCount n + 2 * n + 8) ^ d

/-- The shared tape budget is efficient in the parameter and image length. -/
theorem coinBudget_isPolyTime {α : Type} {encode : α ↪ Word} {parameter length : α → ℕ}
    (c d : ℕ) (hparameter : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hlength : IsPolyTime encode (fun a => unaryEncoding (length a))) :
    IsPolyTime encode (fun a => unaryEncoding (coinBudget c d (parameter a) (length a))) := by
  have hcount := hashCount_isPolyTime hparameter
  have hconstant (k : ℕ) := isPolyTime_const encode (unaryEncoding k)
  have hsize := ((hconstant 2).unary_mul hlength).unary_add
    ((hconstant 2).unary_mul (hcount.unary_mul hparameter))
  have hsize := (hsize.unary_add ((hconstant 4).unary_mul hcount)).unary_add
    ((hconstant 2).unary_mul hparameter)
  exact (hconstant c).unary_mul ((hsize.unary_add (hconstant 8)).unary_pow d)

attribute [aesop safe apply (rule_sets := [PolyTime])] coinBudget_isPolyTime

/-- Call the saved-coin predictor on the complete public observation. -/
def predictWithCoins (evaluate : Word → Word → Word) (n : ℕ) (image : Word) (index : ℕ)
    (matrix digest coins query : Word) : Bool :=
  (evaluate coins (parameterInput n (wordObservation image index matrix digest query))).headD false

/-- Capturing the public fields and saved coins requires only their ordinary efficiency
certificates. The callback is uniformly polynomial time in every supplied word. -/
theorem predictWithCoins_isPolyTime {α : Type} {encode : α ↪ Word}
    {evaluate : Word → Word → Word} {parameter index : α → ℕ}
    {image matrix digest coins query : α → Word}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2))
    (hparameter : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (himage : IsPolyTime encode image)
    (hindex : IsPolyTime encode (fun a => unaryEncoding (index a)))
    (hmatrix : IsPolyTime encode matrix) (hdigest : IsPolyTime encode digest)
    (hcoins : IsPolyTime encode coins) (hquery : IsPolyTime encode query) :
    IsPolyTime encode (fun a => [predictWithCoins evaluate (parameter a) (image a) (index a)
      (matrix a) (digest a) (coins a) (query a)]) :=
  (hevaluate.comp_pair hcoins (hparameter.parameterInput
    (wordObservation_isPolyTime himage hindex hmatrix hdigest hquery))).headD false

attribute [aesop safe apply (rule_sets := [PolyTime])] predictWithCoins_isPolyTime

/-- Guess the unknown hash value and decode, using the same predictor coins for every query. -/
noncomputable def wordInverter (f : Word → Word) (evaluate : Word → Word → Word)
    (c d degree : ℕ) : Inverter := fun n image => do
  let coins ← OracleComp.sampleBits (coinBudget c d n image.length)
  let index ← sampleDyadicIndex (n + 6)
  let matrix ← OracleComp.sampleBits (hashCount n * n)
  let digest ← OracleComp.sampleBits (index + 1)
  let masks ← OracleComp.sampleBits (maskCount n (precision degree n) * n)
  return wordDecode f (predictWithCoins evaluate n image index matrix digest coins)
    degree n image masks

set_option maxHeartbeats 800000 in
-- Five captured samples produce nested tuples whose projection certificates must be composed.
/-- The complete inverter is one strict PPT program for every parameter and image. -/
theorem wordInverter_isPPT {f : Word → Word} {evaluate : Word → Word → Word}
    (hf : IsPolyTime wordEncoding f)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2))
    (c d degree : ℕ) : IsPPT wordEncoding (wordInverter f evaluate c d degree) := by
  unfold IsPPT wordInverter
  apply IsPPTOn.bind_with
  · apply IsPolyTime.sampleBits
    apply coinBudget_isPolyTime <;> polytime
  apply IsPPTOn.bind_with
  · ppt
  apply IsPPTOn.bind_with
  · apply IsPolyTime.sampleBits
    apply IsPolyTime.unary_mul
    · apply hashCount_isPolyTime
      polytime
    · polytime
  apply IsPPTOn.bind_with
  · ppt
  apply IsPPTOn.bind_with
  · ppt
  apply IsPolyTime.isPPTOn
  apply wordDecode_isPolyTime degree hf
  · apply predictWithCoins_isPolyTime hevaluate <;> polytime
  · polytime
  · polytime
  · polytime

/-- The tape budget covers every well-formed public observation at this dimension. -/
theorem observation_coinBudget_le (c d n : ℕ) (image : Word)
    (index : Fin (hashCount n)) (matrix : BitString (hashCount n * n))
    (digest : BitString (index.val + 1)) (query : BitString n) :
    c * ((parameterInput n (wordObservation image index.val (List.ofFn matrix)
      (List.ofFn digest) (List.ofFn query))).length + 1) ^ d ≤
        coinBudget c d n image.length := by
  unfold coinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [wordObservation, length_parameterInput, length_pairEncoding,
    wordEncoding, Function.Embedding.coe_refl, id_eq, unaryEncoding_apply, List.length_replicate,
    List.length_ofFn]
  have := index.isLt
  lia

/-- A common finite tape turns the word evaluator into a deterministic matrix predictor.
The finite image type is represented injectively when relating its inversion experiment. -/
def fixedPredictor {Image : Type*} (encodeImage : Image → Word)
    (evaluate : Word → Word → Word) (c d n imageLength : ℕ)
    (coins : BitString (coinBudget c d n imageLength)) :
    MatrixPredictor n (hashCount n) Image := fun image index rows digest query =>
  predictWithCoins evaluate n (encodeImage image) index.val
    (List.ofFn ((maskEquiv (hashCount n) n).symm rows))
    (List.ofFn digest) (List.ofFn coins) (List.ofFn query)

/-- Padding the saved tape to the common budget preserves every individual prediction law. -/
theorem fixedPredictor_distribution {Image : Type*} (encodeImage : Image → Word)
    (adversary : Distinguisher) (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input budget, c * ((parameterInput n input).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformBits budget).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (n imageLength : ℕ) (image : Image) (hlength : (encodeImage image).length = imageLength)
    (index : Fin (hashCount n)) (rows : Fin (hashCount n) → BitString n)
    (digest : BitString (index.val + 1)) (query : BitString n) :
    (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))).map
        (fun coins => fixedPredictor encodeImage evaluate c d n imageLength coins
          image index rows digest query) =
      ProbComp.eval (adversary n (wordObservation (encodeImage image) index.val
        (List.ofFn ((maskEquiv (hashCount n) n).symm rows))
        (List.ofFn digest) (List.ofFn query))) := by
  have hbudget := observation_coinBudget_le c d n (encodeImage image) index
    ((maskEquiv (hashCount n) n).symm rows) digest query
  rw [hlength] at hbudget
  rw [hrealize _ _ _ hbudget]
  simp only [uniformBits, PMF.map_comp, Function.comp_def, fixedPredictor, predictWithCoins]

/-- The word inverter agrees exactly with the finite inverter after encoding its output.
Only the image representation and its fixed width enter this statement. -/
theorem wordInverter_eval {n imageLength : ℕ} {Image : Type*} [DecidableEq Image]
    (f : Word → Word) (finiteFunction : BitString n → Image) (encodeImage : Image ↪ Word)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (evaluate : Word → Word → Word) (c d degree : ℕ) (image : Image)
    (hlength : (encodeImage image).length = imageLength) :
    ProbComp.eval (wordInverter f evaluate c d degree n (encodeImage image)) =
      ((PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))).bind fun coins =>
        matrixInverter finiteFunction (fixedPredictor encodeImage evaluate c d n imageLength coins)
          (precision degree n) image).map List.ofFn := by
  have hindex : OracleComp.eval (fun q => q.elim) (sampleDyadicIndex (n + 6)) =
      (PMF.uniformOfFintype (Fin (hashCount n))).map Fin.val := eval_sampleDyadicIndex (n + 6)
  have hmatrix : uniformBits (hashCount n * n) =
      (PMF.uniformOfFintype (Fin (hashCount n) → BitString n)).map
        (fun rows => List.ofFn ((maskEquiv (hashCount n) n).symm rows)) := by
    rw [uniformBits, ← PMF.uniformOfFintype_map_equiv (maskEquiv (hashCount n) n).symm,
      PMF.map_comp]
    rfl
  have hfunction : (fun bits => f (List.ofFn bits)) = encodeImage ∘ finiteFunction :=
    funext hf
  have hdecode (predictor : Word → Bool) :
      (uniformBits (maskCount n (precision degree n) * n)).bind
        (fun masks => PMF.pure (wordDecode f predictor degree n (encodeImage image) masks)) =
      (invertFixed finiteFunction (fun query => predictor (List.ofFn query))
        (maskCount n (precision degree n)) image).map List.ofFn := by
    change (uniformBits _).map (wordDecode f predictor degree n (encodeImage image)) = _
    rw [uniform_wordDecode, hfunction,
      invertFixed_comp_injective finiteFunction encodeImage encodeImage.injective]
  simp only [wordInverter, ProbComp.eval, OracleComp.eval_bind, OracleComp.eval_pure,
    OracleComp.eval_sampleBits, hindex, hlength]
  simp_rw [hdecode, hmatrix]
  simp only [uniformBits, PMF.bind_map, PMF.map_bind,
    Function.comp_def, matrixInverter, guessInverter]
  rfl

/-- The complete prediction game agrees with the finite experiment with one independent saved
tape. Moving that tape outside the experiment does not change the predictor's distribution. -/
theorem eval_predictionGame {n imageLength : ℕ} {Image : Type*}
    (f : Word → Word) (finiteFunction : BitString n → Image) (encodeImage : Image → Word)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (adversary : Distinguisher) (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input budget, c * ((parameterInput n input).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformBits budget).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false)) :
    ProbComp.eval (predictionGame (sample f) adversary n) =
      (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))).bind fun coins =>
        matrixPrediction finiteFunction (fixedPredictor encodeImage evaluate c d n imageLength
          coins) := by
  simp only [predictionGame, ProbComp.eval_bind, eval_sample f finiteFunction encodeImage hf,
    ProbComp.eval_pure, joint, PMF.uniformOfFintype_prod, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, Function.comp_def]
  rw [← PMF.uniformOfFintype_map_equiv (maskEquiv (hashCount n) n).symm]
  simp only [PMF.bind_map, Function.comp_def, encodeObservation, prefixHash,
    Equiv.apply_symm_apply]
  simp_rw [← fixedPredictor_distribution encodeImage adversary evaluate c d hrealize n
    imageLength _ (hlength _), PMF.bind_map]
  simp only [Function.comp_def, matrixPrediction, PMF.map]
  simp_rw [← PMF.bind_comm (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength)))]
  congr 1
  funext coins
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext index
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext rows
  rw [PMF.bind_comm]

/-- The existing word one-wayness game is the finite inversion experiment under the same
image encoding. Success still means finding any preimage. -/
theorem eval_wordInversionGame {n imageLength : ℕ} {Image : Type*} [DecidableEq Image]
    (f : Word → Word) (finiteFunction : BitString n → Image) (encodeImage : Image ↪ Word)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (evaluate : Word → Word → Word) (c d degree : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment finiteFunction (fun image =>
        (PMF.uniformOfFintype (BitString (coinBudget c d n imageLength))).bind fun coins =>
          matrixInverter finiteFunction
            (fixedPredictor encodeImage evaluate c d n imageLength coins)
            (precision degree n) image) := by
  simp only [inversionGame, ProbComp.eval_bind, ProbComp.eval_sample, ProbComp.eval_pure,
    uniformBits, PMF.bind_map, Function.comp_def, hf]
  simp_rw [wordInverter_eval f finiteFunction encodeImage hf evaluate c d degree _ (hlength _)]
  simp only [inversionExperiment, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    hf, beq_eq_decide, encodeImage.injective.eq_iff]

/-- Holenstein's entropy-versus-prediction bound for the executable word games. Every sampled
bit and decoder query is included in the inverter certified by `wordInverter_isPPT`. -/
theorem word_prediction_entropy_le {n imageLength : ℕ} {Image : Type*}
    [Finite Image]
    (f : Word → Word) (finiteFunction : BitString n → Image) (encodeImage : Image ↪ Word)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x))
    (hlength : ∀ image, (encodeImage image).length = imageLength)
    (adversary : Distinguisher) (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input budget, c * ((parameterInput n input).length + 1) ^ d ≤ budget →
      ProbComp.eval (adversary n input) = (uniformBits budget).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (degree : ℕ) (hp : 8 * hashCount n ≤ precision degree n) :
    2 * winProbability (predictionGame (sample f) adversary n) - 1 +
        PMF.conditionalEntropy (joint (count := hashCount n) finiteFunction) ≤
      1 - 2 / (hashCount n : ℝ) + 128 * (dyadicSize (16 * hashCount n) : ℝ) ^ 2 *
        winProbability (inversionGame f (wordInverter f evaluate c d degree) n) := by
  classical
  simp only [winProbability, eval_predictionGame f finiteFunction encodeImage hf hlength
    adversary evaluate c d hrealize,
    eval_wordInversionGame f finiteFunction encodeImage hf hlength evaluate c d degree]
  exact matrixPrediction_entropy_le_of_coins finiteFunction (hashCount_ge n) _ _ _ hp

end Cslib.Crypto.Pseudoentropy.HashPair
