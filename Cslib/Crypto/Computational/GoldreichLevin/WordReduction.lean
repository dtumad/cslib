/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GoldreichLevin.WordDecoder
public import Cslib.Crypto.Computational.OneWay
public import Cslib.Computability.Probabilistic.CoinTape
public import Cslib.Computability.Probabilistic.Parameter
public import Cslib.Tactic.PPT

/-!
# Goldreich–Levin as a word-based probabilistic program

`wordInverter` is one program for every input length. Its fixed parameters are the predictor's
seed-length polynomial and a precision degree. It samples a sign bit, a single predictor tape,
and a flat tape of independent masks, then runs the decoder and checks its candidates.
The matrix view of that flat tape is proved exactly uniform; no sampling oracle is assumed.

The program receives only the image and security parameter. Image lengths are unrestricted:
the predictor tape length depends on the image, while recovered candidates have the original
input length. Both word games agree exactly with their finite experiments.

`wordInverter_isPPT` composes the deterministic decoder's certificate with sampling, using `ppt`.
`word_prediction_advantage_le` is the concrete reduction bound; `negligible_parityPrediction`
derives the asymptotic Goldreich–Levin theorem from the existing `OneWay` and `IsPPT` definitions.
The computational proof charges for saved coins, captured inputs, and every decoder operation.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability

/-- Coin budget for parameter `n`, an arbitrary image, and an independent `n`-bit query. -/
def coinBudget (c d n imageLength : ℕ) : ℕ := c * (2 * n + imageLength + 2) ^ d

/-- Query a predictor using a saved coin tape, the image, and a fresh parity mask. -/
def predictWithCoins (evaluate : Word → Word → Word) (n : ℕ)
    (image coins query : Word) : Bool :=
  (evaluate coins (parameterInput n (image ++ query))).headD false

/-- A predictor call is efficient when its coins, parameter, image, and query are efficiently
available. This contract is uniform in their lengths and exposes no machine witnesses. -/
theorem predictWithCoins_isPolyTime {α : Type} {encode : α → Word}
    {evaluate : Word → Word → Word} {parameter : α → ℕ} {image coins query : α → Word}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2))
    (hparameter : IsPolyTime encode (fun a => List.replicate (parameter a) true))
    (himage : IsPolyTime encode image) (hcoins : IsPolyTime encode coins)
    (hquery : IsPolyTime encode query) :
    IsPolyTime encode (fun a => [predictWithCoins evaluate (parameter a)
      (image a) (coins a) (query a)]) :=
  (hevaluate.comp_pair hcoins (hparameter.parameterInput (himage.append hquery))).headD false

attribute [aesop safe apply (rule_sets := [PolyTime])] predictWithCoins_isPolyTime

/-- Evaluate a collection of parity queries while capturing one parameter, image, and coin tape.
The resulting word of votes is available directly to the decoder's majority operation. -/
theorem predictWithCoins_votes_isPolyTime {evaluate : Word → Word → Word}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2)) :
    IsPolyTime (pairEncoding (pairEncoding unaryEncoding coinInputEncoding)
      (listEncoding wordEncoding)) (fun input => input.2.map (fun query =>
        predictWithCoins evaluate input.1.1 input.1.2.1 input.1.2.2 query)) := by
  polytime

/-- Decode with a saved predictor tape and mask tape, then check the generated candidates. -/
def decodeWithCoins (f : Word → Word) (evaluate : Word → Word → Word) (degree n : ℕ)
    (image coins : Word) (flip : Bool) (maskWord : Word) : Word :=
  wordDecode f (fun query => predictWithCoins evaluate n image coins query ^^ flip)
    degree n image maskWord

/-- The full deterministic decoder composes its predictor, matrix reader, guess enumeration,
and candidate check. Captured inputs need only ordinary efficiency certificates. -/
theorem decodeWithCoins_isPolyTime {α : Type} {encode : α ↪ Word} {f : Word → Word}
    {evaluate : Word → Word → Word} {parameter : α → ℕ} {image coins masks : α → Word}
    {flip : α → Bool} (degree : ℕ) (hf : IsPolyTime wordEncoding f)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2))
    (hparameter : IsPolyTime encode (fun a => List.replicate (parameter a) true))
    (himage : IsPolyTime encode image) (hcoins : IsPolyTime encode coins)
    (hflip : IsPolyTime encode (fun a => [flip a])) (hmasks : IsPolyTime encode masks) :
    IsPolyTime encode (fun a => decodeWithCoins f evaluate degree (parameter a)
      (image a) (coins a) (flip a) (masks a)) := by
  unfold decodeWithCoins
  apply wordDecode_isPolyTime degree hf
  · polytime
  · exact hparameter
  · exact himage
  · exact hmasks

attribute [aesop safe -20 apply (rule_sets := [PolyTime])] decodeWithCoins_isPolyTime

/-- Evaluate the predictor with the same private tape for every parity query. -/
def fixedPredictor (evaluate : Word → Word → Word) (c d n : ℕ)
    (image : Word) (coins : BitString (coinBudget c d n image.length))
    (query : BitString n) : Bool :=
  predictWithCoins evaluate n image (List.ofFn coins) (List.ofFn query)

/-- The ordinary word decoder agrees with the finite decoder on encoded inputs and coins. -/
theorem decodeWithCoins_eq_ofFn (f : Word → Word)
    (evaluate : Word → Word → Word)
    (c d degree n : ℕ) (image : Word) (coins : BitString (coinBudget c d n image.length))
    (flip : Bool) (maskWord : Word) :
    decodeWithCoins f evaluate degree n image (List.ofFn coins) flip maskWord =
      List.ofFn (checkCandidates (fun bits => f (List.ofFn bits)) image
        (candidateList (fun query => fixedPredictor evaluate c d n image coins query ^^ flip)
          (masksFromWord (maskCount n (precision degree n)) n maskWord))) := by
  exact wordDecode_eq_ofFn f _ degree n image maskWord

/-- Predict the inner product of two uniform words, given the first word's image and the second. -/
noncomputable def parityPredictionGame (f : Word → Word) (adversary : Distinguisher)
    (n : ℕ) : ProbComp Bool := do
  let x ← OracleComp.sample (uniformBits n)
  let query ← OracleComp.sample (uniformBits n)
  let guess ← adversary n (f x ++ query)
  return guess == wordBits n x ⬝ᵥ wordBits n query

/-- The Goldreich–Levin inverter samples three independent tapes and runs the word decoder.
The precision degree is fixed across all security parameters. -/
noncomputable def wordInverter (f : Word → Word) (evaluate : Word → Word → Word)
    (c d degree : ℕ) : Inverter := fun n image => do
  let flip ← OracleComp.uniform Bool
  let coins ← OracleComp.sampleBits (coinBudget c d n image.length)
  let maskWord ← OracleComp.sampleBits (maskCount n (precision degree n) * n)
  return decodeWithCoins f evaluate degree n image coins flip maskWord

set_option maxHeartbeats 800000 in
-- The certificate composes three captured samples and the complete decoder.
/-- The uniform inverter is PPT whenever the function and saved-coin predictor evaluator are
polynomial-time. Sampling, captured inputs, and decoder calls compose through the public API. -/
theorem wordInverter_isPPT {f : Word → Word} {evaluate : Word → Word → Word}
    (hf : IsPolyTime wordEncoding f)
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2))
    (c d degree : ℕ) : IsPPT wordEncoding (wordInverter f evaluate c d degree) := by
  unfold wordInverter coinBudget
  ppt

/-- At every image length, the word program is exactly the finite seeded inverter. -/
theorem wordInverter_eval (f : Word → Word)
    (evaluate : Word → Word → Word)
    (c d degree n : ℕ) (image : Word) :
    ProbComp.eval (wordInverter f evaluate c d degree n image) =
      (invertSigned (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
        (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length)))
        (maskCount n (precision degree n)) image).map List.ofFn := by
  simp only [wordInverter, ProbComp.eval, OracleComp.eval_bind, OracleComp.uniform,
    OracleComp.eval_sample, OracleComp.eval_sampleBits, OracleComp.eval_pure,
    invertSigned, invert, invertFixed]
  rw [← uniformBits_wordBits (coinBudget c d n image.length),
    ← uniformBits_masksFromWord (maskCount n (precision degree n)) n]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro flip _
  apply PMF.bind_congr_on_support
  intro coins hcoins
  apply PMF.bind_congr_on_support
  intro masks _
  congr 1
  convert decodeWithCoins_eq_ofFn f evaluate c d degree n image
    (wordBits (coinBudget c d n image.length) coins) flip masks using 1
  rw [ofFn_wordBits (length_of_mem_support_uniformBits hcoins)]

/-- Fixed-coin evaluation preserves prediction distributions, including variable-length images. -/
theorem fixedPredictor_distribution (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (n : ℕ) (image : Word) (query : BitString n) :
    (PMF.uniformOfFintype (BitString (coinBudget c d n image.length))).map
        (fun coins => fixedPredictor evaluate c d n image coins query) =
      ProbComp.eval (adversary n (image ++ List.ofFn query)) := by
  rw [hrealize]
  have hlen : (parameterInput n (image ++ List.ofFn query)).length + 1 =
      2 * n + image.length + 2 := by simp; lia
  rw [hlen]
  simp only [uniformBits, PMF.map_comp, Function.comp_def, coinBudget, fixedPredictor]
  rfl

/-- The word-based prediction game is exactly the finite experiment. The private seed depends
on the image, but is independent of the parity query and can be reused by the reduction. -/
theorem eval_parityPredictionGame (f : Word → Word) (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (n : ℕ) :
    ProbComp.eval (parityPredictionGame f adversary n) =
      predictionExperiment (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
        (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length))) := by
  simp only [parityPredictionGame, ProbComp.eval_bind, ProbComp.eval_sample,
    ProbComp.eval_pure, uniformBits, PMF.bind_map, Function.comp_def,
    wordBits_ofFn, predictionExperiment]
  congr 1
  funext x
  simp_rw [← fixedPredictor_distribution adversary evaluate c d hrealize,
    PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  rfl

/-- The existing one-wayness game agrees exactly with the finite inversion experiment. -/
theorem eval_wordInversionGame (f : Word → Word)
    (evaluate : Word → Word → Word) (c d degree n : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment (fun bits => f (List.ofFn bits))
        (invertSigned (fun bits => f (List.ofFn bits)) (fixedPredictor evaluate c d n)
          (fun image => PMF.uniformOfFintype (BitString (coinBudget c d n image.length)))
          (maskCount n (precision degree n))) := by
  simp only [inversionGame, ProbComp.eval_bind, ProbComp.eval_sample, ProbComp.eval_pure,
    uniformBits, PMF.bind_map, Function.comp_def, inversionExperiment, wordInverter_eval,
    beq_eq_decide]
  rfl

/-- Prediction bias is bounded by inverse-polynomial error plus eight times inversion success. -/
theorem word_prediction_advantage_le (f : Word → Word)
    (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (degree n : ℕ) :
    |winProbability (parityPredictionGame f adversary n) - 1 / 2| ≤
      1 / (precision degree n : ℝ) +
        8 * winProbability (inversionGame f (wordInverter f evaluate c d degree) n) := by
  simp only [winProbability, eval_parityPredictionGame f adversary evaluate c d hrealize,
    eval_wordInversionGame f]
  exact invertSigned_advantage_le _ _ _ _ (precision_pos degree n)

/-- The Goldreich–Levin theorem for word programs: no uniform PPT adversary predicts the parity
of a random mask with the input of any one-way function with nonnegligible bias. -/
theorem negligible_parityPrediction {f : Word → Word}
    (hf : OneWay f)
    (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) :
    Negligible (fun n => |winProbability (parityPredictionGame f adversary n) - 1 / 2|) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.exists_bool_polyTime_coin_evaluator
  simp only [winProbability, eval_parityPredictionGame f adversary evaluate c d hrealize]
  apply negligible_prediction_of_negligible_inversion
  intro degree
  simpa only [winProbability, eval_wordInversionGame f] using
    hf.inversion_negligible _ (wordInverter_isPPT hf.polyTime hefficient c d degree)

/-- A PPT predictor supplies one efficient seeded evaluator and a reduction bound at every
fixed precision degree. `wordInverter_isPPT` certifies each resulting reduction. -/
theorem exists_word_reduction (f : Word → Word)
    (adversary : Distinguisher)
    (hPPT : IsPPT boolEncoding adversary) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ degree n, |winProbability (parityPredictionGame f adversary n) - 1 / 2| ≤
        1 / (precision degree n : ℝ) +
          8 * winProbability (inversionGame f (wordInverter f evaluate c d degree) n) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.exists_bool_polyTime_coin_evaluator
  exact ⟨c, d, evaluate, hefficient,
    fun degree n => word_prediction_advantage_le f adversary evaluate c d hrealize degree n⟩

end Cslib.Crypto.GoldreichLevin
