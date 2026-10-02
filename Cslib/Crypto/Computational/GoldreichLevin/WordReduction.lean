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

The program receives only the image and security parameter. Malformed image lengths return
the empty word. For length-preserving functions, its game is exactly the finite inversion
experiment, and the predictor's word game is exactly the finite parity-prediction experiment.

`wordInverter_isPPT` composes the deterministic decoder's certificate with sampling, using `ppt`.
`word_prediction_advantage_le` is the concrete reduction bound; `negligible_parityPrediction`
derives the asymptotic Goldreich–Levin theorem from the existing `OneWay` and `IsPPT` definitions.
The computational proof charges for saved coins, captured inputs, and every decoder operation.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability

/-- Restrict a word function to `n`-bit inputs and outputs. -/
def functionAtLength (f : Word → Word) (n : ℕ) : BitString n → BitString n :=
  fun bits => wordBits n (f (List.ofFn bits))

/-- The finite restriction is exact for a length-preserving function. -/
theorem ofFn_functionAtLength (f : Word → Word) (hlen : ∀ word, (f word).length = word.length)
    {n : ℕ} (x : BitString n) :
    List.ofFn (functionAtLength f n x) = f (List.ofFn x) :=
  ofFn_wordBits (by simp [hlen])

/-- The predictor sees parameter `n` and `2 * n` challenge bits. -/
def coinBudget (c d n : ℕ) : ℕ := c * (3 * n + 2) ^ d

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
  wordCheckCandidates f image (wordCandidates
    (fun query => predictWithCoins evaluate n image coins query ^^ flip) n
    (maskRows (maskCount n (precision degree n)) n maskWord)
    (guessWords (maskCount n (precision degree n))))
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
  apply wordCheckCandidates_isPolyTime hf himage
  apply wordCandidates_isPolyTime (environment := encode) (env := id)
    (predictor := fun a query => predictWithCoins evaluate (parameter a)
      (image a) (coins a) query ^^ flip a)
  · polytime
  · exact isPolyTime_input encode
  · exact hparameter
  · exact maskRows_isPolyTime.comp_encoded
      (((maskCount_isPolyTime hparameter (precision_isPolyTime hparameter degree)).pair
        (left := unaryEncoding) (right := unaryEncoding) hparameter).pair hmasks)
  · exact guessWords_maskCount_isPolyTime hparameter degree

attribute [aesop safe -20 apply (rule_sets := [PolyTime])] decodeWithCoins_isPolyTime


/-- Evaluate the predictor with the same private tape for every parity query. -/
def fixedPredictor (evaluate : Word → Word → Word) (c d n : ℕ)
    (image : BitString n) (coins : BitString (coinBudget c d n)) (query : BitString n) : Bool :=
  predictWithCoins evaluate n (List.ofFn image) (List.ofFn coins) (List.ofFn query)

/-- The ordinary word decoder agrees with the finite decoder on encoded inputs and coins. -/
theorem decodeWithCoins_eq_ofFn (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (evaluate : Word → Word → Word)
    (c d degree n : ℕ) (image : BitString n) (coins : BitString (coinBudget c d n))
    (flip : Bool) (maskWord : Word) :
    decodeWithCoins f evaluate degree n (List.ofFn image) (List.ofFn coins) flip maskWord =
      List.ofFn (checkCandidates (functionAtLength f n) image
        (candidateList (fun query => fixedPredictor evaluate c d n image coins query ^^ flip)
          (masksFromWord (maskCount n (precision degree n)) n maskWord))) := by
  simp only [decodeWithCoins, maskRows_eq_ofFn, wordCandidates_eq_map]
  exact wordCheckCandidates_eq_ofFn f (functionAtLength f n)
    (fun bits => (ofFn_functionAtLength f hlen bits).symm) image _

/-- Predict the inner product of two uniform words, given the first word's image and the second. -/
noncomputable def parityPredictionGame (f : Word → Word) (adversary : Distinguisher)
    (n : ℕ) : ProbComp Bool := do
  let x ← OracleComp.sample (uniformBits n)
  let query ← OracleComp.sample (uniformBits n)
  let guess ← adversary n (f x ++ query)
  return guess == wordBits n x ⬝ᵥ wordBits n query


/-- Uniform words become exactly uniform finite bitstrings. -/
theorem uniformBits_wordBits (n : ℕ) :
    (uniformBits n).map (wordBits n) = PMF.uniformOfFintype (BitString n) := by
  simp only [uniformBits, PMF.map_comp, Function.comp_def, wordBits_ofFn]
  exact PMF.map_id _

/-- A flat tape of `k * n` uniform bits supplies exactly `k` independent uniform masks. -/
theorem uniformBits_masksFromWord (k n : ℕ) :
    (uniformBits (k * n)).map (masksFromWord k n) =
      PMF.uniformOfFintype (Fin k → BitString n) := by
  change (uniformBits (k * n)).map ((maskEquiv k n) ∘ wordBits (k * n)) = _
  rw [← PMF.map_comp, uniformBits_wordBits]
  exact PMF.uniformOfFintype_map_equiv (maskEquiv k n)

/-- The Goldreich–Levin inverter samples three independent tapes and runs the word decoder.
The precision degree is fixed across all security parameters. -/
noncomputable def wordInverter (f : Word → Word) (evaluate : Word → Word → Word)
    (c d degree : ℕ) : Inverter := fun n image =>
  if image.length = n then do
    let flip ← OracleComp.uniform Bool
    let coins ← OracleComp.sample (uniformBits (coinBudget c d n))
    let maskWord ← OracleComp.sample (uniformBits (maskCount n (precision degree n) * n))
    return decodeWithCoins f evaluate degree n image coins flip maskWord
  else pure []

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

/-- On a well-formed image, the word program is exactly the finite seeded inverter. -/
theorem wordInverter_eval (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (evaluate : Word → Word → Word)
    (c d degree n : ℕ) (image : BitString n) :
    ProbComp.eval (wordInverter f evaluate c d degree n (List.ofFn image)) =
      (invertSigned (functionAtLength f n) (fixedPredictor evaluate c d n)
        (PMF.uniformOfFintype (BitString (coinBudget c d n)))
        (maskCount n (precision degree n)) image).map List.ofFn := by
  simp only [wordInverter, List.length_ofFn, ↓reduceIte, ProbComp.eval_bind,
    OracleComp.uniform, ProbComp.eval_sample, ProbComp.eval_pure,
    invertSigned, invert, invertFixed]
  rw [← uniformBits_wordBits (coinBudget c d n),
    ← uniformBits_masksFromWord (maskCount n (precision degree n)) n]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro flip _
  apply PMF.bind_congr_on_support
  intro coins hcoins
  apply PMF.bind_congr_on_support
  intro masks _
  congr 1
  convert decodeWithCoins_eq_ofFn f hlen evaluate c d degree n image
    (wordBits (coinBudget c d n) coins) flip masks using 1
  rw [ofFn_wordBits (length_of_mem_support_uniformBits hcoins)]

/-- Fixed-coin evaluation preserves each prediction distribution on correctly sized inputs. -/
theorem fixedPredictor_distribution (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (n : ℕ) (image query : BitString n) :
    (PMF.uniformOfFintype (BitString (coinBudget c d n))).map
        (fun coins => fixedPredictor evaluate c d n image coins query) =
      ProbComp.eval (adversary n (List.ofFn image ++ List.ofFn query)) := by
  rw [hrealize]
  have hlen : (parameterInput n (List.ofFn image ++ List.ofFn query)).length + 1 = 3 * n + 2 := by
    simp
    omega
  rw [hlen]
  simp only [uniformBits, PMF.map_comp, Function.comp_def, coinBudget, fixedPredictor]
  rfl


/-- The word-based prediction game is exactly the finite experiment. A private seed may be
sampled before the independent query and reused by the reduction. -/
theorem eval_parityPredictionGame (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (n : ℕ) :
    ProbComp.eval (parityPredictionGame f adversary n) =
      predictionExperiment (functionAtLength f n) (fixedPredictor evaluate c d n)
        (PMF.uniformOfFintype (BitString (coinBudget c d n))) := by
  simp only [parityPredictionGame, ProbComp.eval_bind, ProbComp.eval_sample,
    ProbComp.eval_pure, uniformBits, PMF.bind_map, Function.comp_def,
    wordBits_ofFn, predictionExperiment]
  congr 1
  funext x
  have hdistribution (query : BitString n) :
      ProbComp.eval (adversary n (f (List.ofFn x) ++ List.ofFn query)) =
        (PMF.uniformOfFintype (BitString (coinBudget c d n))).map
          (fun seed => fixedPredictor evaluate c d n (functionAtLength f n x) seed query) := by
    simpa only [ofFn_functionAtLength f hlen] using
      (fixedPredictor_distribution adversary evaluate c d hrealize n
        (functionAtLength f n x) query).symm
  simp_rw [hdistribution, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  rfl

/-- Testing images in coordinates agrees with testing the complete output words. -/
theorem functionAtLength_beq (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) {n : ℕ} (x z : BitString n) :
    (f (List.ofFn z) == f (List.ofFn x)) =
      (functionAtLength f n z == functionAtLength f n x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    exact congrArg (wordBits n) h
  · intro h
    have hh := congrArg List.ofFn h
    simpa only [ofFn_functionAtLength f hlen] using hh

/-- The existing one-wayness game agrees exactly with the finite inversion experiment. -/
theorem eval_wordInversionGame (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length)
    (evaluate : Word → Word → Word) (c d degree n : ℕ) :
    ProbComp.eval (inversionGame f (wordInverter f evaluate c d degree) n) =
      inversionExperiment (functionAtLength f n)
        (invertSigned (functionAtLength f n) (fixedPredictor evaluate c d n)
          (PMF.uniformOfFintype (BitString (coinBudget c d n)))
          (maskCount n (precision degree n))) := by
  simp only [inversionGame, ProbComp.eval_bind, ProbComp.eval_sample, ProbComp.eval_pure,
    uniformBits, PMF.bind_map, Function.comp_def, inversionExperiment]
  congr 1
  funext x
  have hrun : ProbComp.eval (wordInverter f evaluate c d degree n (f (List.ofFn x))) =
      (invertSigned (functionAtLength f n) (fixedPredictor evaluate c d n)
        (PMF.uniformOfFintype (BitString (coinBudget c d n)))
        (maskCount n (precision degree n)) (functionAtLength f n x)).map List.ofFn := by
    simpa only [ofFn_functionAtLength f hlen] using
    wordInverter_eval f hlen evaluate c d degree n (functionAtLength f n x)
  rw [hrun]
  simp only [PMF.bind_map, Function.comp_def, functionAtLength_beq f hlen]
  rfl

/-- Prediction bias is bounded by inverse-polynomial error plus eight times inversion success. -/
theorem word_prediction_advantage_le (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (adversary : Distinguisher)
    (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (degree n : ℕ) :
    |winProbability (parityPredictionGame f adversary n) - 1 / 2| ≤
      1 / (precision degree n : ℝ) +
        8 * winProbability (inversionGame f (wordInverter f evaluate c d degree) n) := by
  simp only [winProbability, eval_parityPredictionGame f hlen adversary evaluate c d hrealize,
    eval_wordInversionGame f hlen]
  exact invertSigned_advantage_le _ _ _ _ (precision_pos degree n)

/-- The Goldreich–Levin theorem for word programs: no uniform PPT adversary predicts the parity
of a random mask with the input of a length-preserving one-way function with nonnegligible bias. -/
theorem negligible_parityPrediction {f : Word → Word}
    (hf : OneWay f) (hlen : ∀ word, (f word).length = word.length)
    (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) :
    Negligible (fun n => |winProbability (parityPredictionGame f adversary n) - 1 / 2|) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.exists_bool_polyTime_coin_evaluator
  simp only [winProbability, eval_parityPredictionGame f hlen adversary evaluate c d hrealize]
  apply negligible_prediction_of_negligible_inversion
  intro degree
  simpa only [winProbability, eval_wordInversionGame f hlen] using
    hf.2 _ (wordInverter_isPPT hf.1 hefficient c d degree)


/-- The predictor's random-tape budget is polynomial in the security parameter. -/
theorem coinBudget_polynomial (c d : ℕ) : PolynomiallyBounded (coinBudget c d) := by
  unfold coinBudget
  fun_prop

/-- The three random samples use polynomially many bits at each fixed precision degree.
This size bound does not account for the decoder's local computation. -/
theorem inverter_randomBits_polynomial (c d degree : ℕ) :
    PolynomiallyBounded (fun n => 1 + coinBudget c d n + maskCount n (precision degree n) * n) := by
  have hm : PolynomiallyBounded (fun n => maskCount n (precision degree n) * n) := by
    simpa only [Nat.mul_comm] using randomMaskBits_polynomial degree
  have := coinBudget_polynomial c d
  fun_prop

/-- A PPT predictor supplies one efficient seeded evaluator and a reduction bound at every
fixed precision degree. `wordInverter_isPPT` certifies each resulting reduction. -/
theorem exists_word_reduction (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (adversary : Distinguisher)
    (hPPT : IsPPT boolEncoding adversary) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ degree n, |winProbability (parityPredictionGame f adversary n) - 1 / 2| ≤
        1 / (precision degree n : ℝ) +
          8 * winProbability (inversionGame f (wordInverter f evaluate c d degree) n) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := hPPT.exists_bool_polyTime_coin_evaluator
  exact ⟨c, d, evaluate, hefficient,
    fun degree n => word_prediction_advantage_le f hlen adversary evaluate c d hrealize degree n⟩

end Cslib.Crypto.GoldreichLevin
