/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GoldreichLevin.Parameters
public import Cslib.Crypto.Computational.OneWay
public import Cslib.Computability.Probabilistic.CoinTape

/-!
# Goldreich–Levin as a word-based probabilistic program

`wordInverter` is one program for every input length. Its fixed parameters are the predictor's
seed-length polynomial and a precision degree. It samples a sign bit, a single predictor tape,
and a flat tape of independent masks, then runs the decoder and checks its candidates.
The matrix view of that flat tape is proved exactly uniform; no sampling oracle is assumed.

The program receives only the image and security parameter. Malformed image lengths return
the empty word. For length-preserving functions, its game is exactly the finite inversion
experiment, and the predictor's word game is exactly the finite parity-prediction experiment.

`word_prediction_advantage_le` is the concrete reduction bound. The final asymptotic lemma
uses the existing `OneWay` definition and exposes the remaining hypothesis:
`∀ degree, IsPPT wordEncoding (wordInverter f evaluate c d degree)`.
The seeded predictor evaluator and all random-tape lengths already have polynomial certificates
or size bounds. Compiling the decoder and candidate search into a uniform PPT machine remains
necessary; this module does not infer efficiency from high-level Lean computations.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability
/-- View a word as `n` coordinates, using false for missing bits. Valid lengths lose no data. -/
def wordBits (n : ℕ) (word : Word) : BitString n := fun i => word[i.val]?.getD false

/-- A finite bitstring survives the word representation unchanged. -/
@[simp] theorem wordBits_ofFn {n : ℕ} (bits : BitString n) :
    wordBits n (List.ofFn bits) = bits := by
  funext i
  simp [wordBits]

/-- A correctly sized word survives the finite-coordinate representation unchanged. -/
theorem ofFn_wordBits {n : ℕ} {word : Word} (hlen : word.length = n) :
    List.ofFn (wordBits n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits, List.getElem?_eq_getElem hi']

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

/-- Evaluate the predictor with the same private tape for every parity query. -/
def fixedPredictor (evaluate : Word → Word → Word) (c d n : ℕ)
    (image : BitString n) (coins : BitString (coinBudget c d n)) (query : BitString n) : Bool :=
  (evaluate (List.ofFn coins)
    (parameterInput n (List.ofFn image ++ List.ofFn query))).headD false

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

/-- The row-major bijection between a flat bitstring and a matrix of masks. -/
def maskEquiv (k n : ℕ) : BitString (k * n) ≃ (Fin k → BitString n) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin k) (Fin n) Bool)

/-- Interpret a flat sampled word as the decoder's base masks. -/
def masksFromWord (k n : ℕ) (word : Word) : Fin k → BitString n :=
  maskEquiv k n (wordBits (k * n) word)

/-- A flat tape of `k * n` uniform bits supplies exactly `k` independent uniform masks. -/
theorem uniformBits_masksFromWord (k n : ℕ) :
    (uniformBits (k * n)).map (masksFromWord k n) =
      PMF.uniformOfFintype (Fin k → BitString n) := by
  change (uniformBits (k * n)).map ((maskEquiv k n) ∘ wordBits (k * n)) = _
  rw [← PMF.map_comp, uniformBits_wordBits]
  exact PMF.uniformOfFintype_map_equiv (maskEquiv k n)

/-- The Goldreich–Levin inverter as a probabilistic program. It uses explicit uniform bit tapes
and one fixed precision degree across all parameters. No PPT certificate is asserted here. -/
noncomputable def wordInverter (f : Word → Word) (evaluate : Word → Word → Word)
    (c d degree : ℕ) : Inverter := fun n image =>
  if image.length = n then do
    let flip ← OracleComp.uniform Bool
    let coins ← OracleComp.sample (uniformBits (coinBudget c d n))
    let maskWord ← OracleComp.sample (uniformBits (maskCount n (precision degree n) * n))
    let masks := masksFromWord (maskCount n (precision degree n)) n maskWord
    return List.ofFn (checkCandidates (functionAtLength f n) (wordBits n image)
      (candidateList (fun query => fixedPredictor evaluate c d n (wordBits n image)
        (wordBits (coinBudget c d n) coins) query
        ^^ flip) masks))
  else pure []

/-- On a well-formed image, the word program is exactly the finite seeded inverter. -/
theorem wordInverter_eval (f : Word → Word) (evaluate : Word → Word → Word)
    (c d degree n : ℕ) (image : BitString n) :
    ProbComp.eval (wordInverter f evaluate c d degree n (List.ofFn image)) =
      (invertSigned (functionAtLength f n) (fixedPredictor evaluate c d n)
        (PMF.uniformOfFintype (BitString (coinBudget c d n)))
        (maskCount n (precision degree n)) image).map List.ofFn := by
  simp only [wordInverter, List.length_ofFn, ↓reduceIte, ProbComp.eval_bind,
    OracleComp.uniform, ProbComp.eval_sample, ProbComp.eval_pure, wordBits_ofFn,
    invertSigned, invert, invertFixed]
  rw [← uniformBits_wordBits (coinBudget c d n),
    ← uniformBits_masksFromWord (maskCount n (precision degree n)) n]
  simp [PMF.map, PMF.bind_bind, Function.comp_def]

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
      wordInverter_eval f evaluate c d degree n (functionAtLength f n x)
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

/-- One-wayness rules out parity prediction once every fixed-precision inverter is certified PPT.
The explicit efficiency hypothesis is the remaining machine-implementation obligation. -/
theorem negligible_parityPrediction_of_inverters (f : Word → Word)
    (hf : OneWay f) (hlen : ∀ word, (f word).length = word.length)
    (adversary : Distinguisher) (evaluate : Word → Word → Word) (c d : ℕ)
    (hrealize : ∀ n input, ProbComp.eval (adversary n input) =
      (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
        (fun coins => (evaluate coins (parameterInput n input)).headD false))
    (hPPT : ∀ degree, IsPPT wordEncoding (wordInverter f evaluate c d degree)) :
    Negligible (fun n => |winProbability (parityPredictionGame f adversary n) - 1 / 2|) := by
  simp only [winProbability, eval_parityPredictionGame f hlen adversary evaluate c d hrealize]
  apply negligible_prediction_of_negligible_inversion
  intro degree
  simpa only [winProbability, eval_wordInversionGame f hlen] using
    hf.2 (wordInverter f evaluate c d degree) (hPPT degree)


/-- The predictor's random-tape budget is polynomial in the security parameter. -/
theorem coinBudget_polynomial (c d : ℕ) : PolynomiallyBounded (coinBudget c d) :=
  (PolynomiallyBounded.const c).mul
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 2) |>.pow d)

/-- The three random samples use polynomially many bits at each fixed precision degree.
This size bound does not account for the decoder's local computation. -/
theorem inverter_randomBits_polynomial (c d degree : ℕ) :
    PolynomiallyBounded (fun n => 1 + coinBudget c d n + maskCount n (precision degree n) * n) := by
  have hm : PolynomiallyBounded (fun n => maskCount n (precision degree n) * n) := by
    simpa only [Nat.mul_comm] using randomMaskBits_polynomial degree
  exact ((PolynomiallyBounded.const 1).add (coinBudget_polynomial c d)).add hm

/-- A PPT predictor supplies one efficient seeded evaluator and a reduction bound at every
fixed precision degree. Efficiency of the full inverter remains to be certified separately. -/
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
