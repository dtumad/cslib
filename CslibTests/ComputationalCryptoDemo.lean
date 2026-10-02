/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Cslib.Computability.Probabilistic.Sampling
import Cslib.Computability.Probabilistic.Output
import Cslib.Computability.Probabilistic.Composition
import Cslib.Computability.Probabilistic.CoinTape
import Cslib.Tactic.PPT
import Cslib.Crypto.Computational.Hybrid
import Cslib.Crypto.Computational.HardCore
import Cslib.Crypto.Computational.GoldreichLevin.WordReduction
import Cslib.Crypto.Computational.OneWay
import Cslib.Crypto.Computational.PseudorandomGenerator

/-!
# A small computational cryptography walkthrough
These examples show the intended interface for cryptographic proofs: write programs using `do`,
certify efficiency with named theorems, and reason about advantages. The machine implementations
and their tape invariants are in the imported library.
The examples establish uniform sampling, efficient fixed output encodings, PPT sequencing,
the ideal-distribution identity for a one-way permutation, the hard-core prediction reduction,
a concrete answer-complementing reduction, and a polynomial hybrid argument under an explicit
common hop bound. The finite Goldreich–Levin decoder has a list-size and recovery guarantee,
and its seeded randomized reduction converts prediction bias into inversion success in the
word-based security game, with an explicit inverse-polynomial precision.
The complete one-bit PRG theorem assumes a hard-core predicate. The Goldreich–Levin reduction's
machine implementation and efficiency remain, so the full OWP-to-PRG construction is incomplete.
-/

namespace CslibTests.ComputationalCryptoDemo

open Cslib Cslib.Probability Cslib.Crypto
noncomputable section

/-- A uniform seed is a program with a machine-checked PPT certificate. -/
def randomSeed (n : ℕ) (_ : Word) : ProbComp Word := OracleComp.sampleBits n

theorem randomSeed_isPPT : IsPPT wordEncoding randomSeed := isPPT_sampleBits

theorem randomSeed_distribution (n : ℕ) :
    ProbComp.eval (randomSeed n []) = uniformBits n := by
  simp [randomSeed, ProbComp.eval]

/-- A fixed bit encoding can be applied to a sampled word without exposing the machine proof. -/
def encodedSeed (code : Bool → Word) (n : ℕ) (input : Word) : ProbComp Word := do
  let seed ← randomSeed n input
  return seed.flatMap code

theorem encodedSeed_isPPT (code : Bool → Word) : IsPPT wordEncoding (encodedSeed code) := by
  apply (randomSeed_isPPT.flatMap_word code).congr
  intro n input
  simp [encodedSeed]

theorem encodedSeed_distribution (code : Bool → Word) (n : ℕ) :
    ProbComp.eval (encodedSeed code n []) = (uniformBits n).map (List.flatMap code) := by
  simp [encodedSeed, randomSeed_distribution]

/-- A preceding computation can choose the parameter of the next random sample. Its certificate
accounts for writing the complete unary parameter and auxiliary-input encoding. -/
def samplePrepared (prepare : ℕ → Word → ProbComp (ℕ × Word)) (n : ℕ) (input : Word) :
    ProbComp Word := do
  let (length, _) ← prepare n input
  OracleComp.sampleBits length

theorem samplePrepared_isPPT (prepare : ℕ → Word → ProbComp (ℕ × Word))
    (hprepare : IsPPT parameterEncoding prepare) : IsPPT wordEncoding (samplePrepared prepare) :=
  hprepare.bind_parameter isPPT_sampleBits

/-- Run an adversary on a fresh seed, retaining the security parameter automatically. -/
def sampleThenDistinguish (adversary : Distinguisher) (n : ℕ) (input : Word) : ProbComp Bool := do
  let seed ← randomSeed n input
  adversary n seed

theorem sampleThenDistinguish_isPPT (adversary : Distinguisher)
    (hadversary : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (sampleThenDistinguish adversary) :=
  randomSeed_isPPT.bind hadversary

/-- A PPT program is a polynomial-time deterministic computation supplied with a uniform
polynomial-length random tape. One evaluator and one polynomial work for all inputs. -/
theorem polynomialRandomTape (program : ℕ → Word → ProbComp Word)
    (hprogram : IsPPT wordEncoding program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ n input, ProbComp.eval (program n input) =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => evaluate coins (parameterInput n input)) := by
  simpa [wordEncoding, Function.Embedding.coe_refl, PMF.map_id] using
    hprogram.exists_polyTime_coin_evaluator

/-- The PRG experiment can be written directly as a probabilistic program. -/
def generatorExperiment (generator : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := do
  let seed ← randomSeed n []
  adversary n (generator seed)

/-- The experiment is PPT by composition of its sampler, generator, and adversary certificates. -/
theorem generatorExperiment_isPPT (generator : Word → Word) (adversary : Distinguisher)
    (hgenerator : IsPolyTime wordEncoding generator) (hadversary : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (fun n _ => generatorExperiment generator adversary n) := by
  unfold generatorExperiment randomSeed
  ppt

theorem generatorExperiment_eq (generator : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (generatorExperiment generator adversary n) =
      ProbComp.eval (prgRealGame generator adversary n) := by
  simp [generatorExperiment, randomSeed_distribution, prgRealGame, distinguishingGame,
    generatorEnsemble, PMF.bind_map, Function.comp_def]

/-- The ideal side of the one-bit construction uses a fresh bit independent of the seed. -/
def idealPermutationOutput (f : Word → Word) (n : ℕ) : ProbComp Word := do
  let seed ← OracleComp.sampleBits n
  let bit ← OracleComp.uniform Bool
  return f seed ++ [bit]

/-- The permutation preserves uniformity, so this ideal output is exactly uniform. -/
theorem idealPermutationOutput_uniform (f : Word → Word) (hf : OneWayPermutation f) (n : ℕ) :
    ProbComp.eval (idealPermutationOutput f n) = uniformBits (n + 1) := by
  simpa [idealPermutationOutput, ProbComp.eval, OracleComp.uniform, PMF.map]
    using hf.uniformBits_append_bit n

/-- Append a trial bit and use the distinguisher's answer to predict the hidden predicate.
Input preparation and Boolean postprocessing both have machine certificates. -/
example (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) (trial : Bool) :
    IsPPT boolEncoding (hardCorePredictor adversary trial) :=
  hardCorePredictor_isPPT hPPT trial

/-- The security part of the one-bit construction has a short cryptographic statement. -/
theorem oneBitExpansion_indistinguishable (f : Word → Word) (predicate : Word → Bool)
    (hf : OneWayPermutation f) (hpredicate : HardCore f predicate) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (fun n => uniformBits (n + 1)) :=
  hf.hardCore_indistinguishable hpredicate

/-- The full one-bit theorem includes deterministic efficiency and strict expansion. -/
theorem oneBitExpansion (f : Word → Word) (predicate : Word → Bool)
    (hf : OneWayPermutation f) (hpredicate : HardCore f predicate) :
    PseudorandomGenerator (fun seed => f seed ++ [predicate seed]) (fun n => n + 1) :=
  hf.pseudorandomGenerator_of_hardCore hpredicate

open GoldreichLevin in
/-- A correlated deterministic predictor gives a short candidate list containing the unknown
string with probability at least one half. This is the finite decoding step; a uniform PPT
implementation is a separate obligation. -/
theorem recoverCorrelatedParity {n k : ℕ} (predictor : BitString n → Bool)
    (x : BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hagreement : 1 / 2 + ε ≤ agreement predictor x)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) :
    (∀ list ∈ (decode predictor k).support, list.card ≤ 2 ^ k) ∧
      (decode predictor k).toOuterMeasure {list | x ∉ list} ≤ 1 / 2 :=
  ⟨fun _ hlist => card_le_of_mem_support_decode predictor hlist,
    decode_failure_le_half predictor x ε hε hk hagreement hsize⟩

open GoldreichLevin in
/-- A predictor with absolute bias yields an inverter with explicit success probability.
The seed is private and sampled once per invocation. This finite theorem does not assert PPT. -/
theorem invertFromPrediction {n k : ℕ} {Coins : Type*} [Finite Coins]
    (f : BitString n → BitString n)
    (predictor : BitString n → Coins → BitString n → Bool)
    (coins : PMF Coins) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hbias : ε ≤ |(predictionExperiment f predictor coins true).toReal - 1 / 2|)
    (hsize : (n : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ k - 1 : ℕ)) :
    ε / 8 ≤ (inversionExperiment f (invertSigned f predictor coins k) true).toReal :=
  invertSigned_success_ge f predictor coins ε hε hk hbias hsize

open GoldreichLevin in
/-- A PPT predictor gives one seeded reduction with a bound valid at every input length.
The evaluator is efficient; certifying the whole inverter as PPT is the remaining obligation. -/
theorem parityPredictionReduction (f : Word → Word)
    (hlen : ∀ word, (f word).length = word.length) (adversary : Distinguisher)
    (hPPT : IsPPT boolEncoding adversary) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ degree n, |winProbability (parityPredictionGame f adversary n) - 1 / 2| ≤
        1 / (precision degree n : ℝ) +
          8 * winProbability (inversionGame f (wordInverter f evaluate c d degree) n) :=
  exists_word_reduction f hlen adversary hPPT

/-- A reduction that runs an adversary and complements its answer. -/
def complement (adversary : Distinguisher) : Distinguisher :=
  fun n input => Bool.not <$> adversary n input

theorem complement_isPPT (adversary : Distinguisher) (hPPT : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (complement adversary) := hPPT.map_bool Bool.not

/-- The reduction has exactly the original distinguishing advantage. -/
theorem complement_advantage (X Y : ℕ → PMF Word) (adversary : Distinguisher) (n : ℕ) :
    advantage (distinguishingGame (X n) (complement adversary n))
      (distinguishingGame (Y n) (complement adversary n)) =
    advantage (distinguishingGame (X n) (adversary n))
      (distinguishingGame (Y n) (adversary n)) := by
  unfold complement
  rw [distinguishingGame_map, distinguishingGame_map, advantage_not]

/-- Quadratically many hops remain secure when every hop obeys the same negligible bound.
The bound may depend on the adversary; it must be uniform over the hop index. -/
theorem quadratic_hybrid (games : ℕ → ℕ → ProbComp Bool) (ε : ℕ → ℝ)
    (hε : Negligible ε) (hε₀ : ∀ n, 0 ≤ ε n)
    (hstep : ∀ n i, i < n ^ 2 → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (n ^ 2))) :=
  negligible_hybrid (PolynomiallyBounded.id.pow 2) hε hε₀ hstep

/-- PRG challenge lengths meet the convention needed for time polynomial in the parameter. -/
example (generator : Word → Word) (size : ℕ → ℕ)
    (h : PseudorandomGenerator generator size) :
    PolynomiallyBoundedEnsemble (generatorEnsemble generator) ∧
      PolynomiallyBoundedEnsemble (fun n => uniformBits (size n)) :=
  ⟨h.bounded_real, h.bounded_ideal⟩
end

end CslibTests.ComputationalCryptoDemo
