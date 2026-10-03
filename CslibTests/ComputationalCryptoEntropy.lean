/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.HashIsolation
public import Cslib.Probability.LinearHash
public import Cslib.Crypto.Computational.GoldreichLevin.WordDecoder
public import Cslib.Crypto.Computational.Pseudoentropy.HashReduction
public import Cslib.Crypto.Computational.Pseudoentropy.Seed
public import Cslib.Crypto.Computational.Pseudoentropy.Selection
public import Cslib.Tactic.PPT

/-!
# Entropy, preimage isolation, and uniform prediction examples

These checks exercise the units and orientation of conditional entropy, null observations, and
the distinction between an arbitrary image length and the dimension of recovered preimages.
Indexed prediction checks the common eventual bound without an efficiently chosen index.
-/

public section

namespace CslibTests.ComputationalCryptoEntropy

open Cslib Cslib.Probability Cslib.Probability.PMF

/-- Entropy is measured in bits, including the unique empty bitstring. -/
theorem uniform_bitString_entropy (n : ℕ) :
    entropy (PMF.uniformOfFintype (BitString n)) = n := by
  simp [entropy_uniform, BitString, Real.logb_pow]

/-- The lower-tail event is empty for independent fair bits, even with zero repetitions.
This checks the sign of the entropy deficit and the probability units. -/
theorem fair_bits_have_no_lower_tail (repetitions : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((PMF.pi (fun _ : Fin repetitions => PMF.uniformOfFintype Bool)).toOuterMeasure
      {outcome | surprisal (PMF.pi (fun _ : Fin repetitions => PMF.uniformOfFintype Bool))
        outcome ≤ repetitions - ε}).toReal = 0 := by
  have hinfo (outcome : Fin repetitions → Bool) :
      surprisal (PMF.pi (fun _ : Fin repetitions => PMF.uniformOfFintype Bool)) outcome =
        repetitions := by
    simp [PMF.pi_uniformOfFintype, surprisal, PMF.uniformOfFintype_apply,
      Real.logb_inv, Real.logb_pow]
  have hempty : {outcome | surprisal
      (PMF.pi (fun _ : Fin repetitions => PMF.uniformOfFintype Bool)) outcome ≤
        repetitions - ε} = ∅ := by
    ext outcome
    simp only [Set.mem_ofPred_eq, hinfo, Set.mem_empty_iff_false, iff_false]
    linarith
  rw [hempty]
  simp

/-- A fair bit remains uncertain on exactly half of the revealed branches. -/
example : conditionalEntropy ((PMF.uniformOfFintype Bool).bind (fun revealed =>
    (if revealed then PMF.pure true else PMF.uniformOfFintype Bool).map (revealed, ·))) =
      1 / 2 := by
  rw [conditionalEntropy_bind_pair]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]

/-- Null observations do not contribute entropy, regardless of the conditional fallback. -/
example : conditionalEntropy ((PMF.pure true).bind (fun revealed =>
    (PMF.uniformOfFintype Bool).map (revealed, ·))) = 1 := by
  rw [conditionalEntropy_bind_pair]
  norm_num [Fintype.sum_bool, PMF.pure_apply]

/-- If the revealed function is injective, hashing leaves no uncertainty about any input bit.
The statement allows the bit itself to depend on the public matrix. -/
theorem injective_image_has_zero_conditional_entropy (n m : ℕ)
    (predicate : (Fin m → BitString n) → BitString n → Bool) :
    conditionalEntropy ((PMF.uniformOfFintype (Fin m → BitString n)).bind (fun rows =>
      (PMF.uniformOfFintype (BitString n)).map
        (fun x => ((rows, x, LinearHash.hash rows x), predicate rows x)))) = 0 := by
  apply le_antisymm _ (conditionalEntropy_nonneg _)
  have h := (LinearHash.isTwoUniversal n m).conditionalEntropy_hash_le
    (PMF.uniformOfFintype (BitString n)) id predicate
  simpa using h

/-- Failure to find a preimage returns the original input width, independent of image length. -/
theorem decoder_failure_keeps_input_width :
    Crypto.GoldreichLevin.wordCheckCandidates (fun word => word ++ [true])
    2 [true] [] = [false, false] := rfl

/-- A fixed power-of-two range is sampled exactly, including at parameter zero. -/
example : ProbComp.eval (sampleDyadicIndex 0) =
    (PMF.uniformOfFintype (Fin 2)).map Fin.val := eval_sampleDyadicIndex 0

/-- Powers of two are rounded to the next larger range, with no rejection sentinel. -/
example : dyadicSize 8 = 16 := by decide

/-- The complete word sampler has its finite mathematical distribution, also at zero width. -/
theorem empty_hash_pair_distribution :
    ProbComp.eval (Crypto.Pseudoentropy.HashPair.sample id 0) =
      (Crypto.Pseudoentropy.HashPair.joint (count := Crypto.Pseudoentropy.HashPair.hashCount 0)
        (id : BitString 0 → BitString 0)).map
          (fun pair =>
            (Crypto.Pseudoentropy.HashPair.encodeObservation List.ofFn pair.1, pair.2)) :=
  Crypto.Pseudoentropy.HashPair.eval_sample id id List.ofFn (fun _ => rfl)

/-- The hash range has room for the inversion cutoff even for zero-bit inputs. -/
example : Crypto.Pseudoentropy.HashPair.hashCount 0 = 8 := by decide

/-- The matrix reduction also handles the largest fiber, where every candidate is a preimage. -/
theorem constant_function_inversion (n count : ℕ) [NeZero count] (precision : ℕ)
    (predictor : Crypto.Pseudoentropy.MatrixPredictor n count Unit) :
    Crypto.GoldreichLevin.inversionExperiment (fun _ : BitString n => ())
      (Crypto.Pseudoentropy.matrixInverter (fun _ => ()) predictor precision) = PMF.pure true := by
  simp [Crypto.GoldreichLevin.inversionExperiment, PMF.map, Function.comp_def, PMF.bind_const]

/-- A perfectly hidden independent bit is samplable but has no entropy surplus. -/
noncomputable def independentBitPair : Crypto.Pseudoentropy.SamplablePair where
  Observation _ := Unit
  encode _ := ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := (PMF.pure ()).bind (fun revealed =>
    (PMF.uniformOfFintype Bool).map (revealed, ·))
  sample _ := do
    let bit ← OracleComp.uniform Bool
    return ([], bit)
  efficient := by ppt
  eval_sample _ := by
    simp [OracleComp.uniform, PMF.map_comp, Function.comp_def]
    rfl

/-- With no public information, the independent hidden bit has one bit of entropy. -/
theorem independentBitPair_conditionalEntropy (n : ℕ) :
    conditionalEntropy (independentBitPair.joint n) = 1 := by
  change conditionalEntropy ((PMF.pure ()).bind (fun revealed =>
    (PMF.uniformOfFintype Bool).map (revealed, ·))) = 1
  rw [conditionalEntropy_bind_pair]
  norm_num [PMF.pure_apply]

/-- A two-bit seed implements the same pair while deliberately ignoring its second bit. -/
@[expose] noncomputable def paddedIndependentBitSeed : independentBitPair.SeedRealization where
  length _ := 2
  length_isPolyTime := by polytime
  evaluate _ coins := ([], coins.headD false)
  efficient := by polytime
  distribution n := by
    rw [uniformBits_succ]
    simp [independentBitPair, PMF.map, Function.comp_def, PMF.bind_const]
    rfl

/-- The ignored seed bit is retained as residual entropy, rather than disappearing from the
expansion accounting. -/
theorem unused_seed_bit_retains_entropy (n : ℕ) :
    conditionalEntropy ((PMF.uniformOfFintype (BitString 2)).map
      (fun bits => (paddedIndependentBitSeed.output n bits, bits))) = 1 := by
  have h := paddedIndependentBitSeed.entropy_chain_rule n
  have hpublic : entropy ((independentBitPair.joint n).map Prod.fst) = 0 := by
    simpa only [independentBitPair, map_fst_bind_pair] using entropy_pure ()
  rw [hpublic, independentBitPair_conditionalEntropy] at h
  change 0 + 1 + conditionalEntropy ((PMF.uniformOfFintype (BitString 2)).map
    (fun bits => (paddedIndependentBitSeed.output n bits, bits))) = (2 : ℝ) at h
  linarith

/-- Unpredictability alone does not give a pseudoentropy pair: the hidden bit's true entropy
must also leave room for the promised gap. -/
theorem independent_bit_has_no_entropy_gap :
    ¬independentBitPair.HasGap (fun _ => 1 / 4) := by
  have hwin (n : ℕ) : Crypto.winProbability
      (Crypto.Pseudoentropy.predictionGame independentBitPair.sample (fun _ _ => pure false) n) =
        1 / 2 := by
    simp [Crypto.Pseudoentropy.predictionGame, independentBitPair, Crypto.winProbability,
      Crypto.Game.winProbability, OracleComp.uniform, PMF.map, Function.comp_def, PMF.bind_apply,
      PMF.uniformOfFintype_apply]
  intro h
  obtain ⟨n, hn⟩ := (h (fun _ _ => pure false) (by ppt)).exists
  rw [hwin, independentBitPair_conditionalEntropy] at hn
  norm_num at hn

/-- Predictor selection composes runtime bounds, fresh samples, and a supplied indexed program.
The indexed program still needs its own certificate. -/
theorem selected_predictor_isPPT (sample : ℕ → ProbComp (Word × Bool))
    (predict : ℕ → ℕ → Word → ProbComp Bool)
    (hsample : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) sample)
    (hpredict : IsPPTOn
      (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding) boolEncoding
      (fun input => predict input.1.1 input.1.2 input.2)) :
    IsPPT boolEncoding (fun n observation => Crypto.Pseudoentropy.selectPredictor
      ((n + 1) ^ 2) ((n + 1) ^ 3) (sample n) (predict n) observation.tail) := by
  fail_if_success (clear hpredict; ppt)
  ppt

open Filter in
/-- The common threshold covers a varying index even when no efficient way to choose it is
given. The algorithm tests all candidates; only the mathematical bound uses `choose`. -/
theorem varying_index_prediction_error (pair : Crypto.Pseudoentropy.SamplablePair) {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (predict : ℕ → ℕ → Word → ProbComp Bool)
    (hpredict : IsPPTOn
      (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding) boolEncoding
      (fun input => predict input.1.1 input.1.2 input.2))
    (choose : ∀ n, Fin ((n + 1) ^ 2)) :
    ∀ᶠ n in atTop, (conditionalEntropy (pair.joint n) + gap n) / 2 ≤
      (ProbComp.eval (Crypto.Pseudoentropy.predictionGame pair.sample
        (fun n => predict n (choose n)) n) false).toReal + 1 / ((n + 1) ^ 3 : ℕ) := by
  have h := hgap.eventually_indexed_error_ge predict hpredict
    (count := fun n => (n + 1) ^ 2) (inverseTolerance := fun n => (n + 1) ^ 3)
    (by polytime) (by polytime) (fun _ => by positivity)
  filter_upwards [h] with n hn
  exact hn (choose n) (choose n).isLt

/-- Bare projections produced by simplification still synthesize their certificates. -/
example {α : Type} (encode : α ↪ Word) :
    IsPolyTime (pairEncoding encode wordEncoding) Prod.snd := by polytime

/-- Bitwise callbacks with several captured values avoid unfolding nested input encodings. -/
example : IsPolyTime
    (pairEncoding (pairEncoding (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      wordEncoding) wordEncoding) wordEncoding)
    (fun a => [(a.2.zipWith Bool.and a.1.2).foldl Bool.xor false]) := by polytime

end CslibTests.ComputationalCryptoEntropy
