/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GoldreichLevin.WordReduction
public import Cslib.Crypto.Computational.HardCore

/-!
# The Goldreich–Levin hard-core predicate

Split a seed into two equal halves and an optional spare bit. Apply the one-way function to
the first half and retain the rest. The inner product of the two halves is a hard-core predicate.
Keeping the spare bit extends the construction to every seed length.

`OneWayPermutation.pseudorandomGenerator` completes the one-bit PRG construction, including
deterministic polynomial time and security against uniform PPT adversaries.

## References

* Oded Goldreich and Leonid Levin, *A Hard-Core Predicate for All One-Way Functions*, STOC 1989.
  [Paper](https://www.wisdom.weizmann.ac.il/~oded/X/gl.pdf).
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability

/-- Apply a function to the first half of a word and retain the remaining bits. -/
def paddedFunction (f : Word → Word) (seed : Word) : Word :=
  let half := seed.length / 2
  f (seed.take half) ++ seed.drop half

/-- The inner product of the first two equal halves, ignoring an optional final bit. -/
def paddedPredicate (seed : Word) : Bool :=
  let half := seed.length / 2
  ((seed.take half).zipWith Bool.and ((seed.drop half).take half)).foldl Bool.xor false

/-- The padded function uses ordinary slicing and one call to the supplied function. -/
theorem paddedFunction_isPolyTime {f : Word → Word} (hf : IsPolyTime wordEncoding f) :
    IsPolyTime wordEncoding (paddedFunction f) := by
  unfold paddedFunction
  polytime

/-- The hard-core predicate is an efficient dot product of the two halves. -/
theorem paddedPredicate_isPolyTime :
    IsPolyTime wordEncoding (fun seed => [paddedPredicate seed]) := by
  unfold paddedPredicate
  polytime

/-- On two equal chunks and at most one spare bit, only the first chunk is transformed. -/
theorem paddedFunction_chunks (f : Word → Word) {n : ℕ} (x r : BitString n)
    (extra : Word) (hextra : extra.length ≤ 1) :
    paddedFunction f (List.ofFn x ++ List.ofFn r ++ extra) =
      f (List.ofFn x) ++ List.ofFn r ++ extra := by
  have hhalf : (n + (n + extra.length)) / 2 = n := by lia
  simp [paddedFunction, hhalf, List.append_assoc]

/-- The spare bit is retained by the function but does not enter the parity. -/
theorem paddedPredicate_chunks {n : ℕ} (x r : BitString n)
    (extra : Word) (hextra : extra.length ≤ 1) :
    paddedPredicate (List.ofFn x ++ List.ofFn r ++ extra) = x ⬝ᵥ r := by
  have hhalf : (n + (n + extra.length)) / 2 = n := by lia
  simp [paddedPredicate, hhalf, List.append_assoc, dotProduct_eq_foldl]

/-- A length-preserving function leaves the complete padded seed length unchanged. -/
theorem paddedFunction_length {f : Word → Word}
    (hlen : ∀ word, (f word).length = word.length) (seed : Word) :
    (paddedFunction f seed).length = seed.length := by
  simp [paddedFunction, hlen]
  lia

/-- Permuting the first half preserves uniform seeds of every length. -/
theorem paddedFunction_uniform {f : Word → Word} (hf : OneWayPermutation f) (n : ℕ) :
    (uniformBits n).map (paddedFunction f) = uniformBits n := by
  have hsplit : uniformBits n = (uniformBits (n / 2)).bind
      (fun left => (uniformBits (n - n / 2)).map (left ++ ·)) := by
    convert uniformBits_add (n / 2) (n - n / 2) using 1
    congr 1
    lia
  rw [hsplit, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  trans ((uniformBits (n / 2)).map f).bind
    (fun left => (uniformBits (n - n / 2)).map (left ++ ·))
  · rw [PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro left hleft
    simp only [PMF.map, Function.comp_def]
    apply PMF.bind_congr_on_support
    intro right hright
    congr 1
    have hleft := length_of_mem_support_uniformBits hleft
    have hright := length_of_mem_support_uniformBits hright
    have hlen : (left ++ right).length = n := by simp [hleft, hright]; lia
    simp [paddedFunction, hlen, ← hleft]
  · rw [hf.uniformBits_map]

/-- Translate a predictor for a padded seed to a parity predictor, sampling its spare bits. -/
noncomputable def paddedPredictor (adversary : Distinguisher) (spare : ℕ) : Distinguisher :=
  fun n input => do
    let extra ← OracleComp.sample (uniformBits spare)
    adversary (2 * n + spare) (input ++ extra)

/-- Parameter rescaling, sampling, and captured adversary calls have a uniform PPT certificate. -/
theorem paddedPredictor_isPPT {adversary : Distinguisher}
    (hPPT : IsPPT boolEncoding adversary) (spare : ℕ) :
    IsPPT boolEncoding (paddedPredictor adversary spare) := by
  unfold paddedPredictor
  ppt

/-- The padded prediction experiment is the parity experiment, for either possible spare length. -/
theorem eval_paddedPrediction (f : Word → Word) (adversary : Distinguisher)
    (n spare : ℕ) (hspare : spare ≤ 1) :
    ProbComp.eval (predictionGame (paddedFunction f) paddedPredicate adversary (2 * n + spare)) =
      ProbComp.eval (parityPredictionGame f (paddedPredictor adversary spare) n) := by
  simp only [predictionGame, parityPredictionGame, paddedPredictor, ProbComp.eval_bind,
    ProbComp.eval_sample, ProbComp.eval_pure, two_mul]
  rw [uniformBits_add (n + n) spare, uniformBits_add n n]
  simp only [uniformBits, PMF.bind_bind, PMF.bind_map, Function.comp_def, wordBits_ofFn]
  congr 1
  funext x
  congr 1
  funext r
  congr 1
  funext extra
  rw [paddedFunction_chunks f x r (List.ofFn extra) (by simpa using hspare),
    paddedPredicate_chunks x r (List.ofFn extra) (by simpa using hspare)]

/-- Goldreich–Levin supplies an efficient hard-core predicate for the padded function. Two fixed
PPT reductions handle even and odd seed lengths; no length-dependent adversary is chosen. -/
theorem padded_hardCore {f : Word → Word} (hf : OneWay f) :
    HardCore (paddedFunction f) paddedPredicate := by
  apply HardCore.of_unpredictable paddedPredicate_isPolyTime
  intro adversary hPPT
  have heven := negligible_parityPrediction hf _ (paddedPredictor_isPPT hPPT 0)
  have hodd := negligible_parityPrediction hf _ (paddedPredictor_isPPT hPPT 1)
  apply negligible_of_le (Negligible.div_two (heven.add hodd)) (fun _ => abs_nonneg _)
  intro n
  have hgame := eval_paddedPrediction f adversary (n / 2) (n % 2) (by lia)
  have hlen : 2 * (n / 2) + n % 2 = n := by lia
  rw [hlen] at hgame
  simp only [winProbability, hgame, Pi.add_apply]
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [heven]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [hodd]
    exact le_add_of_nonneg_left (abs_nonneg _)

/-- The one-bit generator: permute the first half, retain the rest, and append the parity. -/
def generator (f : Word → Word) (seed : Word) : Word :=
  paddedFunction f seed ++ [paddedPredicate seed]

end Cslib.Crypto.GoldreichLevin

namespace Cslib.Crypto

open GoldreichLevin

/-- One-way permutations imply uniform polynomial-time pseudorandom generators with one-bit
stretch. Goldreich–Levin supplies the hard-core predicate; uniformity supplies the ideal hybrid. -/
theorem OneWayPermutation.pseudorandomGenerator {f : Probability.Word → Probability.Word}
    (hf : OneWayPermutation f) :
    PseudorandomGenerator (generator f) (fun n => n + 1) :=
  (padded_hardCore hf.oneWay).pseudorandomGenerator
    (paddedFunction_isPolyTime hf.oneWay.polyTime) (paddedFunction_length hf.length_eq)
    (paddedFunction_uniform hf)

end Cslib.Crypto
