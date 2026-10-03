/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Probability.LinearHash
public import Cslib.Tactic.PPT

/-!
# Polynomial-time binary linear hashing

The hash seed is a flat, row-major Boolean matrix. Hashing consists of reading its rows and
folding the coordinatewise AND with the input using XOR. The polynomial-time certificate is
uniform in the input length and requested output length, and also covers short seed tapes.

The representation and sampling laws are shared with Goldreich–Levin. The family and its
source references are in `Cslib.Probability.LinearHash`.
-/

@[expose] public section

namespace Cslib.Probability.LinearHash

open Cslib.Probability.PMF

/-- A word implementation of binary matrix hashing. Missing seed bits are zero. -/
def wordHash (count : ℕ) (seed input : Word) : Word :=
  (maskRows count input.length seed).map
    (fun row => (row.zipWith Bool.and input).foldl Bool.xor false)

/-- Every row contributes one output bit, including when the input has length zero. -/
@[simp] theorem length_wordHash (count : ℕ) (seed input : Word) :
    (wordHash count seed input).length = count := by
  simp [wordHash, maskRows]

/-- Hashing efficiently available words has a uniform polynomial-time certificate. -/
theorem wordHash_isPolyTime {α : Type} {encode : α ↪ Word}
    {count : α → ℕ} {seed input : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime encode seed) (hinput : IsPolyTime encode input) :
    IsPolyTime encode (fun a => wordHash (count a) (seed a) (input a)) := by
  unfold wordHash
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] wordHash_isPolyTime

/-- On a fixed-length source word, the executable hash is exactly the finite matrix hash. -/
theorem wordHash_eq_ofFn {n m : ℕ} (seed : Word) (input : BitString n) :
    wordHash m seed (List.ofFn input) =
      List.ofFn (hash (masksFromWord m n seed) input) := by
  unfold wordHash hash
  simp only [List.length_ofFn, maskRows_eq_ofFn, List.map_ofFn, Function.comp_def,
    ← dotProduct_eq_foldl]

/-- Sample an independent hash matrix and return its seed followed by the extracted bits. -/
noncomputable def extract (count : ℕ) (input : Word) : ProbComp Word := do
  let seed ← OracleComp.sampleBits (count * input.length)
  return seed ++ wordHash count seed input

/-- The complete seeded extractor is PPT, including all sampling and the revealed seed. -/
theorem extract_isPPTOn {α : Type} {encode : α ↪ Word} {count : α → ℕ} {input : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hinput : IsPolyTime encode input) :
    IsPPTOn encode wordEncoding (fun a => extract (count a) (input a)) := by
  unfold extract
  ppt

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PPT])] extract_isPPTOn

/-- The word extractor agrees exactly with the finite strong-extraction experiment. -/
theorem eval_extract_bind {n m : ℕ} (source : PMF (BitString n)) :
    (source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input)) =
      (seededHash (PMF.uniformOfFintype (BitString (m * n))) source
        (fun seed => hash (maskEquiv m n seed))).map
          (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) := by
  simp only [PMF.bind_map, Function.comp_def, extract, ProbComp.eval, OracleComp.eval_bind,
    OracleComp.eval_pure, OracleComp.eval_sampleBits, List.length_ofFn]
  simp only [uniformBits, seededHash, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  simp only [PMF.map, Function.comp_def,
    wordHash_eq_ofFn, masksFromWord, wordBits_ofFn]

/-- The executable extractor satisfies the strong leftover hash bound on a finite word source. -/
theorem extract_distance_le {n m : ℕ} (source : PMF (BitString n)) :
    dist ((source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input)))
        (uniformBits (m * n + m)) ≤
      Real.sqrt ((2 : ℝ) ^ m * collisionProbability source) / 2 := by
  have huniversal : IsTwoUniversal (PMF.uniformOfFintype (BitString (m * n)))
      (fun seed => hash (maskEquiv m n seed)) := by
    apply IsTwoUniversal.precompose_seed
    rw [uniformOfFintype_map_equiv]
    exact isTwoUniversal n m
  have h := huniversal.leftover_hash source
  have hideal : ((PMF.uniformOfFintype (BitString (m * n))).bind
      (fun seed => (PMF.uniformOfFintype (BitString m)).map (seed, ·))).map
      (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) = uniformBits (m * n + m) := by
    rw [uniformBits_add]
    simp only [uniformBits, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  rw [eval_extract_bind, ← hideal]
  exact (dist_map_le _ _ _).trans (by simpa [BitString] using h)

end Cslib.Probability.LinearHash
