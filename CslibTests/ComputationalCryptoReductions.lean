/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Stretch
public import Cslib.Crypto.Computational.GoldreichLevin.HardCore
public import Cslib.Crypto.Computational.OneWay.Normalize

/-!
# Client proofs of cryptographic reductions

These examples exercise two-step and polynomial stretch, truncation, and randomized
postprocessing through the public interfaces. No machine configurations occur in the proofs.
-/

public section

namespace CslibTests.ComputationalCryptoReductions

open Cslib Cslib.Probability Cslib.Crypto

/-- A bound below the image length never truncates the self-delimiting image. -/
example : padWord 0 [true, false] = [true, true, true, false, false] := by
  decide +kernel

/-- Even a zero padding budget preserves one-wayness, since the original image is retained.
The budget controls the fixed-length guarantee, not the security reduction. -/
theorem zeroBudgetPreservesOneWay {f : Word → Word} (hf : OneWay f) :
    OneWay (OneWayNormalization.normalize f (fun _ => 0)) :=
  hf.normalize (fun _ => 0) (by polytime)

/-- Two iterations retain the original seed width and accumulate two output bits. -/
example : PRGStretch.stretch (fun word => word.map not ++ [word.headD false]) (fun _ => 2)
    [true, false] = [true, false, false, true] := by
  decide +kernel

/-- The zero-iteration endpoint is the unchanged seed. -/
example (generator : Word → Word) (seed : Word) :
    PRGStretch.stretch generator (fun _ => 0) seed = seed := rfl

/-- Empty seeds and positive iteration counts are handled by the same definition. -/
example : PRGStretch.stretch (fun word => word ++ [false]) (fun _ => 2) [] = [false, false] := by
  decide +kernel

/-- Captured input and a variable-width expansion need no global length promise for efficiency. -/
example : IsPolyTime (pairEncoding wordEncoding unaryEncoding) (fun input =>
    PRGStretch.iterate (fun seed => input.1 ++ seed) input.1.length input.2 []) := by
  polytime

/-- The length proof only requires one-bit expansion at the seed width actually used. -/
example (seedBits count : ℕ) (seed : Word) (hseed : seed.length = seedBits) :
    (PRGStretch.iterate (fun word => word.take seedBits ++ [false]) seedBits count seed).length =
      seedBits + count := by
  rw [PRGStretch.length_iterate_of_le (by intro word hw; simp [hw]) _ _ hseed.ge, hseed]

/-- One-bit expansion can be applied twice by an ordinary certified program. -/
example {generator : Word → Word} (h : PseudorandomGenerator generator (fun n => n + 1)) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun _ => 2)) (fun n => n + 2) :=
  PRGStretch.pseudorandomGenerator h (by polytime) (by intro n; decide)

/-- An arbitrary fixed polynomial degree is supported uniformly across all seed lengths. -/
example {generator : Word → Word} (h : PseudorandomGenerator generator (fun n => n + 1))
    (degree : ℕ) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun n => (n + 1) ^ degree))
      (fun n => n + (n + 1) ^ degree) :=
  PRGStretch.pseudorandomGenerator h (by polytime) (by intro n; positivity)

/-- Clients can request the final length directly, including the small-parameter boundary. -/
example {generator : Word → Word} (h : PseudorandomGenerator generator (fun n => n + 1)) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun n => (3 * n + 1) - n))
      (fun n => 3 * n + 1) :=
  h.amplify (fun n => 3 * n + 1) (by polytime) (by intro n; lia)

/-- The complete OWP-to-PRG theorem now supports polynomially many additional bits. -/
theorem polynomialExpansion {f : Word → Word} (hf : OneWayPermutation f) (degree : ℕ) :
    PseudorandomGenerator (PRGStretch.stretch (GoldreichLevin.generator f)
      (fun n => (n + 1) ^ degree)) (fun n => n + (n + 1) ^ degree) :=
  PRGStretch.pseudorandomGenerator hf.pseudorandomGenerator
    (by polytime) (by intro n; positivity)

/-- A second reduction truncates an existing generator while preserving positive stretch. -/
example {generator : Word → Word} (h : PseudorandomGenerator generator (fun n => 3 * n + 1)) :
    PseudorandomGenerator (fun seed => (generator seed).take (2 * seed.length + 1))
      (fun n => 2 * n + 1) :=
  h.truncate (fun n => 2 * n + 1) (by polytime) (by intro n; lia) (by intro n; lia)

/-- A deterministic reduction may retain the parameter when transforming its challenge. -/
example {X Y : ℕ → PMF Word} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable
      (fun n => (X n).map (fun word => word.reverse.take n))
      (fun n => (Y n).map (fun word => word.reverse.take n)) :=
  h.map (fun n word => word.reverse.take n) (by polytime)

/-- A reduction can mix its challenge with fresh local randomness. -/
noncomputable def appendCoins (n : ℕ) (word : Word) : ProbComp Word := do
  let coins ← OracleComp.sampleBits n
  return word ++ coins

/-- Neither input ensemble needs an efficient sampler for this closure theorem. -/
example {X Y : ℕ → PMF Word} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun word => ProbComp.eval (appendCoins n word)))
      (fun n => (Y n).bind (fun word => ProbComp.eval (appendCoins n word))) :=
  h.bind appendCoins (by unfold appendCoins; ppt)

/-- Saturation prevents an arbitrarily long binary input from producing an exponential unary
result. Valid short inputs still decode to their ordinary binary value. -/
example : boundedBinaryValue 5 (List.replicate 100 true) = 5 ∧
    boundedBinaryValue 5 [true, false] = 2 := by
  decide +kernel

/-- A non-dyadic bound uses a rejection outcome, with exactly equal masses on valid indices. -/
example : ProbComp.eval (sampleBoundedIndex 3) =
    (PMF.uniformOfFintype (Fin 4)).map Fin.val := by
  rw [eval_sampleBoundedIndex]
  rw [show Nat.log 2 3 = 1 by decide]
  congr 1
  funext i
  exact Nat.min_eq_right (by lia)

/-- At a power of two the padded sampler rejects half its draws; it never resamples. -/
example : ((ProbComp.eval (sampleBoundedIndex 2)) 2).toReal = 1 / 2 := by
  rw [eval_sampleBoundedIndex]
  rw [show Nat.log 2 2 = 1 by decide]
  change ((PMF.map (fun i : Fin 4 => min 2 i.val) (PMF.uniformOfFintype (Fin 4))) 2).toReal = 1 / 2
  norm_num [PMF.map_apply, tsum_fintype, Fin.sum_univ_four, PMF.uniformOfFintype_apply,
    ENNReal.toReal_add]

end CslibTests.ComputationalCryptoReductions
