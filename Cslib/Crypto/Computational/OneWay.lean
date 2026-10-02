/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Probability.BitString

/-!
# One-way functions and permutations

A deterministic polynomial-time function on binary words is one-way when, given its value on a
uniform `n`-bit input and the unary parameter `n`, every uniform PPT inverter has negligible
probability of finding **any** preimage. Recovering the original sampled input is not required.

`OneWayPermutation` additionally requires a length-preserving bijection. Its inverse exists as a
mathematical function; no efficiency of that inverse is assumed. Such a permutation preserves
the uniform distribution at every input length.

These are definitions, not assertions that one-way functions or permutations exist.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- A candidate inverter receives the parameter and the image of the sampled input. -/
abbrev Inverter := ℕ → Word → ProbComp Word

/-- The inversion experiment accepts any preimage of the challenge. -/
noncomputable def inversionGame (f : Word → Word) (adversary : Inverter) (n : ℕ) :
    ProbComp Bool := do
  let input ← OracleComp.sample (uniformBits n)
  let candidate ← adversary n (f input)
  return f candidate == f input

/-- A polynomial-time computable function that every uniform PPT inverter fails to invert,
except with negligible probability over the uniform input and the inverter's random coins. -/
structure OneWay (f : Word → Word) : Prop where
  /-- A single deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : IsPolyTime id f
  /-- Inversion is indistinguishable from certain failure in the common game calculus. -/
  secure : Game.Secure (fun adversary n => ProbComp.eval (inversionGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT wordEncoding)

/-- The common security definition gives the usual negligible inversion probability. -/
theorem OneWay.inversion_negligible {f : Word → Word} (h : OneWay f)
    (adversary : Inverter) (hPPT : IsPPT wordEncoding adversary) :
    Negligible (fun n => winProbability (inversionGame f adversary n)) := by
  simpa only [Game.advantage_pure_false, winProbability] using h.secure adversary hPPT

/-- Establish one-wayness by bounding every efficient inverter's success probability. -/
theorem OneWay.of_inversion_negligible {f : Word → Word} (hf : IsPolyTime id f)
    (h : ∀ adversary : Inverter, IsPPT wordEncoding adversary →
      Negligible (fun n => winProbability (inversionGame f adversary n))) : OneWay f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false, winProbability] using h adversary hPPT

/-- A length-preserving permutation that is one-way against every uniform PPT inverter. -/
structure OneWayPermutation (f : Word → Word) : Prop where
  /-- Evaluation is polynomial time, and inversion succeeds only with negligible probability. -/
  oneWay : OneWay f
  /-- The permutation acts separately on words of each length. -/
  length_eq : ∀ word, (f word).length = word.length
  /-- Every word has exactly one preimage; computing that preimage need not be efficient. -/
  bijective : Function.Bijective f

/-- Applying a one-way permutation does not change the uniform input distribution. -/
theorem OneWayPermutation.uniformBits_map {f : Word → Word} (hf : OneWayPermutation f) (n : ℕ) :
    (uniformBits n).map f = uniformBits n :=
  uniformBits_map_of_bijective f hf.bijective hf.length_eq n

/-- The ideal output in the one-bit construction: a permuted uniform seed and an independent
fair bit are exactly uniform at the expanded length. Security is needed only when replacing that
independent bit with a hard-core predicate. -/
theorem OneWayPermutation.uniformBits_append_bit {f : Word → Word}
    (hf : OneWayPermutation f) (n : ℕ) :
    (uniformBits n).bind (fun word =>
      (PMF.uniformOfFintype Bool).map (fun bit => f word ++ [bit])) = uniformBits (n + 1) := by
  change (uniformBits n).bind
    ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
  rw [← PMF.bind_map, hf.uniformBits_map]
  exact (uniformBits_snoc n).symm

/-- For an injective function, accepting any preimage is the same as recovering the sampled
input. The general one-way-function game does not make this assumption. -/
theorem inversionGame_eq_of_injective (f : Word → Word) (hf : Function.Injective f)
    (adversary : Inverter) (n : ℕ) :
    inversionGame f adversary n = (do
      let input ← OracleComp.sample (uniformBits n)
      let candidate ← adversary n (f input)
      return candidate == input) := by
  have heq (candidate input : Word) : (f candidate == f input) = (candidate == input) := by
    by_cases h : candidate = input
    · simp [h]
    · have hne : f candidate ≠ f input := fun h' => h (hf h')
      simp [h, hne]
  simp only [inversionGame, heq]

/-- If an inverter always returns a preimage, its inversion game always accepts. This also checks
that success means finding a preimage, rather than necessarily recovering the sampled input. -/
theorem eval_inversionGame_of_rightInverse (f inverse : Word → Word)
    (h : ∀ x, f (inverse (f x)) = f x) (n : ℕ) :
    ProbComp.eval (inversionGame f (fun _ y => pure (inverse y)) n) = PMF.pure true := by
  simp [inversionGame, h, PMF.map, Function.comp_def]

/-- An efficiently computable inverse contradicts one-wayness. Only a preimage is required. -/
theorem not_oneWay_of_inverse (f inverse : Word → Word)
    (hPPT : IsPPT wordEncoding (fun _ y => pure (inverse y)))
    (hinv : ∀ x, f (inverse (f x)) = f x) : ¬ OneWay f := by
  intro h
  have hnegl := h.inversion_negligible _ hPPT
  apply not_negligible_const (c := 1) one_ne_zero
  simpa only [winProbability, Game.winProbability,
    eval_inversionGame_of_rightInverse f inverse hinv, PMF.pure_apply_self,
    ENNReal.toReal_one] using hnegl

/-- Constant functions are not one-way: the empty word is always a preimage. -/
theorem not_oneWay_const (word : Word) : ¬ OneWay (fun _ => word) :=
  not_oneWay_of_inverse _ (fun _ => []) isPPT_empty (fun _ => rfl)

end Cslib.Crypto
