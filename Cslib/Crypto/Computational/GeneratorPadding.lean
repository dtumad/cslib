/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Game
public import Cslib.Tactic.PPT
public import Cslib.Probability.BitString

/-!
# Padding expanding generators to a common input length

Run an expander on the required seed prefix, retain the unused input bits, and truncate the
result to one bit more than the common input length. Independent uniform padding preserves
the distinguishing advantage exactly through an efficient reduction.

This is used to give the entropy guesses in the OWF-to-PRG construction a common seed length
before amplification and XOR combination. See Thomas Holenstein, *Pseudorandom Generators from
One-Way Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of
Theorem 1, [write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorPadding

open Probability

/-- Retain the unused uniform input bits and keep exactly one bit of stretch. -/
def generate (seedBits commonBits : ℕ) (generator : Word → Word) (seed : Word) : Word :=
  (generator (seed.take seedBits) ++ seed.drop seedBits).take (commonBits + 1)

/-- Padding uses only the supplied generator, word slicing, and concatenation. -/
theorem generate_isPolyTime {α : Type} {input : α ↪ Word}
    {seedBits commonBits : α → ℕ} {generator : α → Word → Word} {seed : α → Word}
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hcommon : IsPolyTime input (fun a => unaryEncoding (commonBits a)))
    (hgenerator : IsPolyTime (pairEncoding input wordEncoding)
      (fun a => generator a.1 a.2))
    (hseed : IsPolyTime input seed) :
    IsPolyTime input (fun a => generate (seedBits a) (commonBits a) (generator a) (seed a)) := by
  unfold generate
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeGenerate : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyHead #[(``generate, ``generate_isPolyTime)]

/-- One bit of raw expansion suffices, also when no padding is needed. -/
theorem length_generate {seedBits commonBits : ℕ} {generator : Word → Word}
    (hfits : seedBits ≤ commonBits)
    (hexpands : ∀ seed, seed.length = seedBits → seedBits < (generator seed).length)
    {seed : Word} (hseed : seed.length = commonBits) :
    (generate seedBits commonBits generator seed).length = commonBits + 1 := by
  have h := hexpands (seed.take seedBits) (by simpa [hseed] using Nat.min_eq_left hfits)
  simp only [generate, List.length_take, List.length_append, List.length_drop, hseed]
  exact Nat.min_eq_left (by lia)

/-- The unused suffix of a uniform padded seed is fresh independent randomness. -/
theorem generate_distribution {seedBits commonBits : ℕ} (generator : Word → Word)
    (hfits : seedBits ≤ commonBits) :
    (uniformBits commonBits).map (generate seedBits commonBits generator) =
      ((uniformBits seedBits).map generator).bind (fun word =>
        (uniformBits (commonBits - seedBits)).map
          (fun padding => (word ++ padding).take (commonBits + 1))) := by
  change (uniformBits commonBits).bind (fun seed => PMF.pure
    ((generator (seed.take seedBits) ++ seed.drop seedBits).take (commonBits + 1))) = _
  nth_rw 1 [show commonBits = seedBits + (commonBits - seedBits) by lia]
  rw [uniformBits_bind_split seedBits (commonBits - seedBits)
    (fun front padding => PMF.pure
      ((generator front ++ padding).take (commonBits + 1)))]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

/-- Uniform raw output and independent padding give exactly the desired uniform output. -/
theorem ideal_distribution {seedBits outputBits commonBits : ℕ}
    (hexpands : seedBits < outputBits) :
    (uniformBits outputBits).bind (fun word =>
      (uniformBits (commonBits - seedBits)).map
        (fun padding => (word ++ padding).take (commonBits + 1))) =
      uniformBits (commonBits + 1) := by
  rw [← uniformBits_take (n := outputBits + (commonBits - seedBits))
    (k := commonBits + 1) (by lia), uniformBits_add, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

/-- A distinguisher for padded output is an ordinary randomized postprocessing of raw output. -/
noncomputable def test (seedBits commonBits : ℕ) (adversary : Word → ProbComp Bool)
    (word : Word) : ProbComp Bool := do
  let padding ← OracleComp.sampleBits (commonBits - seedBits)
  adversary ((word ++ padding).take (commonBits + 1))

/-- The reduction charges the padding and the call to the captured adversary. -/
theorem test_isPPT {α : Type} {input : α ↪ Word}
    {seedBits commonBits : α → ℕ} {adversary : α → Word → ProbComp Bool}
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hcommon : IsPolyTime input (fun a => unaryEncoding (commonBits a)))
    (hadversary : IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun a => adversary a.1 a.2)) :
    IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun a => test (seedBits a.1) (commonBits a.1) (adversary a.1) a.2) := by
  unfold test
  ppt

/-- Padding preserves the tested distinguishing advantage exactly. -/
theorem advantage_eq {seedBits outputBits commonBits : ℕ} (generator : Word → Word)
    (adversary : Word → ProbComp Bool) (hfits : seedBits ≤ commonBits)
    (hexpands : seedBits < outputBits) :
    Game.advantage
      (((uniformBits commonBits).map (generate seedBits commonBits generator)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformBits (commonBits + 1)).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformBits seedBits).map generator).bind
        (fun word => ProbComp.eval (test seedBits commonBits adversary word)))
      ((uniformBits outputBits).bind
        (fun word => ProbComp.eval (test seedBits commonBits adversary word))) := by
  rw [generate_distribution generator hfits, ← ideal_distribution hexpands]
  simp only [test, ProbComp.eval_bind, ProbComp.eval_sampleBits, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]

end Cslib.Crypto.GeneratorPadding
