/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Crypto.Computational.Basic
public import Cslib.Probability.Product
public import Cslib.Probability.Uniform
public import Cslib.Tactic.PPT

/-!
# XOR combination of independently seeded generators

Split a uniform tape into equal seed blocks, evaluate every indexed generator, and XOR their
outputs. A reduction simulates all but one candidate. Replacing that candidate's output by
uniform bits makes the combined output uniform, with no assumption on the other candidates.

This is the combination step in Thomas Holenstein, *Pseudorandom Generators from One-Way
Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorXor

open Probability

/-- Evaluate every candidate on its own seed block and XOR the outputs at the declared width. -/
def generate (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word) (seed : Word) : Word :=
  xorWords outputBits ((List.range count).map fun i => generator i (maskRow seedBits i seed))

/-- The output width is fixed, including on short or malformed input tapes. -/
@[simp] theorem length_generate (count seedBits outputBits : ℕ)
    (generator : ℕ → Word → Word) (seed : Word) :
    (generate count seedBits outputBits generator seed).length = outputBits := by
  simp only [generate, length_xorWords]

/-- Combining polynomially many uniformly efficient candidates uses ordinary collection code. -/
theorem generate_isPolyTime {α : Type} {input : α ↪ Word}
    {count seedBits outputBits : α → ℕ} {generator : α → ℕ → Word → Word} {seed : α → Word}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (houtputBits : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hgenerator : IsPolyTime (pairEncoding (pairEncoding input unaryEncoding) wordEncoding)
      (fun pair => generator pair.1.1 pair.1.2 pair.2))
    (hseed : IsPolyTime input seed) :
    IsPolyTime input (fun a => generate (count a) (seedBits a) (outputBits a) (generator a)
      (seed a)) := by
  unfold generate maskRow
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeGenerate : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyHead #[(``generate, ``generate_isPolyTime)]

/-- The executable combiner is the finite sum of its candidates' bitstring outputs. -/
theorem generate_eq_sum (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word)
    (seed : Word) :
    generate count seedBits outputBits generator seed =
      List.ofFn (∑ i : Fin count,
        wordBits outputBits
          (generator i.val (List.ofFn (masksFromWord count seedBits seed i)))) := by
  have hrows : (List.range count).map (fun i => generator i (maskRow seedBits i seed)) =
      List.ofFn (fun i : Fin count =>
        generator i.val (List.ofFn (masksFromWord count seedBits seed i))) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      congrArg (generator i) (maskRow_eq_ofFn seedBits ⟨i, by simpa using hi'⟩ seed)
  rw [generate, hrows, xorWords_ofFn]

/-- Uniform seed blocks are independent; the combiner's law is a sum over their finite tuple. -/
theorem generate_distribution (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word) :
    (uniformBits (count * seedBits)).map (generate count seedBits outputBits generator) =
      (PMF.uniformOfFintype (Fin count → BitString seedBits)).map
        (fun seeds => List.ofFn (∑ i : Fin count,
          wordBits outputBits (generator i.val (List.ofFn (seeds i))))) := by
  rw [← uniformBits_masksFromWord count seedBits, PMF.map_comp]
  congr 1
  funext seed
  exact generate_eq_sum ..

/-- A real challenge can replace the chosen candidate's output because its seed is independent
of every other seed block. The simulator may sample and discard the unused chosen block. -/
theorem real_distribution (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word)
    (i : Fin count) :
    ((uniformBits seedBits).map (generator i.val)).bind (fun challenge =>
      (uniformBits (count * seedBits)).map (generate count seedBits outputBits
        (fun j seed => if j = i.val then challenge else generator j seed))) =
      (uniformBits (count * seedBits)).map (generate count seedBits outputBits generator) := by
  simp_rw [generate_distribution]
  simp only [uniformBits, PMF.bind_map, Function.comp_def]
  let evaluate := fun seeds : Fin count → BitString seedBits =>
    List.ofFn (∑ j : Fin count, wordBits outputBits (generator j.val (List.ofFn (seeds j))))
  have h := congrArg (PMF.map evaluate)
    (PMF.uniformOfFintype_update (γ := BitString seedBits) i)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  refine Eq.trans ?_ h
  congr 1
  funext fresh
  congr 1
  funext seeds
  apply congrArg List.ofFn
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hji, hval]

/-- One uniform candidate masks the complete XOR, for every fixed choice of the other outputs. -/
theorem ideal_distribution (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word)
    (i : Fin count) :
    (uniformBits outputBits).bind (fun challenge =>
      (uniformBits (count * seedBits)).map (generate count seedBits outputBits
        (fun j seed => if j = i.val then challenge else generator j seed))) =
      uniformBits outputBits := by
  simp_rw [generate_distribution]
  simp only [uniformBits, PMF.bind_map, Function.comp_def]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  calc
    _ = (PMF.uniformOfFintype (Fin count → BitString seedBits)).bind
        (fun _ => (PMF.uniformOfFintype (BitString outputBits)).map List.ofFn) := by
      congr 1
      funext seeds
      have h := congrArg (PMF.map List.ofFn) (PMF.uniformOfFintype_map_sum_update
        (fun j : Fin count => wordBits outputBits (generator j.val (List.ofFn (seeds j)))) i)
      simp only [PMF.map_comp, Function.comp_def] at h
      refine Eq.trans ?_ h
      congr 1
      funext challenge
      apply congrArg (PMF.pure ∘ List.ofFn)
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        simp [hji, hval]
    _ = _ := PMF.bind_const _ _

/-- Simulate every other candidate and insert the supplied challenge at the chosen index. -/
noncomputable def test (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word)
    (index : ℕ) (adversary : Word → ProbComp Bool) (challenge : Word) : ProbComp Bool := do
  let seed ← OracleComp.sampleBits (count * seedBits)
  adversary (generate count seedBits outputBits
    (fun j coins => if j = index then challenge else generator j coins) seed)

/-- The reduction is a uniform program that captures its index and its distinguisher. -/
theorem test_isPPT {α : Type} {input : α ↪ Word}
    {count seedBits outputBits index : α → ℕ} {generator : α → ℕ → Word → Word}
    {adversary : α → Word → ProbComp Bool}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (houtputBits : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hindex : IsPolyTime input (fun a => unaryEncoding (index a)))
    (hgenerator : IsPolyTime (pairEncoding (pairEncoding input unaryEncoding) wordEncoding)
      (fun pair => generator pair.1.1 pair.1.2 pair.2))
    (hadversary : IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun pair => adversary pair.1 pair.2)) :
    IsPPTOn (pairEncoding input wordEncoding) boolEncoding (fun pair =>
      test (count pair.1) (seedBits pair.1) (outputBits pair.1) (generator pair.1) (index pair.1)
        (adversary pair.1) pair.2) := by
  unfold test
  ppt

/-- XOR combination loses no distinguishing advantage when reducing to a valid candidate. -/
theorem advantage_eq (count seedBits outputBits : ℕ) (generator : ℕ → Word → Word)
    (i : Fin count) (adversary : Word → ProbComp Bool) :
    Game.advantage
      (((uniformBits (count * seedBits)).map (generate count seedBits outputBits generator)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformBits outputBits).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformBits seedBits).map (generator i.val)).bind
        (fun word => ProbComp.eval (test count seedBits outputBits generator i.val adversary word)))
      ((uniformBits outputBits).bind
        (fun word =>
          ProbComp.eval (test count seedBits outputBits generator i.val adversary word))) := by
  conv_lhs => rw [← real_distribution count seedBits outputBits generator i,
    ← ideal_distribution count seedBits outputBits generator i]
  simp only [test, ProbComp.eval_bind, ProbComp.eval_sampleBits, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]

/-- One secure choice in a uniformly efficient family makes the XOR computationally uniform.
The combiner evaluates the whole family; only the reduction receives the proof's chosen index. -/
theorem indistinguishable {generator : ℕ → ℕ → Word → Word}
    {count seedBits outputBits choose : ℕ → ℕ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hseedBits : IsPolyTime unaryEncoding (fun n => unaryEncoding (seedBits n)))
    (houtputBits : IsPolyTime unaryEncoding (fun n => unaryEncoding (outputBits n)))
    (hgenerator : IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      (fun input => generator input.1.1 input.1.2 input.2))
    (hchoose : ∀ᶠ n in Filter.atTop, choose n < count n)
    (hsecure : ∀ adversary : ℕ → ℕ → Word → ProbComp Bool,
      IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
        boolEncoding (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformBits (seedBits n)).map (generator n (choose n))).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformBits (outputBits n)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word))))) :
    ComputationallyIndistinguishable
      (fun n => (uniformBits (count n * seedBits n)).map
        (generate (count n) (seedBits n) (outputBits n) (generator n)))
      (fun n => uniformBits (outputBits n)) := by
  intro adversary hadversary
  let reduction := fun n index =>
    test (count n) (seedBits n) (outputBits n) (generator n) index (adversary n)
  have hreduce : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun input => reduction input.1.1 input.1.2 input.2) := by
    unfold reduction
    apply test_isPPT (input := pairEncoding unaryEncoding unaryEncoding)
      (count := fun input => count input.1) (seedBits := fun input => seedBits input.1)
      (outputBits := fun input => outputBits input.1) (index := Prod.snd)
      (generator := fun input => generator input.1)
      (adversary := fun input => adversary input.1) <;>
      first | polytime | ppt
  apply (hsecure reduction hreduce).congr'
  filter_upwards [hchoose] with n hn
  simpa only [distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample] using
    (advantage_eq (count n) (seedBits n) (outputBits n) (generator n) ⟨choose n, hn⟩
      (adversary n)).symm

end Cslib.Crypto.GeneratorXor
