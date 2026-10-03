/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.PseudorandomGenerator
public import Cslib.Crypto.Game.Hybrid
public import Cslib.Crypto.Computational.Reduction
public import Cslib.Computability.Probabilistic.UniformNat

/-!
# Polynomial stretch from one-bit pseudorandom generators

Keep a seed of the original length at the front of a word. Each iteration expands that seed
by one bit and retains the previously emitted suffix. The security proof replaces successive
seed expansions by uniform bits, using one uniformly randomized reduction across all hops.
The seed width may differ from the security parameter, and the generator may capture an index.
`indexed_indistinguishable` preserves a secure choice in such a family. Efficiency only needs a
bounded seed prefix; the one-bit length promise is used separately to prove output lengths.

## References

* B. Barak, [*Pseudorandomness*, CS 127, length extension for PRGs]
  (https://www.boazbarak.org/cs127spring16/chap03-pseudorandom-generators).
  We retain the final seed and reverse the order of the emitted bits. The reduction explicitly
  samples its hop to preserve uniformity, with dyadic padding for strict fair-coin sampling.
-/

@[expose] public section

namespace Cslib.Crypto.PRGStretch

open Probability

/-- Expand the first `n` bits, preserving the previously emitted suffix. -/
def step (generator : Word → Word) (n : ℕ) (word : Word) : Word :=
  generator (word.take n) ++ word.drop n

/-- Repeat seed expansion a specified number of times. -/
def iterate (generator : Word → Word) (n count : ℕ) (word : Word) : Word :=
  (step generator n)^[count] word

/-- A one-bit generator yields `count n` additional bits from an `n`-bit seed. -/
def stretch (generator : Word → Word) (count : ℕ → ℕ) (seed : Word) : Word :=
  iterate generator seed.length (count seed.length) seed

/-- Each call increases the whole word's length by one, even on short intermediate words. -/
theorem length_step {generator : Word → Word}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n : ℕ) (word : Word) :
    (step generator n word).length = word.length + 1 := by
  simp only [step, List.length_append, hlen, List.length_take, List.length_drop]
  lia

/-- The loop's length invariant. -/
theorem length_iterate {generator : Word → Word}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n count : ℕ) (word : Word) :
    (iterate generator n count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    simp only [iterate, Function.iterate_succ_apply', length_step hlen]
    simp only [iterate] at ih
    lia

/-- A generator need only expand seeds at the specified length. Longer input words carry a
saved suffix, and every subsequent iteration again uses a correctly sized seed prefix. -/
theorem length_iterate_of_le {generator : Word → Word} {seedBits : ℕ}
    (hlen : ∀ seed, seed.length = seedBits → (generator seed).length = seedBits + 1)
    (count : ℕ) (word : Word) (hword : seedBits ≤ word.length) :
    (iterate generator seedBits count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    rw [iterate, Function.iterate_succ_apply']
    change (step generator seedBits (iterate generator seedBits count word)).length = _
    rw [step, List.length_append, hlen _ (by
      rw [List.length_take, ih]
      exact Nat.min_eq_left (by lia)), List.length_drop, ih]
    lia

/-- A valid seed prefix is expanded independently of the saved suffix. -/
theorem step_append (generator : Word → Word) {n : ℕ} (seed suffix : Word)
    (hlen : seed.length = n) : step generator n (seed ++ suffix) = generator seed ++ suffix := by
  subst n
  simp [step]

/-- Iteration may capture an arbitrary encoded input. Every call reads only a bounded seed
prefix, so polynomial time follows without a length promise on the generator. -/
theorem iterate_isPolyTime {α : Type} {input : α ↪ Word}
    {generator : α → Word → Word} {seedBits count : α → ℕ} {word : α → Word}
    (hgenerator : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => generator pair.1 pair.2))
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => iterate (generator a) (seedBits a) (count a) (word a)) := by
  obtain ⟨c, d, hlength⟩ := hgenerator.length_le
  obtain ⟨cs, ds, hseed⟩ := hseedBits.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hseed
  have hstep : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => step (generator pair.1) (seedBits pair.1) pair.2) := by
    unfold step
    polytime
  apply IsPolyTime.iterate_with_bounded_growth (stateEncoding := wordEncoding)
    (step := fun a => step (generator a) (seedBits a)) hword hcount hstep
    (growth := fun n => c * (2 * n + cs * (n + 1) ^ ds + 2) ^ d) (by fun_prop)
  intro a state
  have h := hlength (a, state.take (seedBits a))
  simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply,
    List.length_take] at h
  have hbound : (generator a (state.take (seedBits a))).length ≤
      c * (2 * (input a).length + cs * ((input a).length + 1) ^ ds + 2) ^ d :=
    h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by have := hseed a; lia) d))
  simp only [step, wordEncoding, Function.Embedding.refl_apply, List.length_append,
    List.length_drop]
  lia

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeIterate : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyHead #[(``iterate, ``iterate_isPolyTime)]

/-- Any efficiently computed iteration count gives an efficient generator. -/
theorem stretch_isPolyTime {generator : Word → Word} {count : ℕ → ℕ}
    (hgenerator : IsPolyTime wordEncoding generator)
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n))) :
    IsPolyTime wordEncoding (stretch generator count) := by
  unfold stretch
  polytime

/-- Hybrid `i` has `i` genuinely random suffix bits and `total - i` seed expansions left. -/
noncomputable def hybrid (generator : Word → Word) (n total i : ℕ) : PMF Word :=
  (uniformBits (n + i)).map (iterate generator n (total - i))

/-- The initial hybrid is the stretched generator's output. -/
theorem hybrid_zero (generator : Word → Word) (count : ℕ → ℕ) (n : ℕ) :
    hybrid generator n (count n) 0 = generatorEnsemble (stretch generator count) n := by
  simp only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble, PRG.Generator.outputDist]
  simp only [PMF.map, PRG.Generator.coe_mk]
  apply PMF.bind_congr_on_support
  intro seed hseed
  simp only [Function.comp_def, stretch, length_of_mem_support_uniformBits hseed]

/-- The final hybrid is uniform at the expanded length. -/
@[simp] theorem hybrid_last (generator : Word → Word) (n total : ℕ) :
    hybrid generator n total total = uniformBits (n + total) := by
  unfold hybrid iterate
  simp only [Nat.sub_self, Function.iterate_zero]
  exact PMF.map_id _

/-- Replacing the challenge by a genuine generator output gives the earlier hybrid. -/
theorem real_hop (generator : Word → Word) (n total i : ℕ) (hi : i < total) :
    (generatorEnsemble generator n).bind (fun challenge =>
      (uniformBits i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total i := by
  have hcount : total - i = total - (i + 1) + 1 := by lia
  simp only [generatorEnsemble, PRG.Generator.outputDist, PMF.bind_map, hybrid,
    uniformBits_add, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro seed hseed
  congr 1
  funext suffix
  simp only [iterate, hcount, Function.iterate_succ_apply,
    step_append generator seed suffix (length_of_mem_support_uniformBits hseed)]
  rfl

/-- Replacing the challenge by uniform bits gives the next hybrid. -/
theorem ideal_hop (generator : Word → Word) (n total i : ℕ) :
    (uniformBits (n + 1)).bind (fun challenge =>
      (uniformBits i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total (i + 1) := by
  rw [hybrid, show n + (i + 1) = (n + 1) + i by lia, uniformBits_add (n + 1) i]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Embed one challenge at a chosen hop; out-of-range hops reject on both sides. -/
noncomputable def hop (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n i : ℕ) (challenge : Word) : ProbComp Bool := do
  if i < count n then
    let suffix ← OracleComp.sampleBits i
    adversary n (iterate generator n (count n - (i + 1)) (challenge ++ suffix))
  else pure false

/-- One uniform reduction samples its hop using a bounded number of fair bits. -/
noncomputable def reduction (generator : Word → Word) (count : ℕ → ℕ)
    (adversary : Distinguisher) : Distinguisher := fun n challenge => do
  let i ← sampleBoundedIndex (count n)
  hop generator count adversary n i challenge

-- The tactic composes a sampled index, a conditional sample, and the supplied distinguisher.
/-- The reduction's complete efficiency proof uses the public programming interface. -/
theorem reduction_isPPT {generator : Word → Word} {count : ℕ → ℕ}
    {adversary : Distinguisher} (hgenerator : IsPolyTime wordEncoding generator)
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hadversary : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (reduction generator count adversary) := by
  unfold reduction hop
  ppt

/-- Apply the same random-hop reduction at an explicit seed length, with any captured test. -/
noncomputable def test (generator : Word → Word) (seedBits count : ℕ)
    (adversary : Word → ProbComp Bool) (challenge : Word) : ProbComp Bool :=
  reduction generator (fun _ => count) (fun _ => adversary) seedBits challenge

/-- Captured parameters, generator code, and the adversary compose through the public tactics. -/
theorem test_isPPT {α : Type} {input : α ↪ Word}
    {generator : α → Word → Word} {seedBits count : α → ℕ}
    {adversary : α → Word → ProbComp Bool}
    (hgenerator : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => generator pair.1 pair.2))
    (hseedBits : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hadversary : IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun pair => adversary pair.1 pair.2)) :
    IsPPTOn (pairEncoding input wordEncoding) boolEncoding
      (fun pair => test (generator pair.1) (seedBits pair.1) (count pair.1)
        (adversary pair.1) pair.2) := by
  unfold test reduction hop
  ppt

/-- Capping a sampled index only merges rejecting branches. -/
theorem hop_min (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n i : ℕ) (challenge : Word) :
    hop generator count adversary n (min (count n) i) challenge =
      hop generator count adversary n i challenge := by
  by_cases hi : i < count n
  · rw [Nat.min_eq_right (by lia)]
  · simp [hop, hi, Nat.min_eq_left (by lia : count n ≤ i)]

/-- The randomized reduction is exactly a uniform mixture of its padded hop reductions. -/
theorem eval_reduction (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n : ℕ) (challenge : Word) :
    ProbComp.eval (reduction generator count adversary n challenge) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind
        (fun i => ProbComp.eval (hop generator count adversary n i.val challenge)) := by
  simp only [reduction, ProbComp.eval_bind, eval_sampleBoundedIndex, PMF.bind_map,
    Function.comp_def, hop_min]

/-- The real challenge at a fixed hop realizes the earlier hybrid experiment. -/
theorem eval_real_hop (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n i : ℕ) :
    (generatorEnsemble generator n).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) i).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF Word =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (real_hop generator n (count n) i hi)
    simpa [hop, hi, ProbComp.eval, PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- The ideal challenge at a fixed hop realizes the next hybrid experiment. -/
theorem eval_ideal_hop (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n i : ℕ) :
    (uniformBits (n + 1)).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) (i + 1)).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF Word =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (ideal_hop generator n (count n) i)
    simpa [hop, hi, ProbComp.eval, PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- Exact loss of the uniform reduction, including the padded sampling outcomes. -/
theorem advantage_eq (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n : ℕ) :
    advantage (prgRealGame (stretch generator count) adversary n)
        (prgIdealGame (fun n => n + count n) adversary n) =
      (2 ^ (Nat.log 2 (count n) + 1) : ℕ) *
        advantage (prgRealGame generator (reduction generator count adversary) n)
          (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n) := by
  have hreal : ProbComp.eval (prgRealGame generator (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) i.val).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgRealGame]
    change (generatorEnsemble generator n).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_real_hop generator count adversary n i.val
  have hideal : ProbComp.eval (prgIdealGame (fun n => n + 1)
      (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) (i.val + 1)).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgIdealGame]
    change (uniformBits (n + 1)).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_ideal_hop generator count adversary n i.val
  have havg := Game.advantage_hybrid_average
    (fun i => (hybrid generator n (count n) i).bind
      (fun word => ProbComp.eval (adversary n word))) (count n)
    (2 ^ (Nat.log 2 (count n) + 1))
    (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (count n)))
  rw [← hreal, ← hideal, hybrid_zero, hybrid_last] at havg
  exact havg

/-- The same exact loss applies with the seed length independent of the security parameter.
This form is convenient for indexed candidate families. -/
theorem test_advantage_eq (generator : Word → Word) (seedBits count : ℕ)
    (adversary : Word → ProbComp Bool) :
    Game.advantage
      (((uniformBits seedBits).map (iterate generator seedBits count)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformBits (seedBits + count)).bind (fun word => ProbComp.eval (adversary word))) =
      (2 ^ (Nat.log 2 count + 1) : ℕ) *
        Game.advantage
          (((uniformBits seedBits).map generator).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word)))
          ((uniformBits (seedBits + 1)).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word))) := by
  have h := advantage_eq generator (fun _ => count) (fun _ => adversary) seedBits
  simp only [advantage, eval_prgRealGame, eval_prgIdealGame, PRG.Generator.realExperiment,
    PRG.Generator.idealExperiment] at h
  rw [← generatorEnsemble, ← hybrid_zero generator (fun _ => count) seedBits] at h
  simpa only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble, PRG.Generator.outputDist,
    PRG.Generator.coe_mk, test] using h

/-- Padding the sampled hop loses at most twice the number of expansions. -/
theorem advantage_le (generator : Word → Word) (count : ℕ → ℕ) (adversary : Distinguisher)
    (n : ℕ) (hpositive : 0 < count n) :
    advantage (prgRealGame (stretch generator count) adversary n)
        (prgIdealGame (fun n => n + count n) adversary n) ≤
      (2 * count n : ℕ) *
        advantage (prgRealGame generator (reduction generator count adversary) n)
          (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n) := by
  rw [advantage_eq]
  have hpow : 2 ^ (Nat.log 2 (count n) + 1) ≤ 2 * count n := by
    rw [pow_succ]
    have := Nat.pow_log_le_self 2 (by lia : count n ≠ 0)
    lia
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpow) (advantage_nonneg _ _)

/-- Efficient unary counts give a polynomial bound on the reduction's dyadic loss. -/
theorem loss_polynomial {count : ℕ → ℕ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n))) :
    PolynomiallyBounded (fun n => 2 ^ (Nat.log 2 (count n) + 1)) :=
  dyadicSize_polynomiallyBounded.comp hcount.polynomiallyBounded

/-- Polynomially many expansions preserve the secure choice in a uniformly efficient family.
The choice is supplied only in the proof; each reduction receives its index as ordinary input. -/
theorem indexed_indistinguishable {generator : ℕ → ℕ → Word → Word}
    {seedBits count choose : ℕ → ℕ}
    (hgenerator : IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      (fun input => generator input.1.1 input.1.2 input.2))
    (hseedBits : IsPolyTime unaryEncoding (fun n => unaryEncoding (seedBits n)))
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hsecure : ∀ adversary : ℕ → ℕ → Word → ProbComp Bool,
      IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
        boolEncoding (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformBits (seedBits n)).map (generator n (choose n))).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformBits (seedBits n + 1)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word))))) :
    ∀ adversary : ℕ → ℕ → Word → ProbComp Bool,
      IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
        boolEncoding (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformBits (seedBits n)).map
          (iterate (generator n (choose n)) (seedBits n) (count n))).bind
            (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformBits (seedBits n + count n)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))) := by
  intro adversary hadversary
  let reduction := fun n index =>
    test (generator n index) (seedBits n) (count n) (adversary n index)
  have hreduce : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun input => reduction input.1.1 input.1.2 input.2) :=
    test_isPPT (generator := fun input : ℕ × ℕ => generator input.1 input.2)
      (seedBits := fun input : ℕ × ℕ => seedBits input.1)
      (count := fun input : ℕ × ℕ => count input.1)
      (adversary := fun input : ℕ × ℕ => adversary input.1 input.2)
      hgenerator (by polytime) (by polytime) hadversary
  have h := (hsecure reduction hreduce).polynomiallyBounded_mul (loss_polynomial hcount)
  exact h.congr (fun n => (test_advantage_eq _ _ _ _).symm)

/-- Polynomially many seed expansions preserve computational indistinguishability. -/
theorem indistinguishable {generator : Word → Word} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n))) :
    ComputationallyIndistinguishable (generatorEnsemble (stretch generator count))
      (fun n => uniformBits (n + count n)) := by
  intro adversary hadversary
  have hreduce := reduction_isPPT hgenerator.polyTime hcount hadversary
  have hnegligible := hgenerator.indistinguishable _ hreduce
  have hloss := hnegligible.polynomiallyBounded_mul (loss_polynomial hcount)
  convert hloss using 1
  funext n
  exact advantage_eq generator count adversary n

/-- A positive efficiently computed number of one-bit expansions is a secure PRG. -/
theorem pseudorandomGenerator {generator : Word → Word} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)))
    (hpositive : ∀ n, 0 < count n) :
    PseudorandomGenerator (stretch generator count) (fun n => n + count n) := by
  refine PseudorandomGenerator.of_indistinguishable
    (stretch_isPolyTime hgenerator.polyTime hcount) ?_ ?_
    (indistinguishable hgenerator hcount)
  · intro seed
    exact length_iterate hgenerator.length_eq _ _ _
  · intro n
    exact Nat.lt_add_of_pos_right (hpositive n)

end Cslib.Crypto.PRGStretch

namespace Cslib.Crypto

open Probability

/-- Amplify a one-bit PRG to any efficiently computed, strictly larger output length. -/
theorem PseudorandomGenerator.amplify {generator : Word → Word}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (target : ℕ → ℕ) (htarget : IsPolyTime unaryEncoding (fun n => unaryEncoding (target n)))
    (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun n => target n - n)) target := by
  have hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (target n - n)) := by polytime
  have h := PRGStretch.pseudorandomGenerator hgenerator hcount (fun n => by
    have := hstretch n
    lia)
  convert h using 1
  funext n
  have := hstretch n
  lia

/-- Truncating a PRG to an efficiently computed, still-expanding length preserves security. -/
theorem PseudorandomGenerator.truncate {generator : Word → Word} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length)
    (target : ℕ → ℕ)
    (htarget : IsPolyTime unaryEncoding (fun n => unaryEncoding (target n)))
    (hle : ∀ n, target n ≤ length n) (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (fun seed => (generator seed).take (target seed.length)) target := by
  have hpoly := hgenerator.polyTime
  refine PseudorandomGenerator.of_indistinguishable (by polytime) ?_ hstretch ?_
  · intro seed
    simp only [List.length_take, hgenerator.length_eq, Nat.min_eq_left (hle _)]
  · have h := hgenerator.indistinguishable.map (fun n word => word.take (target n)) (by polytime)
    simpa only [← generatorEnsemble_postprocess generator (fun n word => word.take (target n)),
      uniformBits_take (hle _)] using h

end Cslib.Crypto
