/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Search
public import Cslib.Crypto.Computational.GeneratorPadding
public import Cslib.Crypto.Computational.PseudorandomGenerator
public import Cslib.Crypto.Computational.UniformChoice

/-!
# Extending an expanding family to every seed length

Choose the largest parameter whose seed fits the input, run that family member on a prefix,
and retain the unused suffix. A finite initial range uses a trivial one-bit extension.
The schedule need not be monotone. Bounded search is efficient, and adjacent parameters give
the polynomial relation needed to preserve negligible decay.

Security uses `ComputationallyIndistinguishable.uniform_bound`: the padding test receives the
prospective input length as an ordinary index, and one negligible bound covers all relevant
lengths. No nonuniform choice of a bad length is supplied to the reduction.

This completes the seed-length convention for the construction in Thomas Holenstein,
*Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness*,
TCC 2006, Section 5, [write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorReindex

open Probability Filter

/-- The greatest parameter whose prescribed seed fits, or zero when none fits. -/
def parameter (length : ℕ → ℕ) (size : ℕ) : ℕ :=
  Nat.findGreatest (fun n => length n ≤ size) size

/-- Searching an efficient schedule up to an efficient unary input size is polynomial-time. -/
theorem parameter_isPolyTime {α : Type} {input : α ↪ Word} {length : ℕ → ℕ} {size : α → ℕ}
    (hlength : IsPolyTime unaryEncoding (fun n => unaryEncoding (length n)))
    (hsize : IsPolyTime input (fun a => unaryEncoding (size a))) :
    IsPolyTime input (fun a => unaryEncoding (parameter length (size a))) := by
  unfold parameter
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeParameter : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyUnaryHead #[(``parameter, ``parameter_isPolyTime)]

/-- The bounded search never returns a parameter above its input size. -/
theorem parameter_le (length : ℕ → ℕ) (size : ℕ) : parameter length size ≤ size :=
  Nat.findGreatest_le _

/-- Once the zeroth seed fits, the selected seed fits too. -/
theorem parameter_fits {length : ℕ → ℕ} {size : ℕ} (hsize : length 0 ≤ size) :
    length (parameter length size) ≤ size :=
  Nat.findGreatest_spec (P := fun n => length n ≤ size) (Nat.zero_le _) hsize

/-- The next parameter's seed is too large, even when the schedule is not monotone. -/
theorem lt_length_succ_parameter {length : ℕ → ℕ} (hge : ∀ n, n + 1 ≤ length n) (size : ℕ) :
    size < length (parameter length size + 1) := by
  have hle := parameter_le length size
  by_cases hlt : parameter length size < size
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun n => length n ≤ size)
      (Nat.lt_succ_self (parameter length size)) (by lia : parameter length size + 1 ≤ size))
  · have := hge (parameter length size + 1)
    lia

/-- Every fixed parameter eventually fits, so the selected parameter tends to infinity. -/
theorem parameter_tendsto (length : ℕ → ℕ) : Tendsto (parameter length) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (max n (length n))] with size hsize
  exact Nat.le_findGreatest (by lia : n ≤ size) (by lia : length n ≤ size)

/-- Search for a family member that fits, then preserve the remaining seed bits as padding. -/
def generate (length : ℕ → ℕ) (generator : ℕ → Word → Word) (seed : Word) : Word :=
  if length 0 ≤ seed.length then
    let n := parameter length seed.length
    GeneratorPadding.generate (length n) seed.length (generator n) seed
  else seed ++ [false]

/-- Generation composes bounded search, the supplied family, and padding. -/
theorem generate_isPolyTime {length : ℕ → ℕ} {generator : ℕ → Word → Word}
    (hlength : IsPolyTime unaryEncoding (fun n => unaryEncoding (length n)))
    (hgenerator : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun a => generator a.1 a.2)) : IsPolyTime id (generate length generator) := by
  change IsPolyTime wordEncoding (generate length generator)
  unfold generate
  polytime

/-- Every input is expanded by exactly one bit, including the finite initial range. -/
theorem length_generate {length : ℕ → ℕ} {generator : ℕ → Word → Word}
    (houtput : ∀ n seed, seed.length = length n → (generator n seed).length = length n + 1)
    (seed : Word) : (generate length generator seed).length = seed.length + 1 := by
  unfold generate
  split_ifs with hfits
  · exact GeneratorPadding.length_generate (parameter_fits hfits)
      (fun word hword => by rw [houtput _ _ hword]; lia) rfl
  · simp

/-- At a fixed seed length, the reindexed ensemble is exactly the corresponding padded family. -/
theorem generate_distribution (length : ℕ → ℕ) (generator : ℕ → Word → Word)
    {size : ℕ} (hsize : length 0 ≤ size) :
    generatorEnsemble (generate length generator) size =
      (uniformBits size).map (GeneratorPadding.generate (length (parameter length size)) size
        (generator (parameter length size))) := by
  simp only [generatorEnsemble, PRG.Generator.outputDist, PRG.Generator.coe_mk, PMF.map]
  apply PMF.bind_congr_on_support
  intro seed hseed
  simp only [Function.comp_def, generate, length_of_mem_support_uniformBits hseed,
    ite_eq_left hsize]

/-- Extending a uniformly efficient secure family preserves uniform security at every seed
length. A single calibrated reduction controls every padding length in the polynomial range. -/
theorem indistinguishable {length : ℕ → ℕ} {generator : ℕ → Word → Word}
    (hlength : IsPolyTime unaryEncoding (fun n => unaryEncoding (length n)))
    (hge : ∀ n, n + 1 ≤ length n)
    (hgenerator : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun a => generator a.1 a.2))
    (hsecure : ComputationallyIndistinguishable
      (fun n => (uniformBits (length n)).map (generator n))
      (fun n => uniformBits (length n + 1))) :
    ComputationallyIndistinguishable (generatorEnsemble (generate length generator))
      (fun n => uniformBits (n + 1)) := by
  intro adversary hadversary
  let real : ℕ → ProbComp Word := fun n => generator n <$> OracleComp.sampleBits (length n)
  let ideal : ℕ → ProbComp Word := fun n => OracleComp.sampleBits (length n + 1)
  have hreal : IsPPTOn unaryEncoding wordEncoding real := by unfold real; ppt
  have hideal : IsPPTOn unaryEncoding wordEncoding ideal := by unfold ideal; ppt
  have hfamily : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (real n)) (fun n => ProbComp.eval (ideal n)) := by
    simpa only [real, ideal, ProbComp.eval_map, ProbComp.eval_sampleBits] using hsecure
  let test := fun n size => GeneratorPadding.test (length n) size (adversary size)
  have htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun a => test a.1.1 a.1.2 a.2) := by
    unfold test
    exact GeneratorPadding.test_isPPT
      (seedBits := fun a : ℕ × ℕ => length a.1) (commonBits := Prod.snd)
      (adversary := fun a : ℕ × ℕ => adversary a.2) (by polytime) (by polytime) (by ppt)
  obtain ⟨ε, hε, hε₀, hbound⟩ := hfamily.uniform_bound hreal hideal
    (bound := fun n => length (n + 1)) (by polytime) test htest
  have hdecay := hε.comp_of_polynomial_bound (parameter_tendsto length)
    (hlength.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1)))
    (Eventually.of_forall (fun size => (lt_length_succ_parameter hge size).le))
  apply hdecay.trans_eventually_abs_le
  filter_upwards [eventually_ge_atTop (length 0)] with size hsize
  simp only [Function.comp_def, distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample,
    abs_of_nonneg (Game.advantage_nonneg _ _), abs_of_nonneg (hε₀ _)]
  rw [generate_distribution length generator hsize,
    GeneratorPadding.advantage_eq _ _ (parameter_fits hsize) (Nat.lt_succ_self _)]
  simpa only [advantage, real, ideal, test, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_sampleBits] using
    hbound (parameter length size) size (lt_length_succ_parameter hge size).le

/-- A uniformly efficient one-bit expanding family on a polynomial schedule gives a PRG
stretching every input by one bit. -/
theorem pseudorandomGenerator {length : ℕ → ℕ} {generator : ℕ → Word → Word}
    (hlength : IsPolyTime unaryEncoding (fun n => unaryEncoding (length n)))
    (hge : ∀ n, n + 1 ≤ length n)
    (hgenerator : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun a => generator a.1 a.2))
    (houtput : ∀ n seed, seed.length = length n → (generator n seed).length = length n + 1)
    (hsecure : ComputationallyIndistinguishable
      (fun n => (uniformBits (length n)).map (generator n))
      (fun n => uniformBits (length n + 1))) :
    PseudorandomGenerator (generate length generator) (fun n => n + 1) :=
  .of_indistinguishable (generate_isPolyTime hlength hgenerator)
    (length_generate houtput) (fun _ => Nat.lt_succ_self _)
    (indistinguishable hlength hge hgenerator hsecure)

end Cslib.Crypto.GeneratorReindex
