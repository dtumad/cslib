/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Computational.Ensemble
public import Cslib.Crypto.Primitives.PRG.Asymptotic

/-!
# Pseudorandom generators

A secure generator is deterministic polynomial time, stretches every input length, and maps uniform
seeds to an ensemble computationally indistinguishable from uniform words of the output length.
Both experiments give the distinguisher the seed-length security parameter. The expansion function
is constrained by actual output length and polynomial-time evaluation; it is not a free source of
exponentially long outputs.

Security is `PRG.Family.Secure` instantiated with uniform word distributions and `IsPPTTest`.
The semantic PRG API supplies the experiments and advantage; this module adds uniform efficient
generation and length expansion. Reductions can establish security through
`PseudorandomGenerator.of_indistinguishable` using ordinary probabilistic programs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.3.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- The output ensemble obtained from uniform seeds. -/
noncomputable def generatorEnsemble (generator : Word → Word) (n : ℕ) : PMF Word :=
  (PRG.Generator.mk generator).outputDist (uniformBits n)

/-- Postprocessing may use the original seed length, which equals the game's parameter. -/
theorem generatorEnsemble_postprocess (generator : Word → Word) (f : ℕ → Word → Word) (n : ℕ) :
    generatorEnsemble (fun seed => f seed.length (generator seed)) n =
      (generatorEnsemble generator n).map (f n) := by
  simp only [generatorEnsemble, PRG.Generator.outputDist, PRG.Generator.coe_mk, PMF.map_comp]
  simp only [PMF.map]
  apply PMF.bind_congr_on_support
  intro seed hseed
  simp only [Function.comp_def, length_of_mem_support_uniformBits hseed]

/-- The semantic family API specializes to computational indistinguishability for PPT tests. -/
theorem PRG.Family.secure_iff_indistinguishable {Seed : ℕ → Type*}
    (G : PRG.Family Seed (fun _ => Word)) (seed : ∀ n, PMF (Seed n)) (ideal : ℕ → PMF Word) :
    G.Secure IsPPTTest seed ideal ↔
      ComputationallyIndistinguishable (fun n => (G n).outputDist (seed n)) ideal :=
  computationallyIndistinguishable_iff_tests.symm

/-- The real PRG experiment: expand a uniform seed, then invoke the distinguisher. -/
noncomputable def prgRealGame (generator : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := distinguishingGame (generatorEnsemble generator n) (adversary n)

/-- The ideal PRG experiment: give the distinguisher a uniform word of the output length. -/
noncomputable def prgIdealGame (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := distinguishingGame (uniformBits (length n)) (adversary n)

/-- The real program denotes the real experiment of the semantic PRG API. -/
@[simp] theorem eval_prgRealGame (generator : Word → Word) (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgRealGame generator adversary n) =
      (PRG.Generator.mk generator).realExperiment (fun word => ProbComp.eval (adversary n word))
        (uniformBits n) := by
  simp [prgRealGame, distinguishingGame, generatorEnsemble, PRG.Generator.realExperiment]

/-- The ideal program denotes the ideal experiment of the semantic PRG API. -/
@[simp] theorem eval_prgIdealGame (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgIdealGame length adversary n) =
      PRG.Generator.idealExperiment (fun word => ProbComp.eval (adversary n word))
        (uniformBits (length n)) := by
  simp [prgIdealGame, distinguishingGame, PRG.Generator.idealExperiment]

/-- Both APIs use exactly the same advantage, with no change of normalization. -/
theorem prg_advantage_eq (generator : Word → Word) (length : ℕ → ℕ)
    (adversary : Distinguisher) (n : ℕ) :
    advantage (prgRealGame generator adversary n) (prgIdealGame length adversary n) =
      (PRG.Generator.mk generator).advantage (fun word => ProbComp.eval (adversary n word))
        (uniformBits n) (uniformBits (length n)) := by
  simp [advantage, PRG.Generator.advantage]

/-- A secure pseudorandom generator of the specified stretch, against uniform PPT distinguishers. -/
structure PseudorandomGenerator (generator : Word → Word) (length : ℕ → ℕ) : Prop where
  /-- One deterministic polynomial-time algorithm evaluates the generator. -/
  polyTime : IsPolyTime id generator
  /-- Output length depends only on seed length. -/
  length_eq : ∀ input, (generator input).length = length input.length
  /-- The generator strictly stretches every seed length. -/
  stretch : ∀ n, n < length n
  /-- The shared PRG security definition, restricted to uniform PPT tests. -/
  secure : PRG.Family.Secure (fun _ => PRG.Generator.mk generator) IsPPTTest
    uniformBits (fun n => uniformBits (length n))

/-- Prove PRG security by a program-based indistinguishability argument. -/
theorem PseudorandomGenerator.of_indistinguishable {generator : Word → Word} {length : ℕ → ℕ}
    (hpoly : IsPolyTime id generator)
    (hlen : ∀ input, (generator input).length = length input.length)
    (hstretch : ∀ n, n < length n)
    (hsecure : ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => uniformBits (length n))) : PseudorandomGenerator generator length :=
  ⟨hpoly, hlen, hstretch, computationallyIndistinguishable_iff_tests.mp hsecure⟩

/-- A secure generator's output is computationally indistinguishable from uniform. -/
theorem PseudorandomGenerator.indistinguishable {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => uniformBits (length n)) :=
  computationallyIndistinguishable_iff_tests.mpr h.secure

/-- The generator's stretch is necessarily bounded by a polynomial. -/
theorem PseudorandomGenerator.length_le {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ c d : ℕ, ∀ n, length n ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hbound⟩ := h.polyTime.length_le
  refine ⟨c, d, fun n => ?_⟩
  simpa [h.length_eq] using hbound (List.replicate n false)

/-- A generator's real samples have polynomially bounded length. -/
theorem PseudorandomGenerator.bounded_real {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    PolynomiallyBoundedEnsemble (generatorEnsemble generator) :=
  (PolynomiallyBoundedEnsemble.uniformBits PolynomiallyBounded.id).map h.polyTime

/-- A generator's ideal samples have polynomially bounded length as well. -/
theorem PseudorandomGenerator.bounded_ideal {generator : Word → Word} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    PolynomiallyBoundedEnsemble (fun n => uniformBits (length n)) :=
  PolynomiallyBoundedEnsemble.uniformBits h.length_le

end Cslib.Crypto
