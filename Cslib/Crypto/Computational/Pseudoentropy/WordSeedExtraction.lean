/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.MatrixExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.SeedExtraction

/-!
# Executable extraction of observations and retained seeds

The first and third components use the same matrix extractor as label extraction. Concatenating
fixed-width sampler seeds supplies an injective input representation. Public observations first
receive self-delimiting padding, since their lengths can vary. Each program retains its complete
independent matrix seed.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the first and third extractors and Games 0--1.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF Filter

/-- Pad observations injectively, concatenate their blocks, and return a fresh hash seed and
digest as one word. The seed is part of the output, as in the strong extractor. -/
noncomputable def extractWordObservations (bound outputBits : ℕ)
    (observations : List Word) : ProbComp Word :=
  LinearHash.extract outputBits ((observations.map (padWord bound)).flatten)

/-- Bounded observations give a fixed output length, including the complete public seed. -/
theorem length_extractWordObservations (bound outputBits : ℕ) (observations : List Word)
    (hbound : ∀ observation ∈ observations, observation.length ≤ bound) {output : Word}
    (houtput : output ∈ (ProbComp.eval
      (extractWordObservations bound outputBits observations)).support) :
    output.length = outputBits * (observations.length * (2 * bound + 1)) + outputBits := by
  simpa only [length_flatten_padWord bound observations hbound] using
    LinearHash.length_extract outputBits
    ((observations.map (padWord bound)).flatten) houtput

/-- Observation padding and concatenation compose with the existing matrix extractor. -/
theorem extractWordObservations_isPPT {α : Type} {input : α ↪ Word}
    {bound outputBits : α → ℕ} {observations : α → List Word}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (houtput : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hobservations : IsPolyTime input (fun a => listEncoding wordEncoding (observations a))) :
    IsPPTOn input wordEncoding
      (fun a => extractWordObservations (bound a) (outputBits a) (observations a)) := by
  unfold extractWordObservations
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtractWordObservations : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``extractWordObservations, ``extractWordObservations_isPPT)]

/-- The first statistical transition with an executable hash and self-delimiting padding.
Only supported observations need to fit the bound; `exists_observationBound` supplies an efficient
bound for every PPT sampler. The uniform comparison includes the entire matrix seed. -/
theorem SamplablePair.SeedRealization.extract_word_observations {pair : SamplablePair}
    (saved : pair.SeedRealization) (bound inverseSlack outputBits : ℕ → ℕ)
    (hbound : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (Prod.fst <$> pair.sample n) >>=
        extractWordObservations (bound n) (outputBits n)))
      (fun n => uniformBits (outputBits n * (count n * (2 * bound n + 1)) + outputBits n)) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  let observe (n : ℕ) (value : pair.Observation n) : BitString (2 * bound n + 1) :=
    wordBits (2 * bound n + 1) (padWord (bound n) (pair.encode n value))
  let source (n : ℕ) := ((pair.joint n).map Prod.fst).map (observe n)
  have hentropy (n : ℕ) : entropy (source n) = entropy ((pair.joint n).map Prod.fst) := by
    apply entropy_map_of_injOn
    intro x hx y hy hxy
    exact (pair.encode n).injective
      (word_eq_of_paddedBits_eq (hbound n x hx) (hbound n y hy) hxy)
  have h := seededHash_replicate_statisticallyIndistinguishable
    (fun n => OracleComp.sample (source n)) saved.length inverseSlack outputBits
    (by
      intro n value hvalue
      simp only [ProbComp.eval_sample, source, ← saved.output_distribution, PMF.map_comp,
        Function.comp_def] at hvalue ⊢
      simpa [BitString, Real.logb_pow] using
        uniform_map_mass_ge (fun bits => observe n (saved.output n bits).1) value hvalue)
    (fun n => OracleComp.uniform (BitString (outputBits n * (count n * (2 * bound n + 1)))))
    (fun n key values =>
      LinearHash.hash (maskEquiv (outputBits n) (count n * (2 * bound n + 1)) key)
        (wordBits (count n * (2 * bound n + 1)) (values.map List.ofFn).flatten))
    (fun n => by
      simpa only [OracleComp.uniform, ProbComp.eval_sample, wordBits_flatten_ofFn] using
        (LinearHash.isTwoUniversal_flat (count n * (2 * bound n + 1)) (outputBits n)).precompose
          (maskEquiv (count n) (2 * bound n + 1)).symm.injective)
    (by simpa only [ProbComp.eval_sample, hentropy] using hbudget)
  have hmap := h.map (fun _ result => List.ofFn result.1 ++ List.ofFn result.2)
  apply hmap.congr
  intro n
  have hpublic : ProbComp.eval (padWord (bound n) <$> (Prod.fst <$> pair.sample n)) =
      ProbComp.eval (List.ofFn <$> OracleComp.sample (source n)) := by
    simp only [ProbComp.eval_map, ProbComp.eval_sample, pair.eval_sample, source, PMF.map_comp,
      Function.comp_def]
    apply map_congr_on_support
    intro result hresult
    exact (ofFn_wordBits (length_padWord (hbound n result.1
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨result, hresult, rfl⟩)))).symm
  have hreal := LinearHash.eval_extract_replicate (OracleComp.sample (source n))
    (count n) (outputBits n)
  rw [ProbComp.eval_bind, ← ProbComp.eval_replicate_congr hpublic] at hreal
  simp only [OracleComp.replicate_map, ProbComp.eval_map, PMF.bind_map, Function.comp_def] at hreal
  dsimp only
  simp only [OracleComp.uniform, ProbComp.eval_sample] at hreal ⊢
  rw [← hreal, uniformBits_add]
  simp only [count, extractWordObservations, OracleComp.replicate_map, ProbComp.eval_bind,
    ProbComp.eval_map, uniformBits, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Hash complete sampler seeds while retaining every sampled observation and label. -/
noncomputable def extractWordSeeds (count seedBits outputBits : ℕ)
    (samples : List ((Word × Bool) × Word)) : ProbComp (List (Word × Bool) × Word × Word) :=
  extractMatrixLabels (count * seedBits) outputBits List.flatten samples

/-- Seed-block concatenation composes with the shared matrix extractor's PPT certificate. -/
theorem extractWordSeeds_isPPT {α : Type} {input : α ↪ Word}
    {count seedBits outputBits : α → ℕ} {samples : α → List ((Word × Bool) × Word)}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (houtput : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hsamples : IsPolyTime input (fun a =>
      listEncoding (pairEncoding (pairEncoding wordEncoding boolEncoding) wordEncoding)
        (samples a))) :
    IsPPTOn input (pairEncoding (listEncoding (pairEncoding wordEncoding boolEncoding))
      (pairEncoding wordEncoding wordEncoding))
      (fun a => extractWordSeeds (count a) (seedBits a) (outputBits a) (samples a)) := by
  unfold extractWordSeeds
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtractWordSeeds : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``extractWordSeeds, ``extractWordSeeds_isPPT)]

/-- The third statistical transition for ordinary programs, with matrix universality discharged.
The ideal program preserves the complete pair output and independently samples seed and bits. -/
theorem SamplablePair.SeedRealization.extract_word_seeds {pair : SamplablePair}
    (saved : pair.SeedRealization) (inverseSlack outputBits : ℕ → ℕ)
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (saved.sampleWithSeed n) >>=
        extractWordSeeds (count n) (saved.length n) (outputBits n)))
      (fun n => ProbComp.eval (extractMatrixLabelsIdeal (pair.sample n) (count n)
        (count n * saved.length n) (outputBits n))) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := saved.remainingSeed_word_extraction inverseSlack outputBits
    (fun n => OracleComp.uniform (BitString (outputBits n * (count n * saved.length n))))
    (fun n key values => LinearHash.hash (maskEquiv (outputBits n) (count n * saved.length n) key)
      (wordBits (count n * saved.length n) values.flatten))
    (fun n => by
      simpa only [OracleComp.uniform, ProbComp.eval_sample, wordBits_flatten_ofFn] using
        (LinearHash.isTwoUniversal_flat (count n * saved.length n) (outputBits n)).precompose
          (maskEquiv (count n) (saved.length n)).symm.injective) hbudget
  have hmap := h.map (fun _ result =>
    (result.1, List.ofFn result.2.1, List.ofFn result.2.2))
  apply hmap.congr
  intro n
  simp only [count, extractWordSeeds, ProbComp.eval_bind, eval_extractMatrixLabels,
    eval_extractMatrixLabelsIdeal, PMF.map_bind]

end Cslib.Crypto.Pseudoentropy
