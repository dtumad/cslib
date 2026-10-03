/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import Cslib.Computability.Probabilistic.LinearHash

/-!
# Repeated extraction with an executable matrix hash

The three extractors in the pseudoentropy construction share this program. A client prepares
the label list as one word; the extractor supplies a fresh matrix, hashes at the declared width,
and retains every observation and the complete matrix seed. Width normalization specifies total
behavior on malformed inputs without affecting the finite extraction laws.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use the shared Boolean-matrix family in place of finite-field hashing.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability

/-- Hash prepared labels with a fresh matrix, retaining the observations and full seed. -/
noncomputable def extractMatrixLabels {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → Word) (samples : List (Observation × Label)) :
    ProbComp (List Observation × Word × Word) :=
  extractLabels (OracleComp.sampleBits (outputBits * inputBits))
    (fun seed labels => LinearHash.wordHash outputBits seed
      (List.ofFn (wordBits inputBits (prepare labels)))) samples

/-- Every result preserves the observations and has the declared seed and digest lengths. -/
theorem extractMatrixLabels_result {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → Word) (samples : List (Observation × Label))
    {result : List Observation × Word × Word}
    (hresult : result ∈ (ProbComp.eval
      (extractMatrixLabels inputBits outputBits prepare samples)).support) :
    result.1 = samples.map Prod.fst ∧ result.2.1.length = outputBits * inputBits ∧
      result.2.2.length = outputBits := by
  simp only [extractMatrixLabels, extractLabels, bind_pure_comp, ProbComp.eval_map,
    ProbComp.eval_sampleBits, PMF.mem_support_map_iff] at hresult
  obtain ⟨seed, hseed, rfl⟩ := hresult
  exact ⟨rfl, mem_support_uniformBits_iff.mp hseed, LinearHash.length_wordHash _ _ _⟩

/-- The comparison experiment preserves the observations and samples independent seed and bits. -/
noncomputable def extractMatrixLabelsIdeal {Observation : Type} (source : ProbComp Observation)
    (count inputBits outputBits : ℕ) : ProbComp (List Observation × Word × Word) := do
  let observations ← OracleComp.replicate count source
  let seed ← OracleComp.sampleBits (outputBits * inputBits)
  let bits ← OracleComp.sampleBits outputBits
  return (observations, seed, bits)

/-- Runtime dimensions and a certified preparation function give an ordinary PPT program. -/
theorem extractMatrixLabels_isPPT {α Observation Label : Type} {input : α ↪ Word}
    {observation : Observation ↪ Word} {label : Label ↪ Word}
    {inputBits outputBits : α → ℕ} {prepare : α → List Label → Word}
    {samples : α → List (Observation × Label)}
    (hinput : IsPolyTime input (fun a => unaryEncoding (inputBits a)))
    (houtput : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hprepare : IsPolyTime (pairEncoding input (listEncoding label))
      (fun pair => prepare pair.1 pair.2))
    (hsamples : IsPolyTime input
      (fun a => listEncoding (pairEncoding observation label) (samples a))) :
    IsPPTOn input
      (pairEncoding (listEncoding observation) (pairEncoding wordEncoding wordEncoding))
      (fun a => extractMatrixLabels (inputBits a) (outputBits a) (prepare a) (samples a)) := by
  unfold extractMatrixLabels
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtractMatrixLabels : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``extractMatrixLabels, ``extractMatrixLabels_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hsamples => solve | aesop (rule_sets := [PolyTime])))

/-- Word matrix sampling and hashing exactly realize the finite extraction experiment. -/
theorem eval_extractMatrixLabels {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → Word) (samples : List (Observation × Label)) :
    ProbComp.eval (extractMatrixLabels inputBits outputBits prepare samples) =
      (ProbComp.eval (extractLabels (OracleComp.uniform (BitString (outputBits * inputBits)))
        (fun seed labels => LinearHash.hash (maskEquiv outputBits inputBits seed)
          (wordBits inputBits (prepare labels))) samples)).map
            (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  simp only [extractMatrixLabels, extractLabels, bind_pure_comp, ProbComp.eval_map,
    OracleComp.uniform, ProbComp.eval_sample]
  simp only [ProbComp.eval, OracleComp.eval_sampleBits,
    uniformBits, PMF.map_comp, Function.comp_def, LinearHash.wordHash_eq_ofFn,
    masksFromWord, wordBits_ofFn]

/-- The ideal word program agrees with the finite ideal distribution, retaining the full seed. -/
theorem eval_extractMatrixLabelsIdeal {Observation : Type} (source : ProbComp Observation)
    (count inputBits outputBits : ℕ) :
    ProbComp.eval (extractMatrixLabelsIdeal source count inputBits outputBits) =
      (extractLabelsIdeal (Output := BitString outputBits) source count
        (OracleComp.uniform (BitString (outputBits * inputBits)))).map
          (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  simp only [extractMatrixLabelsIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    extractLabelsIdeal, OracleComp.uniform, ProbComp.eval_sample, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  simp only [ProbComp.eval, OracleComp.eval_sampleBits, uniformBits, PMF.map,
    Function.comp_def, PMF.bind_bind, PMF.pure_bind]

/-- In the ideal experiment, the public matrix seed and digest together form one uniform word.
The continuation may depend on all retained observations. -/
theorem eval_extractMatrixLabelsIdeal_bind {Observation Output : Type}
    (source : ProbComp Observation) (count inputBits outputBits : ℕ)
    (next : List Observation → Word → ProbComp Output) :
    ProbComp.eval (extractMatrixLabelsIdeal source count inputBits outputBits >>= fun result =>
      next result.1 (result.2.1 ++ result.2.2)) =
        ProbComp.eval (do
          let observations ← OracleComp.replicate count source
          let bits ← OracleComp.sampleBits (outputBits * inputBits + outputBits)
          next observations bits) := by
  simp only [extractMatrixLabelsIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_sampleBits]
  rw [uniformBits_add]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]

/-- An independently uniform ideal hash can be sampled after processing the observations. -/
theorem eval_extractMatrixLabelsIdeal_append {Observation : Type}
    (source : ProbComp Observation) (count inputBits outputBits : ℕ)
    (next : List Observation → ProbComp Word) :
    ProbComp.eval (extractMatrixLabelsIdeal source count inputBits outputBits >>= fun result =>
      (fun front => front ++ (result.2.1 ++ result.2.2)) <$> next result.1) =
        ProbComp.eval (do
          let front ← OracleComp.replicate count source >>= next
          let suffix ← OracleComp.sampleBits (outputBits * inputBits + outputBits)
          return front ++ suffix) := by
  rw [eval_extractMatrixLabelsIdeal_bind source count inputBits outputBits
    (fun observations suffix => (fun front => front ++ suffix) <$> next observations)]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    ProbComp.eval_sampleBits, PMF.bind_bind]
  congr 1
  funext observations
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]

end Cslib.Crypto.Pseudoentropy
