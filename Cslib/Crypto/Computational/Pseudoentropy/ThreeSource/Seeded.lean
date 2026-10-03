/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.ThreeSource

/-!
# Deterministic three-source extraction

The input contains exactly the original sampler seeds and three independent matrix seeds.
Ordinary word operations split this tape and evaluate the same hashes as the probabilistic
program. The implementation uses the shared row parser and polynomial-time combinators.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Lemma 5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  The matrix seeds are retained in full, so their lengths cancel from the expansion budget.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.ThreeSource

open Probability

/-- Evaluate the three hashes using supplied matrix seeds, preserving all three seeds. -/
def hashSamples (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (samples : List ((Word × Bool) × Word)) (firstKey middleKey lastKey : Word) : Word :=
  let observations := ((samples.map (fun sample => sample.1.1)).map (padWord bound)).flatten
  let labels := List.ofFn (wordBits count (samples.map (fun sample => sample.1.2)))
  let seeds := List.ofFn (wordBits (count * seedBits) (samples.map Prod.snd).flatten)
  ((firstKey ++ LinearHash.wordHash observationBits firstKey observations) ++
    (middleKey ++ LinearHash.wordHash labelBits middleKey labels)) ++
      (lastKey ++ LinearHash.wordHash remainingBits lastKey seeds)

/-- Deterministic hashing composes the same efficient word operations as the sampled program. -/
theorem hashSamples_isPolyTime {α : Type} {input : α ↪ Word}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {samples : α → List ((Word × Bool) × Word)} {firstKey middleKey lastKey : α → Word}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hobservation : IsPolyTime input (fun a => unaryEncoding (observationBits a)))
    (hlabel : IsPolyTime input (fun a => unaryEncoding (labelBits a)))
    (hremaining : IsPolyTime input (fun a => unaryEncoding (remainingBits a)))
    (hsamples : IsPolyTime input (fun a =>
      listEncoding (pairEncoding (pairEncoding wordEncoding boolEncoding) wordEncoding)
        (samples a)))
    (hfirst : IsPolyTime input firstKey) (hmiddle : IsPolyTime input middleKey)
    (hlast : IsPolyTime input lastKey) :
    IsPolyTime input (fun a => hashSamples (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (samples a)
      (firstKey a) (middleKey a) (lastKey a)) := by
  unfold hashSamples
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeHashSamples : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyHead #[(``hashSamples, ``hashSamples_isPolyTime)]

/-- Evaluate from one seed: sampler coins, remaining-seed matrix, label matrix, observation matrix.
Parsing is total even on short input tapes; exact sampling laws use `seedLength` input bits. -/
def generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : Word → Word × Bool) (tape : Word) : Word :=
  let coins := tape.take (count * seedBits)
  let tape := tape.drop (count * seedBits)
  let lastKey := tape.take (remainingBits * (count * seedBits))
  let tape := tape.drop (remainingBits * (count * seedBits))
  let middleKey := tape.take (labelBits * count)
  let firstKey := tape.drop (labelBits * count)
  let samples := (maskRows count seedBits coins).map (fun seed => (evaluate seed, seed))
  hashSamples count seedBits bound observationBits labelBits remainingBits samples
    firstKey middleKey lastKey

/-- Runtime dimensions, parsing, and every evaluator call are charged through ordinary
polynomial-time combinators. The callback may capture the original input. -/
theorem generate_isPolyTime {α : Type} {input : α ↪ Word}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {evaluate : α → Word → Word × Bool} {tape : α → Word}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hobservation : IsPolyTime input (fun a => unaryEncoding (observationBits a)))
    (hlabel : IsPolyTime input (fun a => unaryEncoding (labelBits a)))
    (hremaining : IsPolyTime input (fun a => unaryEncoding (remainingBits a)))
    (hevaluate : IsPolyTime (pairEncoding input wordEncoding) (fun a =>
      pairEncoding wordEncoding boolEncoding (evaluate a.1 a.2)))
    (htape : IsPolyTime input tape) :
    IsPolyTime input (fun a => generate (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (evaluate a) (tape a)) := by
  unfold generate
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeGenerate : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyHead #[(``generate, ``generate_isPolyTime)]

/-- Uniform input bits supply independent sampler coins and matrix seeds, with no padding
coins added by an execution clock. -/
theorem generate_distribution (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : Word → Word × Bool) :
    (uniformBits (seedLength count seedBits bound observationBits labelBits remainingBits)).map
        (generate count seedBits bound observationBits labelBits remainingBits evaluate) =
      (uniformBits (count * seedBits)).bind (fun coins =>
        (uniformBits (remainingBits * (count * seedBits))).bind (fun lastKey =>
          (uniformBits (labelBits * count)).bind (fun middleKey =>
            (uniformBits (observationBits * (count * (2 * bound + 1)))).map (fun firstKey =>
              hashSamples count seedBits bound observationBits labelBits remainingBits
                ((maskRows count seedBits coins).map (fun seed => (evaluate seed, seed)))
                firstKey middleKey lastKey)))) := by
  unfold seedLength
  let run (coins lastKey middleKey firstKey : Word) :=
    hashSamples count seedBits bound observationBits labelBits remainingBits
      ((maskRows count seedBits coins).map (fun seed => (evaluate seed, seed)))
      firstKey middleKey lastKey
  change (uniformBits _).bind (fun tape => PMF.pure
    (run (tape.take (count * seedBits))
      ((tape.drop (count * seedBits)).take (remainingBits * (count * seedBits)))
      (((tape.drop (count * seedBits)).drop (remainingBits * (count * seedBits))).take
        (labelBits * count))
      (((tape.drop (count * seedBits)).drop (remainingBits * (count * seedBits))).drop
        (labelBits * count)))) = _
  rw [uniformBits_bind_split (count * seedBits) _ (fun coins tape => PMF.pure
    (run coins (tape.take (remainingBits * (count * seedBits)))
      ((tape.drop (remainingBits * (count * seedBits))).take (labelBits * count))
      ((tape.drop (remainingBits * (count * seedBits))).drop (labelBits * count))))]
  congr 1
  funext coins
  rw [uniformBits_bind_split (remainingBits * (count * seedBits)) _
    (fun lastKey tape => PMF.pure
      (run coins lastKey (tape.take (labelBits * count)) (tape.drop (labelBits * count))))]
  congr 1
  funext lastKey
  exact uniformBits_bind_split (labelBits * count) _
    (fun middleKey firstKey => PMF.pure (run coins lastKey middleKey firstKey))

/-- Supplying independent uniform keys to the deterministic hash core realizes the three
probabilistic hashing calls exactly. Only the observation padding requires a size bound. -/
theorem eval_hashSamples (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (samples : List ((Word × Bool) × Word)) (hcount : samples.length = count)
    (hbound : ∀ sample ∈ samples, sample.1.1.length ≤ bound) :
    ProbComp.eval (do
      let third ← extractWordSeeds count seedBits remainingBits samples
      let middle ← extractWordLabels count labelBits third.1
      let front ← finish bound observationBits middle
      return front ++ (third.2.1 ++ third.2.2)) =
      (uniformBits (remainingBits * (count * seedBits))).bind (fun lastKey =>
        (uniformBits (labelBits * count)).bind (fun middleKey =>
          (uniformBits (observationBits * (count * (2 * bound + 1)))).map (fun firstKey =>
            hashSamples count seedBits bound observationBits labelBits remainingBits samples
              firstKey middleKey lastKey))) := by
  have hfits : ∀ observation ∈ samples.map (fun sample => sample.1.1),
      observation.length ≤ bound := by
    intro observation hobservation
    obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hobservation
    exact hbound sample hsample
  have hlength := length_flatten_padWord bound _ hfits
  simp only [List.length_map, hcount, List.map_map, Function.comp_def] at hlength
  simp only [ProbComp.eval_bind, extractWordSeeds, extractWordLabels, extractMatrixLabels,
    extractLabels, finish, extractWordObservations, LinearHash.extract,
    ProbComp.eval_pure, ProbComp.eval_sampleBits, hashSamples, List.map_map, Function.comp_def,
    hlength, PMF.pure_bind, PMF.map, PMF.bind_bind, id_eq]

/-- A uniform seed of exactly `seedLength` bits realizes the complete sampled extractor.
The only size premise is the observation bound on correctly sized sampler seeds. -/
theorem eval_generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : Word → Word × Bool)
    (hbound : ∀ seed, seed.length = seedBits → (evaluate seed).1.length ≤ bound) :
    (uniformBits (seedLength count seedBits bound observationBits labelBits remainingBits)).map
        (generate count seedBits bound observationBits labelBits remainingBits evaluate) =
      ProbComp.eval (extract count seedBits bound observationBits labelBits remainingBits (do
        let seed ← OracleComp.sampleBits seedBits
        return (evaluate seed, seed))) := by
  rw [generate_distribution, extract, ProbComp.eval_bind,
    ProbComp.eval_replicate_of_uniformBits count seedBits _ (fun seed => (evaluate seed, seed))
      (by simp only [bind_pure_comp, ProbComp.eval_map, ProbComp.eval_sampleBits])]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext coins
  symm
  apply eval_hashSamples
  · simp only [List.length_map, length_maskRows]
  · intro sample hsample
    obtain ⟨seed, hseed, rfl⟩ := List.mem_map.mp hsample
    exact hbound seed (length_of_mem_maskRows hseed)

/-- Every correctly sized seed produces the advertised fixed output length. -/
theorem length_generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : Word → Word × Bool)
    (hbound : ∀ seed, seed.length = seedBits → (evaluate seed).1.length ≤ bound)
    {tape : Word}
    (htape : tape.length =
      seedLength count seedBits bound observationBits labelBits remainingBits) :
    (generate count seedBits bound observationBits labelBits remainingBits evaluate tape).length =
      outputLength count seedBits bound observationBits labelBits remainingBits := by
  apply length_extract count seedBits bound observationBits labelBits remainingBits
    (do
      let seed ← OracleComp.sampleBits seedBits
      return (evaluate seed, seed))
  · intro sample hsample
    simp only [bind_pure_comp, ProbComp.eval_map, ProbComp.eval_sampleBits,
      PMF.mem_support_map_iff] at hsample
    obtain ⟨seed, hseed, rfl⟩ := hsample
    exact hbound seed (mem_support_uniformBits_iff.mp hseed)
  · rw [← eval_generate count seedBits bound observationBits labelBits remainingBits
      evaluate hbound]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨tape, mem_support_uniformBits_iff.mpr htape, rfl⟩

/-- The sampler's saved-seed evaluator implements the exact ensemble in the security theorem.
The observation bound only concerns outcomes in the support of the finite pair. -/
theorem eval_generate_of_realization {pair : SamplablePair} (saved : pair.SeedRealization)
    (n count bound observationBits labelBits remainingBits : ℕ)
    (hbound : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ bound) :
    (uniformBits (seedLength count (saved.length n) bound
        observationBits labelBits remainingBits)).map
        (generate count (saved.length n) bound observationBits labelBits remainingBits
          (saved.evaluate n)) =
      ProbComp.eval (extract count (saved.length n) bound observationBits labelBits remainingBits
        (saved.sampleWithSeed n)) :=
  eval_generate count (saved.length n) bound observationBits labelBits remainingBits
    (saved.evaluate n) (fun _ h => saved.observation_length_le n bound hbound h)

end Cslib.Crypto.Pseudoentropy.ThreeSource
