/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.WordExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.WordSeedExtraction

/-!
# Combining the three pseudoentropy extractors

One collection of sampler seeds supplies the observations, hidden labels, and remaining seed
randomness. Each extractor keeps its independent public matrix seed. The security argument
replaces the remaining-seed component, then the labels, then the observations by uniform bits.
The middle transition uses a strict PPT test; the other two are statistical transitions.
The indexed theorem allows any valid choice from a polynomial-size family. The choice belongs
only to the security argument; the efficient test handles all indices uniformly.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Lemma 5 and the final proof of Theorem 1.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use the shared Boolean-matrix family and make the three component transitions explicit.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.ThreeSource

open Probability

/-- Finish the first two components by hashing observations and retaining the label hash. -/
noncomputable def finish (bound observationBits : ℕ) (middle : List Word × Word × Word) :
    ProbComp Word := do
  let first ← extractWordObservations bound observationBits middle.1
  return first ++ (middle.2.1 ++ middle.2.2)

/-- The last observation hash composes with a certified intermediate result. -/
theorem finish_isPPT {α : Type} {input : α ↪ Word} {bound observationBits : α → ℕ}
    {middle : α → List Word × Word × Word}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hobservation : IsPolyTime input (fun a => unaryEncoding (observationBits a)))
    (hmiddle : IsPolyTime input (fun a =>
      pairEncoding (listEncoding wordEncoding) (pairEncoding wordEncoding wordEncoding)
        (middle a))) :
    IsPPTOn input wordEncoding (fun a => finish (bound a) (observationBits a) (middle a)) := by
  unfold finish
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptFinish : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``finish, ``finish_isPPT)]

/-- Sample once and hash all three components, retaining every independent matrix seed. -/
noncomputable def extract (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp ((Word × Bool) × Word)) : ProbComp Word := do
  let samples ← OracleComp.replicate count source
  let third ← extractWordSeeds count seedBits remainingBits samples
  let middle ← extractWordLabels count labelBits third.1
  let front ← finish bound observationBits middle
  return front ++ (third.2.1 ++ third.2.2)

/-- The complete three-component program is PPT from ordinary sampler and size certificates. -/
theorem extract_isPPT {α : Type} {input : α ↪ Word}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {source : α → ProbComp ((Word × Bool) × Word)}
    (hsource : IsPPTOn input
      (pairEncoding (pairEncoding wordEncoding boolEncoding) wordEncoding) source)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hobservation : IsPolyTime input (fun a => unaryEncoding (observationBits a)))
    (hlabel : IsPolyTime input (fun a => unaryEncoding (labelBits a)))
    (hremaining : IsPolyTime input (fun a => unaryEncoding (remainingBits a))) :
    IsPPTOn input wordEncoding (fun a => extract (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (source a)) := by
  unfold extract
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtract : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``extract, ``extract_isPPT)]

/-- The first hybrid replaces the remaining-seed component by independent uniform bits. -/
noncomputable def withoutSeeds
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp (Word × Bool)) : ProbComp Word := do
  let middle ← OracleComp.replicate count source >>= extractWordLabels count labelBits
  let front ← finish bound observationBits middle
  let suffix ← OracleComp.sampleBits (remainingBits * (count * seedBits) + remainingBits)
  return front ++ suffix

/-- The second hybrid also replaces the label component by independent uniform bits. -/
noncomputable def withoutLabels
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp Word) : ProbComp Word := do
  let first ← OracleComp.replicate count source >>= extractWordObservations bound observationBits
  let middle ← OracleComp.sampleBits (labelBits * count + labelBits)
  let third ← OracleComp.sampleBits (remainingBits * (count * seedBits) + remainingBits)
  return (first ++ middle) ++ third

/-- The output length counts every digest and every retained matrix seed. -/
def outputLength (count seedBits bound observationBits labelBits remainingBits : ℕ) : ℕ :=
  (observationBits * (count * (2 * bound + 1)) + observationBits) +
    (labelBits * count + labelBits) + (remainingBits * (count * seedBits) + remainingBits)

/-- Every supported output has the advertised length when sampled observations fit the bound.
The statement also covers zero-sized components and malformed retained seeds. -/
theorem length_extract (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp ((Word × Bool) × Word))
    (hbound : ∀ sample ∈ (ProbComp.eval source).support, sample.1.1.length ≤ bound)
    {output : Word} (houtput : output ∈ (ProbComp.eval
      (extract count seedBits bound observationBits labelBits remainingBits source)).support) :
    output.length = outputLength count seedBits bound observationBits labelBits remainingBits := by
  simp only [extract, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at houtput
  obtain ⟨samples, hsamples, third, hthird, middle, hmiddle, front, hfront, rfl⟩ := houtput
  have hsamples := (ProbComp.mem_support_replicate_iff count source samples).mp hsamples
  have hthird := extractMatrixLabels_result (count * seedBits) remainingBits List.flatten
    samples hthird
  have hmiddle := extractMatrixLabels_result count labelBits id third.1 hmiddle
  have hfits : ∀ observation ∈ middle.1, observation.length ≤ bound := by
    intro observation hobservation
    rw [hmiddle.1, hthird.1, List.map_map] at hobservation
    obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hobservation
    exact hbound sample (hsamples.2 sample hsample)
  have hcount : middle.1.length = count := by
    rw [hmiddle.1, List.length_map, hthird.1, List.length_map, hsamples.1]
  simp only [finish, bind_pure_comp, ProbComp.eval_map, PMF.mem_support_map_iff] at hfront
  obtain ⟨first, hfirst, rfl⟩ := hfront
  have hfirst := length_extractWordObservations bound observationBits middle.1 hfits hfirst
  simp only [List.length_append, hfirst, hcount, hmiddle.2.1, hmiddle.2.2,
    hthird.2.1, hthird.2.2, outputLength, Nat.add_assoc]

/-- Original sampler coins followed by the three matrix seeds in execution order. -/
def seedLength (count seedBits bound observationBits labelBits remainingBits : ℕ) : ℕ :=
  count * seedBits + (remainingBits * (count * seedBits) +
    (labelBits * count + observationBits * (count * (2 * bound + 1))))

section Lengths

variable {α : Type} {input : α ↪ Word}
  {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
  (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
  (hseed : IsPolyTime input (fun a => unaryEncoding (seedBits a)))
  (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
  (hobservation : IsPolyTime input (fun a => unaryEncoding (observationBits a)))
  (hlabel : IsPolyTime input (fun a => unaryEncoding (labelBits a)))
  (hremaining : IsPolyTime input (fun a => unaryEncoding (remainingBits a)))

include hcount hseed hbound hobservation hlabel hremaining

/-- The exact seed ledger can be computed in unary from efficient dimensions. -/
theorem seedLength_isPolyTime : IsPolyTime input (fun a => unaryEncoding
    (seedLength (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a))) := by
  unfold seedLength
  polytime

/-- The exact output ledger can be computed in unary from efficient dimensions. -/
theorem outputLength_isPolyTime : IsPolyTime input (fun a => unaryEncoding
    (outputLength (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a))) := by
  unfold outputLength
  polytime

end Lengths

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeLengths : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyUnaryHead
    #[(``seedLength, ``seedLength_isPolyTime), (``outputLength, ``outputLength_isPolyTime)]

/-- Retained matrix seeds cancel in the expansion budget: only the digest bits must exceed
the original sampler coins. `ThreeSource.Seeded` realizes this exact input length. -/
theorem seedLength_lt_outputLength_iff
    (count seedBits bound observationBits labelBits remainingBits : ℕ) :
    seedLength count seedBits bound observationBits labelBits remainingBits <
        outputLength count seedBits bound observationBits labelBits remainingBits ↔
      count * seedBits < observationBits + labelBits + remainingBits := by
  unfold seedLength outputLength
  lia

/-- Moving the independent ideal seed component to the end gives the first hybrid exactly. -/
theorem eval_ideal_remaining
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp (Word × Bool)) :
    ProbComp.eval (extractMatrixLabelsIdeal source count (count * seedBits) remainingBits >>=
      fun third => do
        let middle ← extractWordLabels count labelBits third.1
        let front ← finish bound observationBits middle
        return front ++ (third.2.1 ++ third.2.2)) =
      ProbComp.eval (withoutSeeds count seedBits bound observationBits labelBits remainingBits
        source) := by
  simpa only [withoutSeeds, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using
    eval_extractMatrixLabelsIdeal_append source count (count * seedBits) remainingBits
      (fun samples => extractWordLabels count labelBits samples >>= finish bound observationBits)

/-- Once the label hash is ideal, its seed and digest can follow the observation extraction. -/
theorem eval_ideal_labels (count bound observationBits labelBits : ℕ)
    (source : ProbComp Word) :
    ProbComp.eval (extractWordLabelsIdeal source count labelBits >>= finish bound observationBits) =
      ProbComp.eval (do
        let first ← OracleComp.replicate count source >>=
          extractWordObservations bound observationBits
        let middle ← OracleComp.sampleBits (labelBits * count + labelBits)
        return first ++ middle) := by
  simpa only [extractWordLabelsIdeal, ProbComp.eval_bind, finish, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using
    eval_extractMatrixLabelsIdeal_append source count count labelBits
      (extractWordObservations bound observationBits)

open Probability.PMF Filter in
/-- Statistical extraction replaces the third component while retaining the data needed by
the first two components. No efficiency assumption is needed for this postprocessing. -/
theorem replace_remaining {pair : SamplablePair} (saved : pair.SeedRealization)
    (bound inverseSlack observationBits labelBits remainingBits : ℕ → ℕ)
    (hbudget : ∀ᶠ n in atTop, remainingBits n = 0 ∨
      remainingBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (extract (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (saved.sampleWithSeed n)))
      (fun n => ProbComp.eval (withoutSeeds (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (pair.sample n))) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := (saved.extract_word_seeds inverseSlack remainingBits hbudget).bind
    (fun n third => ProbComp.eval (do
      let middle ← extractWordLabels (count n) (labelBits n) third.1
      let front ← finish (bound n) (observationBits n) middle
      return front ++ (third.2.1 ++ third.2.2)))
  apply h.congr
  intro n
  simp only [← ProbComp.eval_bind, eval_ideal_remaining, extract, bind_assoc, count]

open Probability.PMF Filter in
/-- After the other two components are uniform, observation extraction completes the
statistical comparison with a single uniform word of the advertised total length. -/
theorem replace_observations {pair : SamplablePair} (saved : pair.SeedRealization)
    (bound inverseSlack observationBits labelBits remainingBits : ℕ → ℕ)
    (hbound : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hbudget : ∀ᶠ n in atTop, observationBits n = 0 ∨
      observationBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (withoutLabels (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (Prod.fst <$> pair.sample n)))
      (fun n => uniformBits (outputLength (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n))) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := (saved.extract_word_observations bound inverseSlack observationBits hbound hbudget).bind
    (fun n first => ProbComp.eval (do
      let middle ← OracleComp.sampleBits (labelBits n * count n + labelBits n)
      let third ← OracleComp.sampleBits
        (remainingBits n * (count n * saved.length n) + remainingBits n)
      return (first ++ middle) ++ third))
  apply h.congr
  intro n
  simp only [withoutLabels, outputLength, count, ProbComp.eval_bind, ProbComp.eval_sampleBits,
    ProbComp.eval_pure, uniformBits_add, PMF.bind_bind, PMF.pure_bind, PMF.map,
    Function.comp_def, List.append_assoc]

open Probability.PMF Filter in
/-- Indexed label extraction remains secure when the test computes the observation hash and
supplies the independent third component. Only the proof uses the chosen valid index. -/
theorem replace_indexed_labels {pair : SamplablePair} {gap : ℕ → ℝ} (hpair : pair.HasGap gap)
    (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (hcandidates : IsPolyTime unaryEncoding (fun n => unaryEncoding (candidates n)))
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)))
    (hobservation : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (observationBits input.1 input.2)))
    (hlabel : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (labelBits input.1 input.2)))
    (hremaining : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (remainingBits input.1 input.2)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    (hnumerator : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (numerator input.1 input.2)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (adversary : ℕ → ℕ → Word → ProbComp Bool)
    (hadversary : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun input => adversary input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => advantage
      (withoutSeeds (count n) (saved.length n) (bound n) (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (pair.sample n) >>=
          adversary n (choose n))
      (withoutLabels (count n) (saved.length n) (bound n) (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (Prod.fst <$> pair.sample n) >>=
          adversary n (choose n))) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have hlength := saved.length_isPolyTime
  have hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)) :=
    ExtractionSchedule.count_isPolyTime (isPolyTime_input unaryEncoding) hlength hslack
  let test (n i : ℕ) (middle : List Word × Word × Word) : ProbComp Bool := do
    let front ← finish (bound n) (observationBits n i) middle
    let suffix ← OracleComp.sampleBits
      (remainingBits n i * (count n * saved.length n) + remainingBits n i)
    adversary n i (front ++ suffix)
  have htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      (pairEncoding (listEncoding wordEncoding) (pairEncoding wordEncoding wordEncoding)))
      boolEncoding (fun input => test input.1.1 input.1.2 input.2) := by
    dsimp only [test]
    ppt
  have h := hpair.extract_indexed_word_labels saved choose hcandidates hlabel hslack hnumerator
    hdensity hchoose hvalid hbudget test htest
  have hideal (n i : ℕ) :
      ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (labelBits n i) >>= test n i) =
      ProbComp.eval (withoutLabels (count n) (saved.length n) (bound n)
        (observationBits n i) (labelBits n i) (remainingBits n i) (Prod.fst <$> pair.sample n) >>=
          adversary n i) := by
    have heq := congrArg (fun distribution : PMF Word => distribution.bind (fun front =>
      ProbComp.eval (do
        let suffix ← OracleComp.sampleBits
          (remainingBits n i * (count n * saved.length n) + remainingBits n i)
        adversary n i (front ++ suffix))))
      (eval_ideal_labels (count n) (bound n) (observationBits n i) (labelBits n i)
        (Prod.fst <$> pair.sample n))
    simpa only [test, withoutLabels, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind] using heq
  apply h.congr
  intro n
  change Game.advantage _ _ = Game.advantage _ _
  rw [hideal]
  simp only [count, test, withoutSeeds, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]

end Cslib.Crypto.Pseudoentropy.ThreeSource

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF Filter

/-- A valid candidate in an efficient polynomial-size family passes the complete three-source
game argument. The candidate may vary arbitrarily with the parameter; one efficient indexed test
handles the entire family. All three entropy budgets are needed only at the chosen candidate. -/
theorem SamplablePair.HasGap.extract_indexed_three {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (hcandidates : IsPolyTime unaryEncoding (fun n => unaryEncoding (candidates n)))
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)))
    (hobservation : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (observationBits input.1 input.2)))
    (hlabel : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (labelBits input.1 input.2)))
    (hremaining : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (remainingBits input.1 input.2)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    (hnumerator : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (numerator input.1 input.2)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n (choose n) = 0 ∨
      observationBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n (choose n) = 0 ∨
      remainingBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n)))
    (test : ℕ → ℕ → Word → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
      boolEncoding (fun input => test input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => advantage
      (ThreeSource.extract (count n) (saved.length n) (bound n) (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (saved.sampleWithSeed n) >>=
          test n (choose n))
      (OracleComp.sampleBits (ThreeSource.outputLength (count n) (saved.length n) (bound n)
        (observationBits n (choose n)) (labelBits n (choose n)) (remainingBits n (choose n))) >>=
          test n (choose n))) := by
  let continuation := fun n word => ProbComp.eval (test n (choose n) word)
  have third := (ThreeSource.replace_remaining saved bound inverseSlack
    (fun n => observationBits n (choose n)) (fun n => labelBits n (choose n))
    (fun n => remainingBits n (choose n)) hlast).bind continuation
  have middle := ThreeSource.replace_indexed_labels hpair saved choose hcandidates hbound
    hobservation hlabel hremaining hslack hnumerator hdensity hchoose hvalid hmiddle test htest
  have first := (ThreeSource.replace_observations saved bound inverseSlack
    (fun n => observationBits n (choose n)) (fun n => labelBits n (choose n))
    (fun n => remainingBits n (choose n)) hfits hfirst).bind continuation
  simp only [advantage, Game.advantage_eq_dist, ProbComp.eval_bind] at middle
  simpa only [advantage, Game.advantage_eq_dist, ProbComp.eval_bind, ProbComp.eval_sampleBits,
    StatisticallyIndistinguishable, continuation] using
      third.trans (StatisticallyIndistinguishable.trans middle first)

/-- The three-source construction is computationally uniform under its three entropy budgets.
The schedules must be computed by uniform polynomial-time algorithms. `ThreeSource.Seeded`
implements this ensemble deterministically with an exact seed budget. Constructing an expanding
family with a valid candidate and combining its candidates are separate obligations. -/
theorem SamplablePair.HasGap.extract_three {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {bound inverseSlack observationBits labelBits remainingBits numerator densityBound : ℕ → ℕ}
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)))
    (hobservation : IsPolyTime unaryEncoding (fun n => unaryEncoding (observationBits n)))
    (hlabel : IsPolyTime unaryEncoding (fun n => unaryEncoding (labelBits n)))
    (hremaining : IsPolyTime unaryEncoding (fun n => unaryEncoding (remainingBits n)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    (hnumerator : IsPolyTime unaryEncoding (fun n => unaryEncoding (numerator n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n = 0 ∨
      observationBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n = 0 ∨
      remainingBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval (ThreeSource.extract (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (saved.sampleWithSeed n)))
      (fun n => uniformBits (ThreeSource.outputLength (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n))) := by
  dsimp only
  intro adversary hadversary
  have h := hpair.extract_indexed_three saved (fun _ => 0)
    (candidates := fun _ => 1) (observationBits := fun n _ => observationBits n)
    (labelBits := fun n _ => labelBits n) (remainingBits := fun n _ => remainingBits n)
    (numerator := fun n _ => numerator n) (by polytime) hbound (by polytime) (by polytime)
    (by polytime) hslack (by polytime) hdensity hfits (Eventually.of_forall (by intro n; decide))
    hvalid hfirst hmiddle hlast (fun n _ => adversary n) (by ppt)
  simpa only [advantage, distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample,
    ProbComp.eval_sampleBits] using h

end Cslib.Crypto.Pseudoentropy
