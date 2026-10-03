/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.LabelExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.MatrixExtraction

/-!
# Executable extraction of repeated labels

The program samples a flat Boolean matrix, hashes the labels, and retains every observation and
the matrix seed. Its exact law agrees with the finite two-universal family used by the extraction
theorems. The supplied input width also defines behavior on malformed sample lists: labels are
truncated or padded with false before hashing.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Game 2.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  The Boolean-matrix implementation replaces the write-up's finite-field hash family.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability

/-- Extract labels using an explicitly sampled matrix, retaining observations and the full seed. -/
noncomputable def extractWordLabels (count outputBits : ℕ) (samples : List (Word × Bool)) :
    ProbComp (List Word × Word × Word) :=
  extractMatrixLabels count outputBits id samples

/-- The comparison experiment keeps the observations and independently samples the hash seed
and output bits. -/
noncomputable def extractWordLabelsIdeal (source : ProbComp Word) (count outputBits : ℕ) :
    ProbComp (List Word × Word × Word) :=
  extractMatrixLabelsIdeal source count count outputBits

/-- Runtime dimensions and sample lists compose into a strict PPT extractor. -/
theorem extractWordLabels_isPPT {α : Type} {input : α ↪ Word} {count outputBits : α → ℕ}
    {samples : α → List (Word × Bool)}
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (houtput : IsPolyTime input (fun a => unaryEncoding (outputBits a)))
    (hsamples : IsPolyTime input
      (fun a => listEncoding (pairEncoding wordEncoding boolEncoding) (samples a))) :
    IsPPTOn input
      (pairEncoding (listEncoding wordEncoding) (pairEncoding wordEncoding wordEncoding))
      (fun a => extractWordLabels (count a) (outputBits a) (samples a)) := by
  unfold extractWordLabels
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtractWordLabels : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``extractWordLabels, ``extractWordLabels_isPPT)]

/-- The finite and word extractors have exactly the same law, even on malformed sample lists. -/
theorem eval_extractWordLabels (count outputBits : ℕ) (samples : List (Word × Bool)) :
    ProbComp.eval (extractWordLabels count outputBits samples) =
      (ProbComp.eval (extractLabels (OracleComp.uniform (BitString (outputBits * count)))
        (fun seed bits => LinearHash.hash (maskEquiv outputBits count seed) (wordBits count bits))
          samples)).map (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  exact eval_extractMatrixLabels count outputBits id samples

/-- The ideal word program agrees with the finite ideal distribution and retains the full seed. -/
theorem eval_extractWordLabelsIdeal (source : ProbComp Word) (count outputBits : ℕ) :
    ProbComp.eval (extractWordLabelsIdeal source count outputBits) =
      (extractLabelsIdeal (Output := BitString outputBits) source count
        (OracleComp.uniform (BitString (outputBits * count)))).map
          (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  exact eval_extractMatrixLabelsIdeal source count count outputBits

/-- An ordinary word test after extraction gives the finite test required by the security
theorem. Sampling, padding, hashing, and encoding the public data are all charged to PPT.
The test and dimensions may depend on any encoded runtime parameter. -/
theorem extractedWordTest_isPPT {α : Type} {input : α ↪ Word} {count outputBits : α → ℕ}
    (test : α → List Word × Word × Word → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding input (pairEncoding (listEncoding wordEncoding)
      (pairEncoding wordEncoding wordEncoding))) boolEncoding (fun input => test input.1 input.2))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (houtput : IsPolyTime input (fun a => unaryEncoding (outputBits a))) :
    IsPPTOn (pairEncoding input
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
      (fun input => extractLabels
        (OracleComp.uniform (BitString (outputBits input.1 * count input.1)))
        (fun seed bits => LinearHash.hash (maskEquiv (outputBits input.1) (count input.1) seed)
          (wordBits (count input.1) bits)) input.2 >>= fun result =>
            test input.1 (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  have hword : IsPPTOn (pairEncoding input
      (listEncoding (pairEncoding wordEncoding boolEncoding))) boolEncoding
      (fun input => extractWordLabels (count input.1) (outputBits input.1) input.2 >>=
        test input.1) := by ppt
  apply hword.congr
  intro input
  simp only [ProbComp.eval_bind, eval_extractWordLabels, PMF.bind_map, Function.comp_def]

open Filter in
/-- An efficient indexed family of word extractors is computationally uniform along any bounded
choice satisfying the entropy budget. The choice is used only in the proof and need not be
efficient; the reduction certifies the whole family of tests. -/
theorem SamplablePair.HasGap.extract_indexed_word_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates inverseSlack densityBound : ℕ → ℕ} {outputBits numerator : ℕ → ℕ → ℕ}
    (hcandidates : IsPolyTime unaryEncoding (fun n => unaryEncoding (candidates n)))
    (houtput : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (outputBits input.1 input.2)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    (hnumerator : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
      (fun input => unaryEncoding (numerator input.1 input.2)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n (choose n) +
        2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ → ℕ → List Word × Word × Word → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      (pairEncoding (listEncoding wordEncoding) (pairEncoding wordEncoding wordEncoding)))
      boolEncoding (fun input => test input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => advantage
      (OracleComp.replicate (count n) (pair.sample n) >>=
        fun samples => extractWordLabels (count n) (outputBits n (choose n)) samples >>=
          test n (choose n))
      (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n) (outputBits n (choose n)) >>=
        test n (choose n))) := by
  let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
  have hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)) :=
    ExtractionSchedule.count_isPolyTime (isPolyTime_input unaryEncoding)
      realization.length_isPolyTime hslack
  have h := hpair.extract_indexed_labels realization choose
    (inverseSlack := inverseSlack)
    (fun n i => OracleComp.uniform (BitString (outputBits n i * count n)))
    (fun n i seed bits => LinearHash.hash (maskEquiv (outputBits n i) (count n) seed)
      (wordBits (count n) bits))
    (fun n i result => test n i (result.1, List.ofFn result.2.1, List.ofFn result.2.2))
    (extractedWordTest_isPPT (count := fun input : ℕ × ℕ => count input.1)
      (outputBits := fun input : ℕ × ℕ => outputBits input.1 input.2)
      (fun input : ℕ × ℕ => test input.1 input.2) htest
      (hcount.comp_encoded (isPolyTime_fst unaryEncoding unaryEncoding)) houtput)
    hcandidates hslack hnumerator hdensity hchoose hvalid
    (fun n i => by simpa only [OracleComp.uniform, ProbComp.eval_sample, wordBits_ofFn] using
      LinearHash.isTwoUniversal_flat (count n) (outputBits n i)) hbudget
  apply h.congr
  intro n
  have hpublic : ProbComp.eval ((fun value => pair.encode n value.1) <$>
      OracleComp.sample (pair.joint n)) = ProbComp.eval (Prod.fst <$> pair.sample n) := by
    simp only [ProbComp.eval_map, ProbComp.eval_sample, pair.eval_sample, PMF.map_comp,
      Function.comp_def]
  simp only [count, advantage, ProbComp.eval_bind, eval_extractWordLabels,
    eval_extractWordLabelsIdeal, PMF.bind_map, Function.comp_def, extractLabelsIdeal,
    ProbComp.eval_replicate_congr hpublic
      (ExtractionSchedule.count n (realization.length n) (inverseSlack n))]

open Filter in
/-- Computational label extraction as two ordinary word programs. The client supplies the
entropy budget and a certified test; matrix sampling, finite representations, and the uniform
prediction reduction are discharged by the library. -/
theorem SamplablePair.HasGap.extract_word_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization)
    {outputBits inverseSlack numerator densityBound : ℕ → ℕ}
    (houtput : IsPolyTime unaryEncoding (fun n => unaryEncoding (outputBits n)))
    (hslack : IsPolyTime unaryEncoding (fun n => unaryEncoding (inverseSlack n)))
    (hnumerator : IsPolyTime unaryEncoding (fun n => unaryEncoding (numerator n)))
    (hdensity : IsPolyTime unaryEncoding (fun n => unaryEncoding (densityBound n)))
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n + 2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ → List Word × Word × Word → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding unaryEncoding (pairEncoding (listEncoding wordEncoding)
      (pairEncoding wordEncoding wordEncoding))) boolEncoding (fun input => test input.1 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => advantage
      (OracleComp.replicate (count n) (pair.sample n) >>=
        fun samples => extractWordLabels (count n) (outputBits n) samples >>= test n)
      (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n) (outputBits n) >>=
        test n)) := by
  exact hpair.extract_indexed_word_labels realization (fun _ => 0)
    (candidates := fun _ => 1) (outputBits := fun n _ => outputBits n)
    (numerator := fun n _ => numerator n) (by polytime) (by polytime) hslack (by polytime)
    hdensity (Eventually.of_forall (by intro n; decide)) hvalid hbudget (fun n _ => test n) (by ppt)

end Cslib.Crypto.Pseudoentropy
