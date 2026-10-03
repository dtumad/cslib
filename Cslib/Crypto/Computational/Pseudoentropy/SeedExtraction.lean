/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.Seed

/-!
# Statistical extraction from a sampler's seed

The first component hashes public observations; the third hashes the original sampler seeds
while revealing every observation and label. Its conditional entropy is exactly the seed length
minus the two visible entropy terms. Both use the same repetition schedule as label extraction.
The program retains unused coins and never samples a conditional distribution. Zero output bits
remain valid even when a component has no entropy left.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the first and third extractors and Games 0--1.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use the shared seed-information concentration schedule.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization

open Probability Probability.PMF Filter

/-- Repeated public observations supply their Shannon entropy to the first extractor. -/
theorem observation_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Fintype (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (pair.Observation n) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        pair.Observation n) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    StatisticallyIndistinguishable
      (fun n => seededHash (ProbComp.eval (key n))
        (ProbComp.eval (OracleComp.replicate
          (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
            (OracleComp.sample ((pair.joint n).map Prod.fst)))) (hash n))
      (fun n => (ProbComp.eval (key n)).bind
        (fun k => (PMF.uniformOfFintype (BitString (outputBits n))).map (k, ·))) := by
  apply seededHash_replicate_statisticallyIndistinguishable
    (fun n => OracleComp.sample ((pair.joint n).map Prod.fst)) saved.length inverseSlack outputBits
    ?_ key hash hhash (by simpa only [ProbComp.eval_sample] using hbudget)
  intro n value hvalue
  simp only [ProbComp.eval_sample, ← saved.output_distribution, PMF.map_comp,
    Function.comp_def] at hvalue ⊢
  simpa [BitString, Real.logb_pow] using
    uniform_map_mass_ge (fun bits => (saved.output n bits).1) value hvalue

/-- The first statistical transition on ordinary sampled observation words. Its hash's finite
two-universality premise includes the public encoding; no observation is sampled conditionally. -/
theorem observation_word_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Fintype (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List Word → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        pair.Observation n) => hash n key ((List.ofFn values).map (pair.encode n))))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    StatisticallyIndistinguishable
      (fun n => seededHash (ProbComp.eval (key n))
        (ProbComp.eval (OracleComp.replicate
          (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
            (Prod.fst <$> pair.sample n))) (hash n))
      (fun n => (ProbComp.eval (key n)).bind
        (fun k => (PMF.uniformOfFintype (BitString (outputBits n))).map (k, ·))) := by
  have h := saved.observation_extraction inverseSlack outputBits key
    (fun n k values => hash n k (values.map (pair.encode n))) hhash hbudget
  apply h.congr
  intro n
  have hpublic : ProbComp.eval (Prod.fst <$> pair.sample n) =
      ProbComp.eval (pair.encode n <$> OracleComp.sample ((pair.joint n).map Prod.fst)) := by
    simp only [ProbComp.eval_map, ProbComp.eval_sample, pair.eval_sample, PMF.map_comp,
      Function.comp_def]
  dsimp only
  rw [ProbComp.eval_replicate_congr hpublic
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n))]
  simp only [seededHash_eq_bind, OracleComp.replicate_map, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def]

/-- Extract the unused seed entropy, preserving the complete pair output and hash seed.
The entropy chain rule pays for both the public observations and the labels already revealed. -/
theorem remainingSeed_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Fintype (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (BitString (saved.length n)) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        BitString (saved.length n)) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate
        (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
          (OracleComp.sample (saved.jointWithSeed n)) >>= extractLabels (key n) (hash n)))
      (fun n => extractLabelsIdeal (Output := BitString (outputBits n))
        (OracleComp.sample (pair.joint n))
          (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n)) := by
  have h := extractLabels_statisticallyIndistinguishable
    (fun n => OracleComp.sample (saved.jointWithSeed n)) saved.length inverseSlack outputBits
    (by simpa only [ProbComp.eval_sample] using saved.jointWithSeed_mass_ge) key hash hhash
    (by
      filter_upwards [hbudget] with n hn
      simpa only [ProbComp.eval_sample, show conditionalEntropy (saved.jointWithSeed n) =
        saved.length n - entropy ((pair.joint n).map Prod.fst) -
          conditionalEntropy (pair.joint n) by linarith [saved.entropy_chain_rule n]] using hn)
  apply h.congr
  intro n
  have hpublic : ProbComp.eval (Prod.fst <$> OracleComp.sample (saved.jointWithSeed n)) =
      ProbComp.eval (OracleComp.sample (pair.joint n)) := by
    simp only [ProbComp.eval_map, ProbComp.eval_sample, saved.jointWithSeed_map_fst]
  simp only [extractLabelsIdeal, ProbComp.eval_replicate_congr hpublic
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n))]

/-- The remaining-seed transition for the actual word sampler. Every observation and label
stays public; finite representations are confined to the two-universality hypothesis. -/
theorem remainingSeed_word_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Fintype (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List Word → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        BitString (saved.length n)) => hash n key ((List.ofFn values).map List.ofFn)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate
        (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
          (saved.sampleWithSeed n) >>= extractLabels (key n) (hash n)))
      (fun n => extractLabelsIdeal (Output := BitString (outputBits n)) (pair.sample n)
        (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n)) := by
  have h := (saved.remainingSeed_extraction inverseSlack outputBits key
    (fun n k values => hash n k (values.map List.ofFn)) hhash hbudget).map
      (fun n result => (result.1.map (fun value => (pair.encode n value.1, value.2)), result.2))
  apply h.congr
  intro n
  let observe := fun value : pair.Observation n × Bool => (pair.encode n value.1, value.2)
  have hsource : ProbComp.eval (saved.sampleWithSeed n) =
      ProbComp.eval ((fun result => (observe result.1, List.ofFn result.2)) <$>
        OracleComp.sample (saved.jointWithSeed n)) := by
    simpa only [ProbComp.eval_map, ProbComp.eval_sample] using saved.eval_sampleWithSeed n
  have hpublic : ProbComp.eval (observe <$> OracleComp.sample (pair.joint n)) =
      ProbComp.eval (pair.sample n) := by
    simp only [ProbComp.eval_map, ProbComp.eval_sample, pair.eval_sample, observe]
  have hreal := eval_replicate_extractLabels_map_pair observe List.ofFn
    (OracleComp.sample (saved.jointWithSeed n))
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n) (hash n)
  rw [ProbComp.eval_bind, ← ProbComp.eval_replicate_congr hsource] at hreal
  dsimp only
  simp only [observe] at hreal
  rw [← hreal, ← ProbComp.eval_bind]
  change dist _ ((extractLabelsIdeal (Output := BitString (outputBits n))
    (OracleComp.sample (pair.joint n))
      (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n)).map
        (fun result => (result.1.map observe, result.2))) = _
  rw [extractLabelsIdeal_map_observation]
  simp only [extractLabelsIdeal, ProbComp.eval_replicate_congr hpublic
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n))]

end Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization
