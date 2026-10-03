/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Extraction
public import Cslib.Crypto.Computational.Pseudoentropy.WordExtraction
public import Cslib.Crypto.Computational.Pseudoentropy.WordSeedExtraction

/-!
# Extraction and entropy examples

The examples check the matrix representation, malformed tapes, public-seed security, and a
client reduction from computational indistinguishability through extraction. They do not assert
the existence of a one-way function or a proof of the general OWF-to-PRG theorem.
-/

public section

namespace CslibTests.ComputationalCryptoExtraction

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto

/-- A row-major identity matrix preserves a two-bit input. -/
example : LinearHash.wordHash 2 [true, false, false, true] [true, false] = [true, false] := by
  decide +kernel

/-- Missing matrix entries are zero, as in the shared word-to-matrix representation. -/
example : LinearHash.wordHash 2 [true] [true, false] = [true, false] := by
  decide +kernel

/-- An empty source has no dot-product entropy, regardless of the supplied seed. -/
example : LinearHash.wordHash 3 [true, true] [] = [false, false, false] := by
  decide +kernel

/-- Runtime matrix dimensions, captured words, and sampling compose without machine internals. -/
example : IsPPT wordEncoding
    (fun n input => LinearHash.extract ((n + 1) ^ 2) input) := by
  ppt

/-- An output constant across distinct inputs fails the two-universality requirement. -/
example : ¬ IsTwoUniversal (PMF.uniformOfFintype Unit) (fun _ (_ : Bool) => false) := by
  intro h
  have hbad := h false true (by decide)
  norm_num [PMF.uniformOfFintype_apply] at hbad

/-- A deterministic source can have a uniform hash value when the seed is hidden. -/
example : (seededHash (PMF.uniformOfFintype Bool) (PMF.pure true)
    (fun seed input => seed && input)).map Prod.snd = PMF.uniformOfFintype Bool := by
  simp [seededHash, PMF.map, Function.comp_def]

/-- Revealing the seed exposes the correlation: the same experiment has distance one half. -/
example : dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pure true)
    (fun seed input => seed && input)) (PMF.uniformOfFintype (Bool × Bool)) = 1 / 2 := by
  norm_num [seededHash, dist_eq, Fintype.sum_prod_type, Fintype.sum_bool, PMF.map,
    PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFintype_apply, tsum_fintype]

/-- Conditioning a fair bit on one outcome discards exactly half its probability. -/
theorem conditioning_fair_bit_distance :
    dist (PMF.uniformOfFintype Bool)
      ((PMF.uniformOfFintype Bool).filter {true}
        ⟨true, rfl, PMF.mem_support_uniformOfFintype true⟩) = 1 / 2 := by
  rw [dist_filter, toOuterMeasure_apply_toReal]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]

/-- The public flag reveals the entire source on one branch; otherwise four bits remain uniform. -/
noncomputable def sourceWithLeakage (revealed : Bool) : PMF (BitString 4) :=
  if revealed then PMF.pure 0 else PMF.uniformOfFintype (BitString 4)

/-- One of sixteen equally likely choices activates the leakage branch. -/
noncomputable def rareLeakageFlag : PMF Bool :=
  (PMF.uniformOfFintype (Fin 16)).map (fun index => index == 0)

/-- A rare fully leaked branch still permits a nontrivial extraction bound. This uses its
probability `1/16`, rather than imposing a worst-case entropy bound on every public branch. -/
theorem extraction_with_rare_leakage :
    let side := rareLeakageFlag
    let seed := PMF.uniformOfFintype (Fin 1 → BitString 4)
    dist (side.bind (fun info => (seededHash seed (sourceWithLeakage info)
        LinearHash.hash).map (info, ·)))
      (side.bind (fun info => (seed.bind
        (fun rows => (PMF.uniformOfFintype (BitString 1)).map (rows, ·))).map (info, ·))) ≤
          3 / 8 := by
  dsimp only
  have h := (LinearHash.isTwoUniversal 4 1).leftover_hash_conditional_of_heavy_probability
    rareLeakageFlag sourceWithLeakage
      (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  have huniform : (PMF.uniformOfFintype (BitString 4)).toOuterMeasure
      {x | (1 / 16 : ℝ) < ((PMF.uniformOfFintype (BitString 4)) x).toReal} = 0 := by
    simp [PMF.uniformOfFintype_apply, BitString]
  have hpure : ((PMF.pure 0 : PMF (BitString 4)).toOuterMeasure
      {x | (1 / 16 : ℝ) < ((PMF.pure 0 : PMF (BitString 4)) x).toReal}) = 1 := by
    rw [PMF.toOuterMeasure_pure_apply]
    norm_num
  simp only [Fintype.sum_bool, sourceWithLeakage, Bool.false_eq_true, ↓reduceIte,
    huniform, hpure] at h
  have hsqrt : Real.sqrt 4 = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
    norm_num
  norm_num [rareLeakageFlag, sourceWithLeakage, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype, Fin.sum_univ_succ, BitString, hsqrt] at h ⊢
  exact h

/-- A client can extract from repetitions of any PPT pair using only its saved-seed interface.
The proof combines the uniform matrix hash with the generic conditional extraction theorem. -/
theorem repeated_pair_extraction (pair : Pseudoentropy.SamplablePair)
    (saved : pair.SeedRealization) (n repetitions outputBits : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    let seed := PMF.uniformOfFintype (Fin outputBits → BitString repetitions)
    dist ((PMF.pi (fun _ : Fin repetitions => pair.joint n)).bind (fun outcomes => seed.map
        (fun rows => (fun i => (outcomes i).1, rows,
          LinearHash.hash rows (fun i => (outcomes i).2)))))
      ((PMF.pi (fun _ : Fin repetitions => (pair.joint n).map Prod.fst)).bind
        (fun observed => (seed.bind
          (fun rows => (PMF.uniformOfFintype (BitString outputBits)).map (rows, ·))).map
            (observed, ·))) ≤
      2 * Real.exp (-2 * ε ^ 2 / (repetitions * (saved.length n : ℝ) ^ 2)) +
        Real.sqrt ((2 : ℝ) ^ outputBits *
          (2 * (2 : ℝ) ^ (-(repetitions * conditionalEntropy (pair.joint n) - ε)))) / 2 := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    BitString, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] using
      (LinearHash.isTwoUniversal repetitions outputBits).leftover_hash_pi_conditional
        (fun _ : Fin repetitions => pair.joint n) (Nat.cast_nonneg (saved.length n))
          (fun _ => saved.mass_ge n) hε

/-- Repeated labeled samples can be hashed while retaining their observations and the complete
matrix seed. The source and output dimensions may depend on the security parameter. -/
noncomputable def extractTraining (source : ℕ → ProbComp (Word × Bool)) (n : ℕ) :
    ProbComp (List Word × Word × Word) := do
  let samples ← OracleComp.replicate ((n + 1) ^ 3) (source n)
  Pseudoentropy.extractLabels (OracleComp.sampleBits ((n + 1) * samples.length))
    (LinearHash.wordHash (n + 1)) samples

/-- The complete sampling and extraction pipeline has a synthesized strict PPT certificate. -/
theorem extractTraining_isPPT {source : ℕ → ProbComp (Word × Bool)}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source) :
    IsPPTOn unaryEncoding (pairEncoding (listEncoding wordEncoding)
      (pairEncoding wordEncoding wordEncoding)) (extractTraining source) := by
  unfold extractTraining
  ppt

/-- The security theorem's repetition schedule composes with an arbitrary certified sampler.
Both the source-seed bound and the output dimension may depend on the security parameter. -/
example {source : ℕ → ProbComp (Word × Bool)} {sourceBits : ℕ → ℕ}
    (hsource : IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) source)
    (hbits : IsPolyTime unaryEncoding (fun n => unaryEncoding (sourceBits n))) :
    IsPPTOn unaryEncoding (pairEncoding (listEncoding wordEncoding)
      (pairEncoding wordEncoding wordEncoding)) (fun n => do
        let count := Pseudoentropy.ExtractionSchedule.count n (sourceBits n) 3
        let samples ← OracleComp.replicate count (source n)
        Pseudoentropy.extractWordLabels count n samples) := by
  have hcount : IsPolyTime unaryEncoding
      (fun n => unaryEncoding (Pseudoentropy.ExtractionSchedule.count n (sourceBits n) 3)) := by
    apply Pseudoentropy.ExtractionSchedule.count_isPolyTime <;> polytime
  ppt

open Filter Pseudoentropy in
/-- A common numerical budget used by the positive-entropy examples below. -/
private theorem halfBitBudget (n sourceBits : ℕ) :
    (n : ℝ) + 2 * (ExtractionSchedule.slack n sourceBits 3 : ℝ) ≤
      ExtractionSchedule.count n sourceBits 3 * (1 / 2 : ℝ) := by
  have hinformation : (1 : ℝ) ≤ ((sourceBits : ℝ) + n + 2) ^ 2 := by
    have h : 1 ≤ (sourceBits + n + 2) ^ 2 := Nat.succ_le_of_lt (by positivity)
    exact_mod_cast h
  norm_num [ExtractionSchedule.count, ExtractionSchedule.slack]
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sub_nonneg.mpr hinformation)]

open Filter Pseudoentropy in
/-- A known half-bit pseudoentropy threshold suffices to extract `n` computationally uniform
labels. The test sees every observation and every matrix-seed bit. The proof discharges the
repetition and slack budget using the stated half-bit threshold. -/
theorem label_extraction_half {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    (hentropy : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ conditionalEntropy (pair.joint n) + gap n)
    (test : ℕ → List Word × Word × Word → ProbComp Bool)
    (htest : IsPPTOn (pairEncoding unaryEncoding (pairEncoding (listEncoding wordEncoding)
      (pairEncoding wordEncoding wordEncoding))) boolEncoding (fun input => test input.1 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) 3
    Negligible (fun n => advantage
      (OracleComp.replicate (count n) (pair.sample n) >>=
        fun samples => extractWordLabels (count n) n samples >>= test n)
      (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n) n >>= test n)) := by
  apply hpair.extract_word_labels saved (outputBits := id) (inverseSlack := fun _ => 3)
    (numerator := fun _ => 1) (densityBound := fun _ => 1)
    (by polytime) (by polytime) (by polytime) (by polytime) ?_ ?_ test htest
  · filter_upwards [hentropy] with n hn
    norm_num [dyadicSize, hn]
  · apply Filter.Eventually.of_forall
    intro n
    simpa [dyadicSize] using halfBitBudget n (saved.length n)

open Filter Pseudoentropy in
/-- The first extractor obtains its padding bound from PPT and uses it in the actual program.
A half-bit entropy assumption yields `n` uniform digest bits with the full matrix seed public. -/
theorem observation_extraction_half {pair : SamplablePair} (saved : pair.SeedRealization)
    (hentropy : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ entropy ((pair.joint n).map Prod.fst)) :
    ∃ bound : ℕ → ℕ, IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n)) ∧
      let count := fun n => ExtractionSchedule.count n (saved.length n) 3
      StatisticallyIndistinguishable
        (fun n => ProbComp.eval (OracleComp.replicate (count n) (Prod.fst <$> pair.sample n) >>=
          extractWordObservations (bound n) n))
        (fun n => uniformBits (n * (count n * (2 * bound n + 1)) + n)) := by
  obtain ⟨bound, hefficient, hbound⟩ := pair.exists_observationBound
  refine ⟨bound, hefficient, saved.extract_word_observations bound (fun _ => 3) id hbound ?_⟩
  filter_upwards [hentropy] with n hn
  exact Or.inr ((halfBitBudget n (saved.length n)).trans
    (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)))

open Filter Pseudoentropy in
/-- The third extractor's concrete hash releases `n` uniform bits below its residual-entropy
budget, preserving all original pair outputs and the complete matrix seed. -/
theorem remaining_seed_extraction_half {pair : SamplablePair} (saved : pair.SeedRealization)
    (hentropy : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ saved.length n -
      entropy ((pair.joint n).map Prod.fst) - conditionalEntropy (pair.joint n)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) 3
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (saved.sampleWithSeed n) >>=
        extractWordSeeds (count n) (saved.length n) n))
      (fun n => ProbComp.eval (extractMatrixLabelsIdeal (pair.sample n) (count n)
        (count n * saved.length n) n)) := by
  apply saved.extract_word_seeds (fun _ => 3) id
  filter_upwards [hentropy] with n hn
  exact Or.inr ((halfBitBudget n (saved.length n)).trans
    (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)))

open Pseudoentropy in
/-- One client samples once and extracts all three components using the ordinary program API. -/
noncomputable def threeExtractedComponents {pair : SamplablePair}
    (saved : pair.SeedRealization) (bound : ℕ → ℕ) (n : ℕ) : ProbComp Word := do
  let count := ExtractionSchedule.count n (saved.length n) 3
  let samples ← OracleComp.replicate count (saved.sampleWithSeed n)
  let third ← extractWordSeeds count (saved.length n) n samples
  let middle ← extractWordLabels count n third.1
  let first ← extractWordObservations (bound n) n middle.1
  return first ++ middle.2.1 ++ middle.2.2 ++ third.2.1 ++ third.2.2

/-- The combined client proof exposes only its sampler and size certificates. This is an
efficiency test; security of the combined construction requires the three game transitions. -/
theorem threeExtractedComponents_isPPT {pair : Pseudoentropy.SamplablePair}
    (saved : pair.SeedRealization) {bound : ℕ → ℕ}
    (hbound : IsPolyTime unaryEncoding (fun n => unaryEncoding (bound n))) :
    IsPPTOn unaryEncoding wordEncoding (threeExtractedComponents saved bound) := by
  have hsource := saved.sampleWithSeed_isPPT
  have hlength := saved.length_isPolyTime
  have hcount : IsPolyTime unaryEncoding (fun n =>
      unaryEncoding (Pseudoentropy.ExtractionSchedule.count n (saved.length n) 3)) := by
    apply Pseudoentropy.ExtractionSchedule.count_isPolyTime <;> polytime
  unfold threeExtractedComponents
  ppt

/-- A client hashes retained word seeds while exposing every sampled observation and label. -/
noncomputable def extractRetainedSeeds {pair : Pseudoentropy.SamplablePair}
    (saved : pair.SeedRealization) (n : ℕ) : ProbComp (List (Word × Bool) × Word × Word) := do
  let samples ← OracleComp.replicate (n + 1) (saved.sampleWithSeed n)
  Pseudoentropy.extractLabels (OracleComp.sampleBits (n * ((n + 1) * saved.length n)))
    (fun key seeds => LinearHash.wordHash n key seeds.flatten) samples

/-- The same extractor tactic handles word labels, captured dimensions, and retained coins. -/
theorem extractRetainedSeeds_isPPT {pair : Pseudoentropy.SamplablePair}
    (saved : pair.SeedRealization) :
    IsPPTOn unaryEncoding
      (pairEncoding (listEncoding (pairEncoding wordEncoding boolEncoding))
        (pairEncoding wordEncoding wordEncoding)) (extractRetainedSeeds saved) := by
  have hsource := saved.sampleWithSeed_isPPT
  have hlength := saved.length_isPolyTime
  unfold extractRetainedSeeds
  ppt

open Pseudoentropy in
/-- An empty third component is valid for every sampler, even if its remaining entropy is
zero. The comparison experiment still retains all pair outputs and a public fair seed bit. -/
theorem empty_remaining_component {pair : SamplablePair} (saved : pair.SeedRealization) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) 0
    StatisticallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (saved.sampleWithSeed n) >>=
        extractLabels (OracleComp.uniform Bool) (fun _ _ => (Fin.elim0 : BitString 0))))
      (fun n => extractLabelsIdeal (Output := BitString 0) (pair.sample n) (count n)
        (OracleComp.uniform Bool)) := by
  apply saved.remainingSeed_word_extraction (fun _ => 0) (fun _ => 0)
    (fun _ => OracleComp.uniform Bool) (fun _ _ _ => Fin.elim0)
  · intro n first second _
    norm_num [BitString, OracleComp.uniform, PMF.uniformOfFintype_apply]
  · exact Filter.Eventually.of_forall (fun _ => Or.inl rfl)

/-- A hidden-label-dependent mask still supplies half a bit per sample for extraction. The
public observation is an empty word; one original label is masked and the other is retained.
The observation type is infinite, even though the underlying source has just two outcomes. -/
theorem extraction_with_hidden_label_mask (count outputBits : ℕ) {slack : ℝ}
    (hslack : 0 ≤ slack) :
    let seed := OracleComp.uniform (Fin outputBits → BitString count)
    let source := Pseudoentropy.maskedSample (OracleComp.uniform Bool) (fun _ => ([] : Word)) id
      (fun bit => Pseudoentropy.Boosting.sampleWeight 0 2 0 [true] bit)
    dist (ProbComp.eval (OracleComp.replicate count source >>=
        Pseudoentropy.extractLabels seed
          (fun rows bits => LinearHash.hash rows (wordBits count bits))))
      ((ProbComp.eval seed).bind (fun rows => (PMF.uniformOfFintype (BitString outputBits)).map
        (fun bits => (List.replicate count ([] : Word), rows, bits)))) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * 9)) +
        Real.sqrt ((2 : ℝ) ^ outputBits * (2 * (2 : ℝ) ^ (-(count / 2 - slack)))) / 2 := by
  dsimp only
  have h := Pseudoentropy.maskedSample_weight_extract (OracleComp.uniform Bool)
    (fun _ => ([] : Word)) id (fun _ => [true]) count 1 0 2 0
    (by intro bit _; norm_num [OracleComp.uniform, PMF.uniformOfFintype_apply])
    (OracleComp.uniform (Fin outputBits → BitString count))
    (fun rows bits => LinearHash.hash rows (wordBits count bits))
    (by simpa [OracleComp.uniform] using LinearHash.isTwoUniversal count outputBits)
    (δ := 1 / 2)
    (by norm_num [Pseudoentropy.Boosting.density, OracleComp.uniform,
        PMF.uniformOfFintype_apply, Fintype.sum_bool, Pseudoentropy.Boosting.voteMargin,
        Pseudoentropy.Boosting.weight, dyadicSize]) hslack
  have hpublic : ProbComp.eval (OracleComp.replicate count
      ((fun _ : Bool => ([] : Word)) <$> OracleComp.uniform Bool)) =
        PMF.pure (List.replicate count ([] : Word)) := by
    rw [OracleComp.replicate_map, ProbComp.eval_map, ProbComp.eval_replicate, PMF.map_comp]
    have hconstant : (fun values : Fin count → Bool =>
        (List.ofFn values).map (fun _ => ([] : Word))) =
        Function.const _ (List.replicate count ([] : Word)) := by
      funext values
      rw [List.map_ofFn]
      change List.ofFn (fun _ : Fin count => ([] : Word)) = List.replicate count []
      rw [List.ofFn_const]
    simpa only [Function.comp_def, hconstant] using
      (PMF.map_const (pi (fun _ : Fin count => ProbComp.eval (OracleComp.uniform Bool)))
        (List.replicate count ([] : Word)))
  rw [hpublic, PMF.pure_bind] at h
  norm_num only [Nat.log_zero_right, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at h
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, id_eq, BitString,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    mul_one_div] using h

/-- A complete client reduction: extract `n` bits from a source indistinguishable from `2n`
uniform bits. The `2n²`-bit seed is retained, so the ideal output has length `2n² + n`. -/
theorem extract_uniform_source {X : ℕ → PMF Word}
    (h : ComputationallyIndistinguishable X (fun n => uniformBits (2 * n))) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun input => ProbComp.eval (LinearHash.extract n input)))
      (fun n => uniformBits (n * (2 * n) + n)) := by
  apply h.extract_uniform (source := fun n => PMF.uniformOfFintype (BitString (2 * n)))
    (fun n => n) (by polytime)
  have hgeometric : Negligible (fun n => (1 / 2 : ℝ) ^ n) :=
    negligible_geometric (by norm_num)
  convert hgeometric using 1
  funext n
  simp only [collisionProbability_uniform, BitString, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, pow_mul, one_div, inv_pow]
  ring_nf
  norm_num [← mul_pow]

end CslibTests.ComputationalCryptoExtraction
