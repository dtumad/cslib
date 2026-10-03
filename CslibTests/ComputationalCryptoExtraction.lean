/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Extraction
public import Cslib.Crypto.Computational.Pseudoentropy.Seed
public import Cslib.Crypto.Computational.Pseudoentropy.MaskedExtraction

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

/-- A hidden-label-dependent mask still supplies half a bit per sample for extraction. The
public observation is constant; one original label is masked and the other is retained. -/
theorem extraction_with_hidden_label_mask (count outputBits : ℕ) {slack : ℝ}
    (hslack : 0 ≤ slack) :
    let seed := OracleComp.uniform (Fin outputBits → BitString count)
    let source := Pseudoentropy.maskedSample (OracleComp.uniform Bool) (fun _ => ()) id
      (fun bit => Pseudoentropy.Boosting.sampleWeight 0 2 0 [true] bit)
    dist (ProbComp.eval (OracleComp.replicate count source >>=
        Pseudoentropy.extractLabels seed
          (fun rows bits => LinearHash.hash rows (wordBits count bits))))
      ((ProbComp.eval seed).bind (fun rows => (PMF.uniformOfFintype (BitString outputBits)).map
        (fun bits => (List.replicate count (), rows, bits)))) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * 9)) +
        Real.sqrt ((2 : ℝ) ^ outputBits * (2 * (2 : ℝ) ^ (-(count / 2 - slack)))) / 2 := by
  dsimp only
  have h := Pseudoentropy.maskedSample_weight_extract (OracleComp.uniform Bool)
    (fun _ => ()) id (fun _ => [true]) count 1 0 2 0
    (by intro bit _; norm_num [OracleComp.uniform, PMF.uniformOfFintype_apply])
    (OracleComp.uniform (Fin outputBits → BitString count))
    (fun rows bits => LinearHash.hash rows (wordBits count bits))
    (by simpa [OracleComp.uniform] using LinearHash.isTwoUniversal count outputBits)
    (δ := 1 / 2)
    (by norm_num [Pseudoentropy.Boosting.density, OracleComp.uniform,
        PMF.uniformOfFintype_apply, Fintype.sum_bool, Pseudoentropy.Boosting.voteMargin,
        Pseudoentropy.Boosting.weight, dyadicSize]) hslack
  have hpublic : ProbComp.eval (OracleComp.replicate count
      ((fun _ : Bool => ()) <$> OracleComp.uniform Bool)) = PMF.pure (List.replicate count ()) := by
    rw [ProbComp.eval_replicate]
    have hconstant : (List.ofFn : (Fin count → Unit) → List Unit) =
        Function.const _ (List.replicate count ()) := by
      funext values
      rw [show values = fun _ => () from Subsingleton.elim _ _, List.ofFn_const]
      rfl
    rw [hconstant, PMF.map_const]
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
