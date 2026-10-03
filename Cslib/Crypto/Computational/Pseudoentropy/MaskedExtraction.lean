/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Masking
public import Cslib.Probability.EntropyExtraction
public import Cslib.Crypto.Game.Statistical

/-!
# Extracting fresh masked labels

A dyadic mask gives a lower bound on every nonzero masked sample probability. The bound depends
on the source and mask precision, independently of the cost of computing the mask's votes.
Independent masked labels can therefore be extracted at almost their total soft density, while
revealing every observation and the complete hash seed.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 3.3, Lemma 2, and Section 5, Game 3.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  These bounds support our fresh soft-mask adaptation of the set-masking experiment. We retain
  the explicit concentration loss from the source mass and dyadic mask precision.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Cslib.Probability Cslib.Probability.PMF

/-- Hash the sampled labels, retaining every public observation and the independent hash seed. -/
def extractLabels {Observation Seed Output : Type} (seed : ProbComp Seed)
    (hash : Seed → Word → Output) (samples : List (Observation × Bool)) :
    ProbComp (List Observation × Seed × Output) := do
  let key ← seed
  return (samples.map Prod.fst, key, hash key (samples.map Prod.snd))

/-- Preserve the sampled observations and public seed, replacing the extracted labels by an
independent uniform output. The ambient observation and seed types need not be finite. -/
noncomputable def extractLabelsIdeal {Observation Seed Output : Type}
    [Fintype Output] [Nonempty Output] (source : ProbComp Observation) (count : ℕ)
    (seed : ProbComp Seed) : PMF (List Observation × Seed × Output) :=
  (ProbComp.eval (OracleComp.replicate count source)).bind (fun observed =>
    ((ProbComp.eval seed).bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map
      (observed, ·))

/-- Re-encoding the public observations commutes with extraction of the hidden labels. -/
theorem extractLabels_map_observation {α β Seed Output : Type} (observe : α → β)
    (seed : ProbComp Seed) (hash : Seed → Word → Output) (samples : List (α × Bool)) :
    extractLabels seed hash (samples.map (fun sample => (observe sample.1, sample.2))) =
      (fun result => (result.1.map observe, result.2)) <$> extractLabels seed hash samples := by
  simp only [extractLabels, map_bind, map_pure, List.map_map, Function.comp_def]

/-- The observation map also commutes with a complete repeated extraction experiment. -/
theorem eval_replicate_extractLabels_map {α β Seed Output : Type} (observe : α → β)
    (source : ProbComp (α × Bool)) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → Word → Output) :
    ProbComp.eval (OracleComp.replicate count
      ((fun sample => (observe sample.1, sample.2)) <$> source) >>= extractLabels seed hash) =
      (ProbComp.eval (OracleComp.replicate count source >>= extractLabels seed hash)).map
        (fun result => (result.1.map observe, result.2)) := by
  rw [OracleComp.replicate_map]
  simp only [bind_map_left, extractLabels_map_observation, ← map_bind, ProbComp.eval_map]

/-- Label extraction composes ordinary sampling, list projections, and an efficient hash. -/
theorem extractLabels_isPPT {Param Observation Seed Output : Type} {input : Param ↪ Word}
    {observation : Observation ↪ Word} {key : Seed ↪ Word} {output : Output ↪ Word}
    {seed : Param → ProbComp Seed} {hash : Param → Seed → Word → Output}
    {samples : Param → List (Observation × Bool)}
    (hseed : IsPPTOn input key seed)
    (hhash : IsPolyTime (pairEncoding (pairEncoding input key) wordEncoding)
      (fun pair => output (hash pair.1.1 pair.1.2 pair.2)))
    (hsamples : IsPolyTime input
      (fun a => listEncoding (pairEncoding observation boolEncoding) (samples a))) :
    IsPPTOn input (pairEncoding (listEncoding observation) (pairEncoding key output))
      (fun a => extractLabels (seed a) (hash a) (samples a)) := by
  unfold extractLabels
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptExtractLabels : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``extractLabels, ``extractLabels_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hseed => solve | aesop (rule_sets := [PPT, PolyTime])))

/-- Repeated program sampling and list-based extraction have the finite product experiment's
exact law. Only the representation of the observation tuple changes. -/
theorem eval_replicate_extractLabels {Observation Seed Output : Type} [Finite Observation]
    (source : ProbComp (Observation × Bool)) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → Word → Output) :
    ProbComp.eval (OracleComp.replicate count source >>= extractLabels seed hash) =
      ((PMF.pi (fun _ : Fin count => ProbComp.eval source)).bind (fun outcome =>
        (ProbComp.eval seed).map (fun s =>
          (fun i => (outcome i).1, s, hash s (List.ofFn (fun i => (outcome i).2)))))).map
        (fun result => (List.ofFn result.1, result.2)) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_replicate, PMF.bind_map, extractLabels,
    bind_pure_comp, ProbComp.eval_map, PMF.map_bind, PMF.map_comp, Function.comp_def, List.map_ofFn]

/-- Extraction error is the only loss when converting a distinguisher of extracted labels
into a distinguisher of the original and comparison sample sequences. The hash seed is public. -/
theorem extractLabels_sequence_gap {Observation Seed Output : Type}
    (original comparison : ProbComp (Observation × Bool)) (count : ℕ)
    (seed : ProbComp Seed) (hash : Seed → Word → Output)
    (test : List Observation × Seed × Output → ProbComp Bool)
    (ideal : PMF (List Observation × Seed × Output)) {ε : ℝ}
    (hclose : dist (ProbComp.eval (OracleComp.replicate count comparison >>=
      extractLabels seed hash)) ideal ≤ ε) :
    let reduced := fun samples => extractLabels seed hash samples >>= test
    Game.advantage (ProbComp.eval (OracleComp.replicate count original >>= reduced))
        (ideal.bind (fun output => ProbComp.eval (test output))) - ε ≤
      advantage (OracleComp.replicate count original >>= reduced)
        (OracleComp.replicate count comparison >>= reduced) := by
  dsimp only
  have hstat := (Game.advantage_bind_le_dist
    (ProbComp.eval (OracleComp.replicate count comparison >>= extractLabels seed hash)) ideal
    (fun output => ProbComp.eval (test output))).trans hclose
  have htriangle := Game.advantage_triangle
    (ProbComp.eval (OracleComp.replicate count original >>=
      fun samples => extractLabels seed hash samples >>= test))
    ((ProbComp.eval (OracleComp.replicate count comparison >>= extractLabels seed hash)).bind
      (fun output => ProbComp.eval (test output)))
    (ideal.bind (fun output => ProbComp.eval (test output)))
  have h := sub_le_iff_le_add.mpr (htriangle.trans (add_le_add le_rfl hstat))
  simpa only [advantage, ProbComp.eval_bind, PMF.bind_bind] using h

/-- The list-based extractor inherits the conditional Shannon-entropy bound for repeated
samples. Every observation and the independent hash seed are retained in the ideal experiment. -/
theorem extractLabels_distance_le {Observation Seed Output : Type} [Finite Observation]
    [Fintype Seed] [Fintype Output] [Nonempty Output]
    (source : ProbComp (Observation × Bool)) (count informationBits : ℕ)
    (hsource : ∀ pair ∈ (ProbComp.eval source).support,
      (2 : ℝ) ^ (-(informationBits : ℝ)) ≤ (ProbComp.eval source pair).toReal)
    (seed : ProbComp Seed) (hash : Seed → Word → Output)
    (hhash : IsTwoUniversal (ProbComp.eval seed)
      (fun s (bits : Fin count → Bool) => hash s (List.ofFn bits))) {δ slack : ℝ}
    (hentropy : δ ≤ conditionalEntropy (ProbComp.eval source)) (hslack : 0 ≤ slack) :
    dist (ProbComp.eval (OracleComp.replicate count source >>= extractLabels seed hash))
      ((ProbComp.eval (OracleComp.replicate count (Prod.fst <$> source))).bind (fun observed =>
        ((ProbComp.eval seed).bind (fun s =>
          (PMF.uniformOfFintype Output).map (s, ·))).map (observed, ·))) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * (informationBits : ℝ) ^ 2)) +
        Real.sqrt (Fintype.card Output * (2 * (2 : ℝ) ^ (-(count * δ - slack)))) / 2 := by
  have h := hhash.leftover_hash_pi_conditional (fun _ : Fin count => ProbComp.eval source)
    (bound := informationBits) (by positivity) (fun _ => hsource) hslack
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hmap := (dist_map_le _ _
    (fun result : (Fin count → Observation) × Seed × Output =>
      (List.ofFn result.1, result.2))).trans h
  simp only [eval_replicate_extractLabels, ProbComp.eval_replicate, ProbComp.eval_map,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def] at hmap ⊢
  refine hmap.trans ?_
  gcongr
  norm_num

/-- Fresh masking preserves the complete public marginal. -/
theorem maskedSample_map_fst {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) :
    (ProbComp.eval (maskedSample source observe truth mask)).map Prod.fst =
      (ProbComp.eval source).map observe := by
  simp only [eval_maskedSample, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (ProbComp.eval source).bind (fun value =>
    (ProbComp.eval (maskBit (mask value) (truth value))).map
      (Function.const Bool (observe value))) = _
  simp only [PMF.map_const]
  rfl

/-- A mask with positive acceptance probability at least `mass` assigns each possible label
probability at least `mass / 2`. Keeping the original label always has probability at least half. -/
theorem maskBit_mass_ge (mask : ProbComp Bool) (truth bit : Bool) {mass : ℝ}
    (hmass : mass ≤ 1)
    (hmask : 0 < (ProbComp.eval mask true).toReal → mass ≤ (ProbComp.eval mask true).toReal)
    (hbit : bit ∈ (ProbComp.eval (maskBit mask truth)).support) :
    mass / 2 ≤ (ProbComp.eval (maskBit mask truth) bit).toReal := by
  have hpositive : 0 < (ProbComp.eval (maskBit mask truth) bit).toReal :=
    ENNReal.toReal_pos ((ProbComp.eval _).apply_pos_iff _ |>.mpr hbit).ne'
      (PMF.apply_ne_top _ _)
  rw [eval_maskBit_apply] at hpositive ⊢
  split_ifs at hpositive ⊢ with heq
  · have hle := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
      (PMF.coe_le_one (ProbComp.eval mask) true)
    norm_num only [ENNReal.toReal_one] at hle
    linarith
  · have h := hmask (by linarith)
    linarith

/-- Revealing only an observation cannot decrease the contribution of any one source outcome.
The mask need not be determined by the observation or be independent of the true label. -/
theorem maskedSample_mass_ge {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool)
    {sourceMass maskMass : ℝ} (hmaskMass : maskMass ∈ Set.Icc 0 1)
    (hsource : ∀ value ∈ (ProbComp.eval source).support,
      sourceMass ≤ (ProbComp.eval source value).toReal)
    (hmask : ∀ value ∈ (ProbComp.eval source).support,
      0 < (ProbComp.eval (mask value) true).toReal →
        maskMass ≤ (ProbComp.eval (mask value) true).toReal)
    (pair : β × Bool) (hpair : pair ∈ (ProbComp.eval
      (maskedSample source observe truth mask)).support) :
    sourceMass * (maskMass / 2) ≤
      (ProbComp.eval (maskedSample source observe truth mask) pair).toReal := by
  rw [eval_maskedSample] at hpair ⊢
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hpair
  obtain ⟨value, hvalue, bit, hbit, rfl⟩ := hpair
  have hbitMass := maskBit_mass_ge (mask value) (truth value) bit hmaskMass.2
    (hmask value hvalue) hbit
  have hmap := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (le_map_apply (ProbComp.eval (maskBit (mask value) (truth value))) (observe value, ·) bit)
  have hbind := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (mul_le_bind_apply (ProbComp.eval source)
      (fun x => (ProbComp.eval (maskBit (mask x) (truth x))).map (observe x, ·))
      value (observe value, bit))
  rw [ENNReal.toReal_mul] at hbind
  exact (mul_le_mul (hsource value hvalue) (hbitMass.trans hmap)
    (div_nonneg hmaskMass.1 (by norm_num)) ENNReal.toReal_nonneg).trans hbind

/-- A dyadic lower bound on positive mask probabilities bounds the extra information carried
by a masked label, independently of how the mask was obtained. -/
theorem maskedSample_dyadic_mass_ge {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) (sourceBits bound : ℕ)
    (hsource : ∀ value ∈ (ProbComp.eval source).support,
      (2 : ℝ) ^ (-(sourceBits : ℝ)) ≤ (ProbComp.eval source value).toReal)
    (hmask : ∀ value ∈ (ProbComp.eval source).support, 0 < winProbability (mask value) →
      1 / (dyadicSize bound : ℝ) ≤ winProbability (mask value))
    (pair : β × Bool) (hpair : pair ∈ (ProbComp.eval
      (maskedSample source observe truth mask)).support) :
    (2 : ℝ) ^ (-((sourceBits + Nat.log 2 bound + 2 : ℕ) : ℝ)) ≤
      (ProbComp.eval (maskedSample source observe truth mask) pair).toReal := by
  have hdenominator : (0 : ℝ) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  have hdenominator_one : (1 : ℝ) ≤ dyadicSize bound := by
    exact_mod_cast Nat.succ_le_of_lt (dyadicSize_pos bound)
  have h := maskedSample_mass_ge source observe truth mask
    (sourceMass := (2 : ℝ) ^ (-(sourceBits : ℝ)))
    (maskMass := 1 / dyadicSize bound)
    ⟨by positivity, (div_le_iff₀ hdenominator).mpr (by simpa using hdenominator_one)⟩
    hsource hmask pair hpair
  have hpower : (2 : ℝ) ^ (-((sourceBits + Nat.log 2 bound + 2 : ℕ) : ℝ)) =
      (2 : ℝ) ^ (-(sourceBits : ℝ)) * ((1 / dyadicSize bound) / 2) := by
    simp only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, dyadicSize, pow_add]
    field_simp
    push_cast
    ring
  simpa only [hpower] using h

/-- A source with `sourceBits` bits of pointwise information gains at most `log₂ bound + 2`
bits from its dyadic mask and fresh label coin. The votes and threshold do not enter this bound. -/
theorem maskedSample_weight_mass_ge {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (votes : α → Word)
    (sourceBits bound numerator threshold : ℕ)
    (hsource : ∀ value ∈ (ProbComp.eval source).support,
      (2 : ℝ) ^ (-(sourceBits : ℝ)) ≤ (ProbComp.eval source value).toReal)
    (pair : β × Bool) (hpair : pair ∈ (ProbComp.eval (maskedSample source observe truth
      (fun value => Boosting.sampleWeight bound numerator threshold (votes value)
        (truth value)))).support) :
    (2 : ℝ) ^ (-((sourceBits + Nat.log 2 bound + 2 : ℕ) : ℝ)) ≤
      (ProbComp.eval (maskedSample source observe truth
        (fun value => Boosting.sampleWeight bound numerator threshold (votes value)
          (truth value))) pair).toReal :=
  maskedSample_dyadic_mass_ge source observe truth _ sourceBits bound hsource
    (fun _ _ => inv_dyadicSize_le_eval_sampleDyadicCoin bound _) pair hpair

/-- For every polynomial mask precision, eventually the extra information is at most `n + 2`
bits, simultaneously for every mask with the given pointwise bound. Only the starting index
depends on the polynomial's degree, so the extraction schedule can be fixed in advance. -/
theorem maskedSample_dyadic_mass_ge_eventually {α β : ℕ → Type}
    (source : ∀ n, ProbComp (α n)) (observe : ∀ n, α n → β n) (truth : ∀ n, α n → Bool)
    (sourceBits bound : ℕ → ℕ) (hbound : PolynomiallyBounded bound)
    (hsource : ∀ n value, value ∈ (ProbComp.eval (source n)).support →
      (2 : ℝ) ^ (-(sourceBits n : ℝ)) ≤ (ProbComp.eval (source n) value).toReal) :
    ∀ᶠ n in Filter.atTop, ∀ mask : α n → ProbComp Bool,
      (∀ value ∈ (ProbComp.eval (source n)).support, 0 < winProbability (mask value) →
        1 / (dyadicSize (bound n) : ℝ) ≤ winProbability (mask value)) →
      ∀ pair ∈ (ProbComp.eval (maskedSample (source n) (observe n) (truth n) mask)).support,
      (2 : ℝ) ^ (-((sourceBits n + n + 2 : ℕ) : ℝ)) ≤
        (ProbComp.eval (maskedSample (source n) (observe n) (truth n) mask) pair).toReal := by
  have hvanishes := negligible_polynomial_mul
    (negligible_geometric (ratio := (1 / 2 : ℝ)) (by norm_num)) (fun _ => by positivity) hbound 0
  simp only [pow_zero, one_mul] at hvanishes
  filter_upwards [hvanishes.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn
  have hpow : bound n ≤ 2 ^ n := by
    have hratio : (bound n : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
      simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hn
    exact_mod_cast (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).mp hratio
  have hlog : Nat.log 2 (bound n) ≤ n := by
    simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hpow
  intro mask hmask pair hpair
  refine le_trans ?_ (maskedSample_dyadic_mass_ge (source n) (observe n) (truth n) mask
    (sourceBits n) (bound n) (hsource n) hmask pair hpair)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hlog _) 2)

/-- The same eventual information bound holds uniformly over all executable vote masks. -/
theorem maskedSample_weight_mass_ge_eventually {α β : ℕ → Type}
    (source : ∀ n, ProbComp (α n)) (observe : ∀ n, α n → β n) (truth : ∀ n, α n → Bool)
    (sourceBits bound : ℕ → ℕ) (hbound : PolynomiallyBounded bound)
    (hsource : ∀ n value, value ∈ (ProbComp.eval (source n)).support →
      (2 : ℝ) ^ (-(sourceBits n : ℝ)) ≤ (ProbComp.eval (source n) value).toReal) :
    ∀ᶠ n in Filter.atTop, ∀ (votes : α n → Word) (numerator threshold : ℕ) (pair : β n × Bool),
      pair ∈ (ProbComp.eval (maskedSample (source n) (observe n) (truth n) (fun value =>
        Boosting.sampleWeight (bound n) numerator threshold (votes value)
          (truth n value)))).support →
      (2 : ℝ) ^ (-((sourceBits n + n + 2 : ℕ) : ℝ)) ≤
        (ProbComp.eval (maskedSample (source n) (observe n) (truth n) (fun value =>
          Boosting.sampleWeight (bound n) numerator threshold (votes value) (truth n value)))
            pair).toReal := by
  filter_upwards [maskedSample_dyadic_mass_ge_eventually source observe truth sourceBits bound
    hbound hsource] with n hn
  intro votes numerator threshold
  exact hn _ (fun _ _ => inv_dyadicSize_le_eval_sampleDyadicCoin (bound n) _)

/-- Any sufficiently dense mask can supply the repeated-label extractor. The source-information
premise concerns the finite latent draw; the public observation type may be infinite. -/
theorem maskedSample_extract {α β Seed Output : Type} [Finite α]
    [Fintype Seed] [Fintype Output] [Nonempty Output]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool)
    (count informationBits : ℕ)
    (hmass : ∀ pair ∈ (ProbComp.eval (maskedSample source id truth mask)).support,
      (2 : ℝ) ^ (-(informationBits : ℝ)) ≤
        (ProbComp.eval (maskedSample source id truth mask) pair).toReal)
    (seed : ProbComp Seed) (hash : Seed → Word → Output)
    (hhash : IsTwoUniversal (ProbComp.eval seed)
      (fun s (bits : Fin count → Bool) => hash s (List.ofFn bits))) {δ slack : ℝ}
    (hdensity : δ ≤ winProbability (source >>= mask)) (hslack : 0 ≤ slack) :
    dist (ProbComp.eval (OracleComp.replicate count (maskedSample source observe truth mask) >>=
        extractLabels seed hash))
      ((ProbComp.eval (OracleComp.replicate count (observe <$> source))).bind (fun observed =>
        ((ProbComp.eval seed).bind (fun s =>
          (PMF.uniformOfFintype Output).map (s, ·))).map (observed, ·))) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * (informationBits : ℝ) ^ 2)) +
        Real.sqrt (Fintype.card Output * (2 * (2 : ℝ) ^ (-(count * δ - slack)))) / 2 := by
  let := Fintype.ofFinite α
  have hentropy := maskedSample_entropy_ge source id truth mask
  rw [winProbability_bind] at hdensity
  have hfull := extractLabels_distance_le (maskedSample source id truth mask) count informationBits
    hmass seed hash hhash (hdensity.trans hentropy) hslack
  have hmap := (dist_map_le _ _
    (fun result : List α × Seed × Output => (result.1.map observe, result.2))).trans hfull
  rw [← eval_replicate_extractLabels_map observe] at hmap
  have hmasked : maskedSample source observe truth mask =
      (fun sample => (observe sample.1, sample.2)) <$> maskedSample source id truth mask := by
    simp only [maskedSample, map_bind, Functor.map_map, id_eq]
  rw [← hmasked] at hmap
  rw [OracleComp.replicate_map count source observe]
  simpa only [ProbComp.eval_replicate, ProbComp.eval_map, maskedSample_map_fst, PMF.map_id,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, List.map_ofFn] using hmap

/-- Independent masked labels contain at least the soft density per sample for extraction.
All observations and the hash seed remain public, and the masked and original public marginals
are identical. Observations may live in an infinite type, such as words: first reveal the finite
source draw, then forget it through `observe`. The error is uniform over every vote collection
and threshold of that density. -/
theorem maskedSample_weight_extract {α β Seed Output : Type} [Fintype α]
    [Fintype Seed] [Fintype Output] [Nonempty Output]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool) (votes : α → Word)
    (count sourceBits bound numerator threshold : ℕ)
    (hsource : ∀ value ∈ (ProbComp.eval source).support,
      (2 : ℝ) ^ (-(sourceBits : ℝ)) ≤ (ProbComp.eval source value).toReal)
    (seed : ProbComp Seed) (hash : Seed → Word → Output)
    (hhash : IsTwoUniversal (ProbComp.eval seed)
      (fun s (bits : Fin count → Bool) => hash s (List.ofFn bits))) {δ slack : ℝ}
    (hdensity : δ ≤ Boosting.density (ProbComp.eval source) (numerator / dyadicSize bound)
      (fun value => Boosting.voteMargin (votes value) (truth value) - threshold))
    (hslack : 0 ≤ slack) :
    dist (ProbComp.eval (OracleComp.replicate count
        (maskedSample source observe truth (fun value => Boosting.sampleWeight bound numerator
          threshold (votes value) (truth value))) >>= extractLabels seed hash))
      ((ProbComp.eval (OracleComp.replicate count (observe <$> source))).bind (fun observed =>
        ((ProbComp.eval seed).bind (fun s =>
          (PMF.uniformOfFintype Output).map (s, ·))).map (observed, ·))) ≤
      2 * Real.exp (-2 * slack ^ 2 / (count * (sourceBits + Nat.log 2 bound + 2 : ℕ) ^ 2)) +
        Real.sqrt (Fintype.card Output * (2 * (2 : ℝ) ^ (-(count * δ - slack)))) / 2 := by
  apply maskedSample_extract source observe truth _ count (sourceBits + Nat.log 2 bound + 2)
    (maskedSample_weight_mass_ge source id truth votes sourceBits bound numerator threshold hsource)
    seed hash hhash _ hslack
  simpa only [winProbability, Game.winProbability, ProbComp.eval_bind,
    Boosting.sampleWeight_density]
    using hdensity

end Cslib.Crypto.Pseudoentropy
