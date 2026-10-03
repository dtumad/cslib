/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.HashIsolation
public import Cslib.Crypto.Computational.Pseudoentropy.Basic
public import Cslib.Computability.Probabilistic.LinearHash
public import Cslib.Computability.Probabilistic.UniformNat

/-!
# The hashed parity pair

Reveal a function image, a random hash length, a public matrix, the corresponding hash prefix,
and an independent parity query. The hidden bit is the input's inner product with the query.

`joint` gives the finite joint distribution and `sample` is its word implementation. The entropy
bound and the strict PPT certificate are proved here. `pair` packages the sampler and its exact
finite law. `HashReduction` proves the finite prediction-to-inversion bound, `WordReduction`
implements that reduction, and `OneWay` derives the computational prediction gap.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 4, equations (4) and (5), and Lemma 3.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We use Boolean matrices in place of field multiplication. The executable sampler chooses the
  hash length exactly uniformly in a dyadic range, avoiding the sampling approximation in
  footnote 3. The entropy bound holds for any positive number of possible hash lengths.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.HashPair

open Cslib.Probability Cslib.Probability.PMF

/-- The number of possible hash lengths. Six extra lengths leave room for the truncation
threshold in the inversion proof; rounding up makes sampling exact with fair bits. -/
def hashCount (n : ℕ) : ℕ := dyadicSize (n + 6)

instance (n : ℕ) : NeZero (hashCount n) := inferInstanceAs (NeZero (dyadicSize (n + 6)))

/-- Every fiber's logarithmic size plus six lies inside the sampled hash range. -/
theorem hashCount_ge (n : ℕ) : n + 6 ≤ hashCount n := (lt_dyadicSize (n + 6)).le

/-- The enlarged hash range is still linear in the input length. -/
theorem hashCount_le (n : ℕ) : hashCount n ≤ 2 * (n + 7) := dyadicSize_le (n + 6)

/-- Sampling among the enlarged hash lengths requires only a polynomial range. -/
@[fun_prop] theorem hashCount_polynomiallyBounded : PolynomiallyBounded hashCount := by
  unfold hashCount
  fun_prop

/-- Compute the sampling range from an efficiently available unary parameter. -/
theorem hashCount_isPolyTime {α : Type} {encode : α ↪ Word} {parameter : α → ℕ}
    (hparameter : IsPolyTime encode (fun a => unaryEncoding (parameter a))) :
    IsPolyTime encode (fun a => unaryEncoding (hashCount (parameter a))) := by
  unfold hashCount
  apply IsPolyTime.dyadicSize
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] hashCount_isPolyTime

/-- A flat matrix seed and an independent parity query, both retained in the public output. -/
abbrev Seed (n count : ℕ) := BitString (count * n) × BitString n

/-- A public observation records the hash length and exactly that many hash bits. -/
abbrev Observation (n count : ℕ) (Image : Type*) :=
  Σ i : Fin count, Seed n count × Image × BitString (i.val + 1)

/-- Hash with the requested initial rows of the public matrix. -/
def prefixHash {n count : ℕ} (i : Fin count) (seed : Seed n count) (x : BitString n) :
    BitString (i.val + 1) :=
  LinearHash.hash (maskEquiv count n seed.1 ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt)) x

/-- The query can be included in the public seed without changing hash universality. -/
theorem prefixHash_isTwoUniversal {n count : ℕ} (i : Fin count) :
    IsTwoUniversal (PMF.uniformOfFintype (Seed n count)) (prefixHash i) := by
  unfold prefixHash
  refine IsTwoUniversal.precompose_seed _ Prod.fst (hash := fun matrix =>
    LinearHash.hash (maskEquiv count n matrix ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt))) ?_
  rw [PMF.uniformOfFintype_prod, map_fst_bind_pair]
  refine IsTwoUniversal.precompose_seed _ (maskEquiv count n) (hash := fun rows =>
    LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt))) ?_
  rw [uniformOfFintype_map_equiv]
  exact LinearHash.isTwoUniversal_prefix (Nat.succ_le_of_lt i.isLt)

/-- The public observation and hidden parity bit under independent uniform inputs. -/
noncomputable def joint {n count : ℕ} [NeZero count] {Image : Type*}
    (f : BitString n → Image) : PMF (Observation n count Image × Bool) :=
  (PMF.uniformOfFintype (Fin count)).bind (fun i =>
    (PMF.uniformOfFintype (Seed n count)).bind (fun seed =>
      (PMF.uniformOfFintype (BitString n)).map (fun x =>
        ((⟨i, (seed, f x, prefixHash i seed x)⟩ : Observation n count Image), x ⬝ᵥ seed.2))))

/-- Holenstein's entropy bound for the complete hashed parity experiment. No regularity,
injectivity, or computational hardness of the function is assumed. -/
theorem conditionalEntropy_joint_le {n count : ℕ} [NeZero count]
    {Image : Type*} [Finite Image] (f : BitString n → Image) :
    conditionalEntropy (joint (count := count) f) ≤
      ((∑ x, Real.logb 2 (Nat.card {y // f y = f x})) / (2 : ℝ) ^ n + 2) / count := by
  have h := conditionalEntropy_random_hash_le count
    (PMF.uniformOfFintype (Seed n count)) (PMF.uniformOfFintype (BitString n))
    f prefixHash prefixHash_isTwoUniversal (fun _ seed x => x ⬝ᵥ seed.2)
  simpa only [joint, PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_ofNat,
    ← Finset.mul_sum, ← div_eq_inv_mul, ← Finset.sum_div] using h

/-- Self-delimiting encoding of the five public fields. -/
def wordObservation (image : Word) (index : ℕ) (matrix digest query : Word) : Word :=
  pairEncoding wordEncoding (pairEncoding unaryEncoding
    (pairEncoding wordEncoding (pairEncoding wordEncoding wordEncoding)))
      (image, index, matrix, digest, query)

/-- Assemble the public fields using the ordinary tuple encoding. -/
theorem wordObservation_isPolyTime {α : Type} {encode : α ↪ Word}
    {image matrix digest query : α → Word} {index : α → ℕ}
    (himage : IsPolyTime encode image)
    (hindex : IsPolyTime encode (fun a => unaryEncoding (index a)))
    (hmatrix : IsPolyTime encode matrix) (hdigest : IsPolyTime encode digest)
    (hquery : IsPolyTime encode query) :
    IsPolyTime encode (fun a => wordObservation (image a) (index a)
      (matrix a) (digest a) (query a)) := by
  unfold wordObservation
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] wordObservation_isPolyTime

/-- Encode a finite public observation using the chosen image representation. -/
def encodeObservation {n count : ℕ} {Image : Type*} (encodeImage : Image → Word)
    (observation : Observation n count Image) : Word :=
  wordObservation (encodeImage observation.2.2.1) observation.1.val
    (List.ofFn observation.2.1.1) (List.ofFn observation.2.2.2)
    (List.ofFn observation.2.1.2)

/-- Encoding loses none of the public information, even though the digest's width varies. -/
theorem encodeObservation_injective {n count : ℕ} {Image : Type*}
    (encodeImage : Image ↪ Word) :
    Function.Injective (encodeObservation (n := n) (count := count) encodeImage) := by
  rintro ⟨i, ⟨matrix, query⟩, image, digest⟩ ⟨j, ⟨matrix', query'⟩, image', digest'⟩ h
  have hfields := (pairEncoding wordEncoding (pairEncoding unaryEncoding
    (pairEncoding wordEncoding (pairEncoding wordEncoding wordEncoding)))).injective h
  have hij : i = j := Fin.ext (congrArg (fun fields => fields.2.1) hfields)
  subst j
  simp only [Prod.mk.injEq, List.ofFn_inj] at hfields
  obtain ⟨himage, _, hmatrix, hdigest, hquery⟩ := hfields
  have himage := encodeImage.injective himage
  simp_all

/-- Sample the hashed parity pair using only fair bits and ordinary word operations. -/
noncomputable def sample (f : Word → Word) (n : ℕ) : ProbComp (Word × Bool) := do
  let index ← sampleDyadicIndex (n + 6)
  let matrix ← OracleComp.sampleBits (hashCount n * n)
  let query ← OracleComp.sampleBits n
  let input ← OracleComp.sampleBits n
  return (wordObservation (f input) index matrix
    (LinearHash.wordHash (index + 1) matrix input) query,
    (input.zipWith Bool.and query).foldl Bool.xor false)

/-- The construction is strict PPT whenever the given function is polynomial time. -/
theorem sample_isPPT (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPPTOn unaryEncoding (pairEncoding wordEncoding boolEncoding) (sample f) := by
  unfold sample hashCount
  apply IsPPTOn.bind_with
  · ppt
  apply IsPPTOn.bind_with
  · apply IsPolyTime.sampleBits
    apply IsPolyTime.unary_mul
    · apply IsPolyTime.dyadicSize
      polytime
    · polytime
  apply IsPPTOn.bind_with
  · ppt
  apply IsPPTOn.bind_with
  · ppt
  apply IsPolyTime.isPPTOn
  apply IsPolyTime.pair
  · apply wordObservation_isPolyTime
    · exact hf.comp_encoded (isPolyTime_snd _ _)
    · polytime
    · polytime
    · apply LinearHash.wordHash_isPolyTime <;> polytime
    · polytime
  · polytime

/-- The executable observation and hidden bit have exactly the finite joint distribution. -/
theorem eval_sample {n : ℕ} {Image : Type*} (f : Word → Word)
    (finiteFunction : BitString n → Image) (encodeImage : Image → Word)
    (hf : ∀ x, f (List.ofFn x) = encodeImage (finiteFunction x)) :
    ProbComp.eval (sample f n) =
      (joint (count := hashCount n) finiteFunction).map
        (fun pair => (encodeObservation encodeImage pair.1, pair.2)) := by
  have hhash (i : Fin (hashCount n)) (matrix : BitString (hashCount n * n))
      (x : BitString n) :
      LinearHash.wordHash (i.val + 1) (List.ofFn matrix) (List.ofFn x) =
        List.ofFn (prefixHash i (matrix, 0) x) := by
    rw [LinearHash.wordHash_eq_ofFn, masksFromWord_prefix (Nat.succ_le_of_lt i.isLt)]
    simp only [masksFromWord, wordBits_ofFn, prefixHash]
  have hindex : OracleComp.eval (fun q => q.elim) (sampleDyadicIndex (n + 6)) =
      (PMF.uniformOfFintype (Fin (hashCount n))).map Fin.val := eval_sampleDyadicIndex (n + 6)
  simp only [prefixHash] at hhash
  simp only [sample, ProbComp.eval, OracleComp.eval_bind, OracleComp.eval_pure,
    OracleComp.eval_sampleBits, hindex,
    joint, PMF.uniformOfFintype_prod, PMF.bind_map, PMF.map_bind,
    PMF.bind_bind, PMF.map_comp, Function.comp_def, uniformBits]
  simp only [Function.comp_def, hf, hhash, encodeObservation, prefixHash,
    dotProduct_eq_foldl, PMF.map, Function.comp_def]

/-- Package the efficient sampler with its finite observation type and exact joint law.
The image representation is needed for entropy bookkeeping, not as an extra algorithmic oracle. -/
noncomputable def pair {Image : ℕ → Type} [∀ n, Finite (Image n)]
    (f : Word → Word) (hf : IsPolyTime wordEncoding f)
    (finiteFunction : ∀ n, BitString n → Image n) (encodeImage : ∀ n, Image n ↪ Word)
    (hencode : ∀ n x, f (List.ofFn x) = encodeImage n (finiteFunction n x)) : SamplablePair where
  Observation n := Observation n (hashCount n) (Image n)
  encode n := ⟨encodeObservation (encodeImage n), encodeObservation_injective (encodeImage n)⟩
  joint n := joint (finiteFunction n)
  sample := sample f
  efficient := sample_isPPT f hf
  eval_sample n := eval_sample f (finiteFunction n) (encodeImage n) (hencode n)

end Cslib.Crypto.Pseudoentropy.HashPair
