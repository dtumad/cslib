/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.BitString
public import Cslib.Tactic.PolyTime
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul

/-!
# Bitstrings and word programs

Shared word representations, Boolean dot products, and row-major matrix parsing for cryptographic
algorithms. A flat uniform bit tape gives exactly independent uniform rows. Efficiency certificates
use the ordinary word and collection combinators, including on malformed or short input tapes.

These operations were factored out of the Goldreich–Levin decoder so that decoding and universal
hashing share their representations, sampling laws, and polynomial-time proofs.
-/

@[expose] public section

namespace Cslib.Probability

/-- Pad a self-delimiting word to `2 * bound + 1` bits when its length is at most `bound`.
Words outside the bound remain distinguishable, rather than being truncated. -/
def padWord (bound : ℕ) (word : Word) : Word :=
  pairEncoding wordEncoding wordEncoding
    (word, List.replicate (2 * (bound - word.length)) false)

/-- Padding never identifies distinct words, even when their bounds differ. -/
theorem word_eq_of_padWord_eq {bound bound' : ℕ} {word word' : Word}
    (h : padWord bound word = padWord bound' word') : word = word' :=
  congrArg Prod.fst ((pairEncoding wordEncoding wordEncoding).injective h)

/-- Every word within the supplied bound has the same padded length. -/
theorem length_padWord {bound : ℕ} {word : Word} (h : word.length ≤ bound) :
    (padWord bound word).length = 2 * bound + 1 := by
  simp only [padWord, length_pairEncoding, wordEncoding, Function.Embedding.refl_apply,
    List.length_replicate]
  lia

/-- Self-delimiting padding uses the shared word encoder and unary arithmetic. -/
theorem padWord_isPolyTime {α : Type} {encode : α ↪ Word}
    {bound : α → ℕ} {word : α → Word}
    (hbound : IsPolyTime encode (fun a => unaryEncoding (bound a)))
    (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => padWord (bound a) (word a)) := by
  unfold padWord
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] padWord_isPolyTime

/-- View a word as `n` coordinates, using false for missing bits. Valid lengths lose no data. -/
def wordBits (n : ℕ) (word : Word) : BitString n := fun i => word[i.val]?.getD false

/-- A finite bitstring survives the word representation unchanged. -/
@[simp] theorem wordBits_ofFn {n : ℕ} (bits : BitString n) :
    wordBits n (List.ofFn bits) = bits := by
  funext i
  simp [wordBits]

/-- A correctly sized word survives the finite-coordinate representation unchanged. -/
theorem ofFn_wordBits {n : ℕ} {word : Word} (hlen : word.length = n) :
    List.ofFn (wordBits n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits, List.getElem?_eq_getElem hi']

/-- Padding embeds bounded words into a fixed finite bitstring space. -/
theorem word_eq_of_paddedBits_eq {bound : ℕ} {left right : Word}
    (hleft : left.length ≤ bound) (hright : right.length ≤ bound)
    (h : wordBits (2 * bound + 1) (padWord bound left) =
      wordBits (2 * bound + 1) (padWord bound right)) : left = right := by
  apply word_eq_of_padWord_eq
  simpa only [ofFn_wordBits (length_padWord hleft), ofFn_wordBits (length_padWord hright)] using
    congrArg List.ofFn h

/-- The fixed-width representation reads a bounded range of indices, padding missing bits. -/
theorem ofFn_wordBits_eq_range (n : ℕ) (word : Word) :
    List.ofFn (wordBits n word) = (List.range n).map (fun i => word[i]?.getD false) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits]

/-- Truncating or padding a word to a supplied unary width is uniformly polynomial time. -/
theorem wordBits_isPolyTime {α : Type} {input : α ↪ Word} {n : α → ℕ} {word : α → Word}
    (hn : IsPolyTime input (fun a => unaryEncoding (n a))) (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => List.ofFn (wordBits (n a) (word a))) := by
  simp_rw [ofFn_wordBits_eq_range]
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] wordBits_isPolyTime

/-- The row-major bijection between a flat bitstring and a matrix of masks. -/
def maskEquiv (k n : ℕ) : BitString (k * n) ≃ (Fin k → BitString n) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin k) (Fin n) Bool)

/-- Packing fixed-width rows is ordinary list concatenation. -/
theorem ofFn_maskEquiv_symm {count width : ℕ} (rows : Fin count → BitString width) :
    List.ofFn ((maskEquiv count width).symm rows) =
      (List.ofFn (fun i => List.ofFn (rows i))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h := congrArg (fun values => values i j) ((maskEquiv count width).apply_symm_apply rows)
  change (maskEquiv count width).symm rows (finProdFinEquiv (i, j)) = rows i j at h
  convert h using 1
  apply congrArg ((maskEquiv count width).symm rows)
  apply Fin.ext
  simp only [finProdFinEquiv_apply_val]
  lia

/-- Concatenated fixed-width rows recover the same finite tuple, including empty rows. -/
theorem wordBits_flatten_ofFn {count width : ℕ} (rows : Fin count → BitString width) :
    wordBits (count * width) ((List.ofFn rows).map List.ofFn).flatten =
      (maskEquiv count width).symm rows := by
  simp only [List.map_ofFn, Function.comp_def, ← ofFn_maskEquiv_symm, wordBits_ofFn]

/-- Interpret a flat sampled word as a matrix of masks. -/
def masksFromWord (k n : ℕ) (word : Word) : Fin k → BitString n :=
  maskEquiv k n (wordBits (k * n) word)

/-- Read one row of the sampled mask tape, padding missing bits with false. -/
def maskRow (dimension row : ℕ) (word : Word) : Word :=
  (List.range dimension).map (fun column => word[row * dimension + column]?.getD false)

/-- Read the mask tape as an ordinary list of rows, padding missing bits with false. -/
def maskRows (count dimension : ℕ) (word : Word) : List Word :=
  (List.range count).map (fun row => maskRow dimension row word)

/-- Matrix parsing charges for the dimension, every runtime index, and the complete output. -/
theorem maskRows_isPolyTime {α : Type} {encode : α ↪ Word}
    {count dimension : α → ℕ} {word : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hdimension : IsPolyTime encode (fun a => unaryEncoding (dimension a)))
    (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => listEncoding wordEncoding
      (maskRows (count a) (dimension a) (word a))) := by
  unfold maskRows maskRow
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] maskRows_isPolyTime

/-- The nested-list program is exactly the finite matrix interpretation, also on short tapes. -/
theorem maskRows_eq_ofFn (count dimension : ℕ) (word : Word) :
    maskRows count dimension word =
      List.ofFn (fun row => List.ofFn (masksFromWord count dimension word row)) := by
  apply List.ext_getElem (by simp [maskRows])
  intro row hleft hright
  apply List.ext_getElem (by simp [maskRows, maskRow])
  intro column hleft' hright'
  simp [maskRows, maskRow, masksFromWord, maskEquiv, wordBits, Nat.mul_comm, Nat.add_comm]

/-- Reading fewer rows takes a prefix of the same matrix, including on short tapes. -/
theorem masksFromWord_prefix {count rows dimension : ℕ} (h : rows ≤ count) (word : Word) :
    masksFromWord rows dimension word = masksFromWord count dimension word ∘ Fin.castLE h := by
  ext row column
  simp [masksFromWord, maskEquiv, wordBits]

/-- Adding finite masks is exactly coordinatewise XOR of their word representations. -/
theorem ofFn_add {n : ℕ} (left right : BitString n) :
    List.ofFn (left + right) = (List.ofFn left).zipWith Bool.xor (List.ofFn right) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getElem_zipWith, Bool.add_eq_xor]

/-- Bitstring addition is uniformly efficient, including when the dimension varies
with the input. Its certificate uses the ordinary `zipWith` combinator. -/
theorem addMasks_isPolyTime {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => List.ofFn (left a + right a)) := by
  simpa only [ofFn_add] using hleft.zipWith hright Bool.xor

/-- A Boolean dot product is a pointwise AND followed by a parity fold on words. -/
theorem dotProduct_eq_foldl {n : ℕ} (left right : BitString n) :
    left ⬝ᵥ right = ((List.ofFn left).zipWith Bool.and (List.ofFn right)).foldl Bool.xor false := by
  have hzip : (List.ofFn left).zipWith Bool.and (List.ofFn right) =
      List.ofFn (fun i => left i * right i) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getElem_zipWith, Bool.mul_eq_and]
  rw [hzip, dotProduct, ← List.sum_ofFn]
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

/-- The dot product is uniformly efficient through word combinators. -/
theorem dotProduct_isPolyTime {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => [left a ⬝ᵥ right a]) := by
  simpa only [dotProduct_eq_foldl] using
    (hleft.zipWith hright Bool.and).foldl_bool Bool.xor false

/-- Uniform words become exactly uniform finite bitstrings. -/
theorem uniformBits_wordBits (n : ℕ) :
    (uniformBits n).map (wordBits n) = PMF.uniformOfFintype (BitString n) := by
  simp only [uniformBits, PMF.map_comp, Function.comp_def, wordBits_ofFn]
  exact PMF.map_id _

/-- A flat tape of `k * n` uniform bits supplies exactly `k` independent uniform masks. -/
theorem uniformBits_masksFromWord (k n : ℕ) :
    (uniformBits (k * n)).map (masksFromWord k n) =
      PMF.uniformOfFintype (Fin k → BitString n) := by
  change (uniformBits (k * n)).map ((maskEquiv k n) ∘ wordBits (k * n)) = _
  rw [← PMF.map_comp, uniformBits_wordBits]
  exact PMF.uniformOfFintype_map_equiv (maskEquiv k n)

end Cslib.Probability
