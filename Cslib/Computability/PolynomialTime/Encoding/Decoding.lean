/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.PolynomialTime.List
public import Mathlib.Computability.Encoding

/-!
# Checked decoding at word interfaces

Mathlib's `Computability.Encoding` supplies a decoder and its round-trip law. Its encoder is
also the embedding used by machine certificates. Checking the decoded value's representation
rejects noncanonical words, without requiring a default value of the represented type.
-/

@[expose] public section

namespace Computability.Encoding

variable {α Γ : Type*}

/-- Use a decodable representation as an injective machine encoding. -/
def toEmbedding (encoding : Encoding α Γ) : α ↪ List Γ :=
  ⟨encoding.encode, encoding.encode_injective⟩

@[simp] theorem toEmbedding_apply (encoding : Encoding α Γ) (value : α) :
    encoding.toEmbedding value = encoding.encode value := rfl

/-- Decode only canonical words, rejecting every word outside the encoder's range. -/
def decodeChecked [DecidableEq Γ] (encoding : Encoding α Γ) (word : List Γ) : Option α :=
  (encoding.decode word).filter (fun value => encoding.encode value == word)

@[simp] theorem decodeChecked_eq_some [DecidableEq Γ] (encoding : Encoding α Γ)
    (word : List Γ) (value : α) :
    encoding.decodeChecked word = some value ↔ encoding.encode value = word := by
  simp only [decodeChecked, Option.filter_eq_some_iff, beq_iff_eq]
  exact ⟨And.right, fun h => ⟨h ▸ encoding.decode_encode value, h⟩⟩

@[simp] theorem decodeChecked_encode [DecidableEq Γ] (encoding : Encoding α Γ) (value : α) :
    encoding.decodeChecked (encoding.encode value) = some value :=
  (decodeChecked_eq_some _ _ _).mpr rfl

/-- Invalid words are exactly those with no represented value. -/
theorem decodeChecked_eq_none [DecidableEq Γ] (encoding : Encoding α Γ) (word : List Γ) :
    encoding.decodeChecked word = none ↔ word ∉ Set.range encoding.encode := by
  simp only [Option.eq_none_iff_forall_not_mem, Option.mem_def, decodeChecked_eq_some,
    Set.mem_range, not_exists]

/-- Two binary representations use the same tagged pair format as machine certificates. -/
def bitPair {β : Type*} (left : Encoding α Bool) (right : Encoding β Bool) :
    Encoding (α × β) Bool where
  encode value := List.BitPair.encode (left.encode value.1) (right.encode value.2)
  decode word := Option.map₂ Prod.mk (left.decode (List.BitPair.fst word))
    (right.decode (List.BitPair.snd word))
  decode_encode value := by simp

@[simp] theorem bitPair_toEmbedding {α β : Type} (left : Encoding α Bool)
    (right : Encoding β Bool) :
    (left.bitPair right).toEmbedding =
      Turing.MultiTapeTM.pairEncoding left.toEmbedding right.toEmbedding := rfl

end Computability.Encoding

namespace Turing.MultiTapeTM

variable {α : Type}

/-- Canonical validation preserves a decoder's polynomial bound. The decoder's result code
already contains the representation needed for comparison, so no typed fallback is required. -/
theorem IsPolyTime.decodeChecked (encoding : Computability.Encoding α Bool)
    (hdecode : IsPolyTime wordEncoding
      (fun word => optionEncoding encoding.toEmbedding (encoding.decode word))) :
    IsPolyTime wordEncoding
      (fun word => optionEncoding encoding.toEmbedding (encoding.decodeChecked word)) := by
  convert (hdecode.tail.beq (isPolyTime_input wordEncoding)).cond hdecode
    (isPolyTime_const wordEncoding []) using 1
  funext word
  cases h : encoding.decode word with
  | none => simp [Computability.Encoding.decodeChecked, h]
  | some value =>
    simp only [Computability.Encoding.decodeChecked, h, Option.filter_some,
      optionEncoding_some, List.tail_cons, Computability.Encoding.toEmbedding_apply]
    split <;> simp_all [wordEncoding]

/-- Decoding a compound request charges both parsers and assembly of the optional result. -/
theorem IsPolyTime.decode_bitPair {β : Type} (left : Computability.Encoding α Bool)
    (right : Computability.Encoding β Bool)
    (hl : IsPolyTime wordEncoding
      (fun word => optionEncoding left.toEmbedding (left.decode word)))
    (hr : IsPolyTime wordEncoding
      (fun word => optionEncoding right.toEmbedding (right.decode word))) :
    IsPolyTime wordEncoding (fun word =>
      optionEncoding (left.bitPair right).toEmbedding ((left.bitPair right).decode word)) :=
  (hl.comp_encoded isPolyTime_bitPair_fst).option_pair
    (hr.comp_encoded isPolyTime_bitPair_snd)

end Turing.MultiTapeTM
