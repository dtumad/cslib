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

/-- Tag a disjoint union with one bit before its payload. -/
def bitSum {β : Type*} (left : Encoding α Bool) (right : Encoding β Bool) :
    Encoding (α ⊕ β) Bool where
  encode
    | .inl value => false :: left.encode value
    | .inr value => true :: right.encode value
  decode
    | [] => none
    | false :: word => (left.decode word).map Sum.inl
    | true :: word => (right.decode word).map Sum.inr
  decode_encode value := by cases value <;> simp

@[simp] theorem decodeChecked_bitSum_nil {β : Type*}
    (left : Encoding α Bool) (right : Encoding β Bool) :
    (left.bitSum right).decodeChecked [] = none := rfl

@[simp] theorem decodeChecked_bitSum_false {β : Type*}
    (left : Encoding α Bool) (right : Encoding β Bool) (word : List Bool) :
    (left.bitSum right).decodeChecked (false :: word) =
      (left.decodeChecked word).map Sum.inl := by
  cases h : left.decode word <;> simp [decodeChecked, bitSum, h, Option.filter_some]

@[simp] theorem decodeChecked_bitSum_true {β : Type*}
    (left : Encoding α Bool) (right : Encoding β Bool) (word : List Bool) :
    (left.bitSum right).decodeChecked (true :: word) =
      (right.decodeChecked word).map Sum.inr := by
  cases h : right.decode word <;> simp [decodeChecked, bitSum, h, Option.filter_some]

/-- Optional values use the same empty-or-tagged representation as machine certificates.
The outer optional result of decoding distinguishes malformed words from a valid `none`. -/
def bitOption (element : Encoding α Bool) : Encoding (Option α) Bool where
  encode
    | none => []
    | some value => true :: element.encode value
  decode
    | [] => some none
    | false :: _ => none
    | true :: word => some <$> element.decode word
  decode_encode value := by cases value <;> simp

@[simp] theorem bitOption_toEmbedding {α : Type} (element : Encoding α Bool) :
    element.bitOption.toEmbedding = Turing.MultiTapeTM.optionEncoding element.toEmbedding := rfl

end Computability.Encoding

namespace Turing.MultiTapeTM

variable {α : Type}

/-- Canonical validation works uniformly with parameter-dependent representations. Both the
decoded value and its code come from the certified parser; comparison needs no typed default. -/
theorem IsPolyTime.decodeChecked_indexed {Input Index : Type} {Value : Index → Type}
    {input : Input → Word} {parameter : Input → Index} {word : Input → Word}
    (encoding : ∀ i, Computability.Encoding (Value i) Bool)
    (hword : IsPolyTime input word)
    (hdecode : IsPolyTime input (fun a =>
      optionEncoding (encoding (parameter a)).toEmbedding
        ((encoding (parameter a)).decode (word a)))) :
    IsPolyTime input (fun a => optionEncoding (encoding (parameter a)).toEmbedding
      ((encoding (parameter a)).decodeChecked (word a))) := by
  convert (hdecode.tail.beq hword).cond hdecode (isPolyTime_const input []) using 1
  funext a
  cases h : (encoding (parameter a)).decode (word a) with
  | none => simp [Computability.Encoding.decodeChecked, h]
  | some value =>
    simp only [Computability.Encoding.decodeChecked, h, Option.filter_some,
      optionEncoding_some, List.tail_cons, Computability.Encoding.toEmbedding_apply]
    split <;> simp_all

/-- Canonical validation preserves a decoder's polynomial bound. The decoder's result code
already contains the representation needed for comparison, so no typed fallback is required. -/
theorem IsPolyTime.decodeChecked (encoding : Computability.Encoding α Bool)
    (hdecode : IsPolyTime wordEncoding
      (fun word => optionEncoding encoding.toEmbedding (encoding.decode word))) :
    IsPolyTime wordEncoding
      (fun word => optionEncoding encoding.toEmbedding (encoding.decodeChecked word)) :=
  IsPolyTime.decodeChecked_indexed (parameter := fun _ => ()) (fun _ => encoding)
    (isPolyTime_input wordEncoding) hdecode

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
