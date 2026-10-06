/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Defs
public import Cslib.Foundations.Data.List.BitPair

/-!
# Encodings of structured data as binary words

Natural numbers in unary (`unaryEncoding`), for security parameters; pairs (`pairEncoding`) and
dependent pairs (`sigmaEncoding`) by tagging the bits of the first component; and optional values
(`optionEncoding`) by a leading tag bit. All of them have linear length.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β ι : Type} {γ : ι → Type}

/-- Natural numbers in unary, so that their value counts towards the input length. -/
def unaryEncoding : ℕ ↪ Word where
  toFun n := List.replicate n true
  inj' := by intro m n h; simpa using congrArg List.length h

@[simp]
theorem unaryEncoding_apply (n : ℕ) : unaryEncoding n = List.replicate n true := rfl

/-- Pairs, tagging each bit of the first component and then a delimiter. -/
def pairEncoding (left : α ↪ Word) (right : β ↪ Word) : (α × β) ↪ Word where
  toFun pair := List.BitPair.encode (left pair.1) (right pair.2)
  inj' := by
    intro a b h
    obtain ⟨hl, hr⟩ := List.BitPair.encode_inj.mp h
    exact Prod.ext (left.injective hl) (right.injective hr)

@[simp]
theorem length_pairEncoding (left : α ↪ Word) (right : β ↪ Word) (pair : α × β) :
    (pairEncoding left right pair).length = 2 * (left pair.1).length + (right pair.2).length + 1 :=
  List.BitPair.length_encode _ _

/-- Dependent pairs, encoding the index and then the value as a pair. -/
def sigmaEncoding (index : ι ↪ Word) (element : ∀ i, γ i ↪ Word) : Sigma γ ↪ Word where
  toFun value := List.BitPair.encode (index value.1) (element value.1 value.2)
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    obtain ⟨hi, hx⟩ := List.BitPair.encode_inj.mp h
    obtain rfl := index.injective hi
    obtain rfl := (element i).injective hx
    rfl

@[simp]
theorem length_sigmaEncoding (index : ι ↪ Word) (element : ∀ i, γ i ↪ Word) (value : Sigma γ) :
    (sigmaEncoding index element value).length =
      2 * (index value.1).length + (element value.1 value.2).length + 1 :=
  List.BitPair.length_encode _ _

/-- Optional values: nothing for `none`, and a tag bit before the value for `some`. -/
def optionEncoding (element : α ↪ Word) : Option α ↪ Word where
  toFun
    | none => []
    | some value => true :: element value
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [element.injective.eq_iff]

end Turing.MultiTapeTM
