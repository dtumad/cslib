/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Binary
public import Cslib.Computability.PolynomialTime.Encoding.Decoding

/-!
# Binary encodings through finite-range equivalences

The equivalence chooses a representation, not a multiplication table. Arithmetic still needs its
own uniform machine certificates. The optional decoder rejects out-of-range indices. A total
conversion is also available when the caller supplies an efficiently encoded fallback.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Encode a finite value by its binary index under a supplied equivalence. -/
def finEquivEncoding {β : Type} {n : ℕ} (equiv : β ≃ Fin n) : β ↪ Word :=
  equiv.toEmbedding.trans (finBinaryEncoding n)

@[simp] theorem finEquivEncoding_apply {β : Type} {n : ℕ} (equiv : β ≃ Fin n) (value : β) :
    finEquivEncoding equiv value = binaryEncoding (equiv value).val := rfl

/-- A checked conversion into an indexed finite type has a uniform machine certificate,
including the cost of its specified fallback. -/
theorem IsPolyTime.finEquiv_decode {α ι : Type} {β : ι → Type} {input : α → Word}
    {bound : ι → ℕ} (equiv : ∀ i, β i ≃ Fin (bound i))
    {parameter : α → ι} {value : α → ℕ} {fallback : ∀ a, β (parameter a)}
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound (parameter a))))
    (hvalue : IsPolyTime input (fun a => binaryEncoding (value a)))
    (hfallback : IsPolyTime input
      (fun a => finEquivEncoding (equiv (parameter a)) (fallback a))) :
    IsPolyTime input (fun a => finEquivEncoding (equiv (parameter a))
      (if h : value a < bound (parameter a) then (equiv (parameter a)).symm ⟨value a, h⟩
        else fallback a)) := by
  convert (hvalue.binary_lt hbound).cond hvalue hfallback using 1
  funext a
  by_cases h : value a < bound (parameter a) <;> simp [h]

end Turing.MultiTapeTM

namespace Computability.Encoding

open Turing.MultiTapeTM

/-- Decode finite-range binary indices through a supplied equivalence. Out-of-range values
are rejected, including when the represented type is empty. -/
def finEquiv {α : Type} {n : ℕ} (equiv : α ≃ Fin n) : Encoding α Bool where
  encode := finEquivEncoding equiv
  decode word := if h : Nat.ofBitsList word < n then some (equiv.symm ⟨_, h⟩) else none
  decode_encode value := by simp [finEquivEncoding_apply, (equiv value).isLt]

@[simp] theorem finEquiv_toEmbedding {α : Type} {n : ℕ} (equiv : α ≃ Fin n) :
    (finEquiv equiv).toEmbedding = finEquivEncoding equiv := rfl

end Computability.Encoding

namespace Turing.MultiTapeTM

/-- Finite-range parsing has a uniform bound in the binary range and input lengths.
The decoder returns `none` outside the range and needs no represented fallback. -/
theorem IsPolyTime.decode_finEquiv {Input Index : Type} {Value : Index → Type}
    {input : Input → Word} {parameter : Input → Index} {word : Input → Word}
    {bound : Index → ℕ} (equiv : ∀ i, Value i ≃ Fin (bound i))
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound (parameter a))))
    (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => optionEncoding (finEquivEncoding (equiv (parameter a)))
      ((Computability.Encoding.finEquiv (equiv (parameter a))).decode (word a))) := by
  have hvalue := hword.binary_ofBitsList
  convert (hvalue.binary_lt hbound).cond hvalue.option_some (isPolyTime_const input []) using 1
  funext a
  by_cases h : Nat.ofBitsList (word a) < bound (parameter a) <;>
    simp [Computability.Encoding.finEquiv, h, finEquivEncoding_apply]

end Turing.MultiTapeTM
