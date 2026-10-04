/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Binary

/-!
# Binary encodings through finite-range equivalences

The equivalence chooses a representation, not a multiplication table. Arithmetic still needs its
own uniform machine certificates. Decoding checks the binary range before constructing a value;
the caller supplies an efficiently encoded fallback for values outside that range.
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
