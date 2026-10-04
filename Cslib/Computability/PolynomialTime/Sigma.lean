/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding

/-!
# Encodings for indexed data

A dependent pair stores the parameter once, followed by its value's encoding. In particular,
cryptographic group families can share one machine across all security parameters, with the
parameter in unary and group elements and scalars in binary.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {ι α : Type} {β : ι → Type}

/-- Encode the index and its dependent value using the ordinary tagged pair representation. -/
def sigmaEncoding (index : ι ↪ Word) (element : ∀ i, β i ↪ Word) : Sigma β ↪ Word where
  toFun value := List.BitPair.encode (index value.1) (element value.1 value.2)
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have he := List.BitPair.encode_inj.mp h
    have hi : i = j := index.injective he.1
    subst j
    have hx : x = y := (element i).injective he.2
    subst y
    rfl

@[simp] theorem length_sigmaEncoding (index : ι ↪ Word) (element : ∀ i, β i ↪ Word)
    (value : Sigma β) :
    (sigmaEncoding index element value).length =
      2 * (index value.1).length + (element value.1 value.2).length + 1 :=
  List.BitPair.length_encode _ _

variable {encode : α → Word} {index : ι ↪ Word} {element : ∀ i, β i ↪ Word}

/-- Assemble indexed data from its parameter and its encoded value. -/
theorem IsPolyTime.sigma {parameter : α → ι} {value : ∀ a, β (parameter a)}
    (hp : IsPolyTime encode (fun a => index (parameter a)))
    (hv : IsPolyTime encode (fun a => element (parameter a) (value a))) :
    IsPolyTime encode (fun a => sigmaEncoding index element ⟨parameter a, value a⟩) :=
  hp.pair (right := wordEncoding) hv

/-- Read the encoded parameter. -/
theorem IsPolyTime.sigma_fst {value : α → Sigma β}
    (hv : IsPolyTime encode (fun a => sigmaEncoding index element (value a))) :
    IsPolyTime encode (fun a => index (value a).1) :=
  (show IsPolyTime encode (fun a => pairEncoding index wordEncoding
    ((value a).1, element (value a).1 (value a).2)) from hv).fst

/-- Read the value's representation while preserving its dependency on the parameter. -/
theorem IsPolyTime.sigma_snd {value : α → Sigma β}
    (hv : IsPolyTime encode (fun a => sigmaEncoding index element (value a))) :
    IsPolyTime encode (fun a => element (value a).1 (value a).2) :=
  (show IsPolyTime encode (fun a => pairEncoding index wordEncoding
    ((value a).1, element (value a).1 (value a).2)) from hv).snd

end Turing.MultiTapeTM
