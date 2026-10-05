/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding

/-! # Polynomial-time optional values -/

public section

namespace Turing.MultiTapeTM

variable {α : Type} {β : α → Type} {encode : α → Word} {element : ∀ a, β a ↪ Word}

/-- Tag an efficiently computed value as present. -/
theorem IsPolyTime.option_some {value : ∀ a, β a}
    (hvalue : IsPolyTime encode (fun a => element a (value a))) :
    IsPolyTime encode (fun a => optionEncoding (element a) (some (value a))) :=
  (isPolyTime_const encode [true]).append hvalue

/-- Presence is read from the first bit of an optional value's encoding. -/
theorem IsPolyTime.option_isSome {value : ∀ a, Option (β a)}
    (hvalue : IsPolyTime encode (fun a => optionEncoding (element a) (value a))) :
    IsPolyTime encode (fun a => [(value a).isSome]) := by
  convert hvalue.headD false using 1
  funext a
  cases value a <;> rfl

/-- Read an optional value, with an efficiently computed default. -/
theorem IsPolyTime.option_getD {value : ∀ a, Option (β a)} {fallback : ∀ a, β a}
    (hvalue : IsPolyTime encode (fun a => optionEncoding (element a) (value a)))
    (hfallback : IsPolyTime encode (fun a => element a (fallback a))) :
    IsPolyTime encode (fun a => element a ((value a).getD (fallback a))) := by
  convert hvalue.option_isSome.cond hvalue.tail hfallback using 1
  funext a
  cases value a <;> rfl

/-- Prefer the first present value; both computations have certified polynomial bounds. -/
theorem IsPolyTime.option_orElse {left right : ∀ a, Option (β a)}
    (hleft : IsPolyTime encode (fun a => optionEncoding (element a) (left a)))
    (hright : IsPolyTime encode (fun a => optionEncoding (element a) (right a))) :
    IsPolyTime encode
      (fun a => optionEncoding (element a) ((left a).orElse (fun _ => right a))) := by
  convert hleft.option_isSome.cond hleft hright using 1
  funext a
  cases left a <;> rfl

/-- Pair present values without choosing defaults for either represented type. -/
theorem IsPolyTime.option_pair {γ : α → Type} {other : ∀ a, γ a ↪ Word}
    {left : ∀ a, Option (β a)} {right : ∀ a, Option (γ a)}
    (hleft : IsPolyTime encode (fun a => optionEncoding (element a) (left a)))
    (hright : IsPolyTime encode (fun a => optionEncoding (other a) (right a))) :
    IsPolyTime encode (fun a => optionEncoding (pairEncoding (element a) (other a))
      (Option.map₂ Prod.mk (left a) (right a))) := by
  have hpair := (hleft.tail.pair (left := wordEncoding) (right := wordEncoding)
    hright.tail).option_some
  convert (hleft.option_isSome.bool₂ hright.option_isSome (· && ·)).cond hpair
    (isPolyTime_const encode []) using 1
  funext a
  cases left a <;> cases right a <;> rfl

/-- Project the first field of a present pair without a default for either type. -/
theorem IsPolyTime.option_fst {γ : α → Type} {other : ∀ a, γ a ↪ Word}
    {value : ∀ a, Option (β a × γ a)}
    (hvalue : IsPolyTime encode (fun a =>
      optionEncoding (pairEncoding (element a) (other a)) (value a))) :
    IsPolyTime encode (fun a => optionEncoding (element a) ((value a).map Prod.fst)) := by
  convert hvalue.option_isSome.cond
    (hvalue.tail.bitPair_fst.option_some (element := fun _ => wordEncoding))
    (isPolyTime_const encode []) using 1
  funext a
  cases value a <;> simp [pairEncoding_apply, wordEncoding]

/-- Project the second field of a present pair without a default for either type. -/
theorem IsPolyTime.option_snd {γ : α → Type} {other : ∀ a, γ a ↪ Word}
    {value : ∀ a, Option (β a × γ a)}
    (hvalue : IsPolyTime encode (fun a =>
      optionEncoding (pairEncoding (element a) (other a)) (value a))) :
    IsPolyTime encode (fun a => optionEncoding (other a) ((value a).map Prod.snd)) := by
  convert hvalue.option_isSome.cond
    (hvalue.tail.bitPair_snd.option_some (element := fun _ => wordEncoding))
    (isPolyTime_const encode []) using 1
  funext a
  cases value a <;> simp [pairEncoding_apply, wordEncoding]

/-- Compose checked computations using a certified continuation on a defaulted argument.
The default is used only to obtain a total certificate: an absent input always stays absent. -/
theorem IsPolyTime.option_bind_getD {γ : α → Type} {output : ∀ a, γ a ↪ Word}
    {value : ∀ a, Option (β a)} {fallback : ∀ a, β a} {cont : ∀ a, β a → Option (γ a)}
    (hvalue : IsPolyTime encode (fun a => optionEncoding (element a) (value a)))
    (hcont : IsPolyTime encode
      (fun a => optionEncoding (output a) (cont a ((value a).getD (fallback a))))) :
    IsPolyTime encode (fun a => optionEncoding (output a) ((value a).bind (cont a))) := by
  convert hvalue.option_isSome.cond hcont (isPolyTime_const encode []) using 1
  funext a
  cases value a <;> rfl

end Turing.MultiTapeTM
