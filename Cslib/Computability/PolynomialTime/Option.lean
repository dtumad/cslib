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

variable {α β : Type} {encode : α → Word} {element : β ↪ Word}

/-- Tag an efficiently computed value as present. -/
theorem IsPolyTime.option_some {value : α → β}
    (hvalue : IsPolyTime encode (fun a => element (value a))) :
    IsPolyTime encode (fun a => optionEncoding element (some (value a))) :=
  (isPolyTime_const encode [true]).append hvalue

/-- Presence is read from the first bit of an optional value's encoding. -/
theorem IsPolyTime.option_isSome {value : α → Option β}
    (hvalue : IsPolyTime encode (fun a => optionEncoding element (value a))) :
    IsPolyTime encode (fun a => [(value a).isSome]) := by
  convert hvalue.headD false using 1
  funext a
  cases value a <;> rfl

/-- Read an optional value, with an efficiently computed default. -/
theorem IsPolyTime.option_getD {value : α → Option β} {fallback : α → β}
    (hvalue : IsPolyTime encode (fun a => optionEncoding element (value a)))
    (hfallback : IsPolyTime encode (fun a => element (fallback a))) :
    IsPolyTime encode (fun a => element ((value a).getD (fallback a))) := by
  convert hvalue.option_isSome.cond hvalue.tail hfallback using 1
  funext a
  cases value a <;> rfl

/-- Prefer the first present value; both computations have certified polynomial bounds. -/
theorem IsPolyTime.option_orElse {left right : α → Option β}
    (hleft : IsPolyTime encode (fun a => optionEncoding element (left a)))
    (hright : IsPolyTime encode (fun a => optionEncoding element (right a))) :
    IsPolyTime encode (fun a => optionEncoding element ((left a).orElse (fun _ => right a))) := by
  convert hleft.option_isSome.cond hleft hright using 1
  funext a
  cases left a <;> rfl

end Turing.MultiTapeTM
