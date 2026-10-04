/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic

/-!
# Encoding pairs of binary words

Tag each bit of the first word with `true`, then place a `false` delimiter before the second
word. This injective, linear-size encoding is shared by value-level programs and machine input
preparation. This module defines the representation; efficiency certificates are separate.
-/

@[expose] public section

namespace List.BitPair

/-- Tag each bit so that `false` can delimit the first word. -/
def tagged (left : List Bool) : List Bool := left.flatMap fun bit => [true, bit]

/-- Encode two binary words as one. -/
def encode (left right : List Bool) : List Bool := tagged left ++ false :: right

/-- Read the tagged first component. An incomplete final tag is discarded; a missing delimiter
still returns all complete tagged bits. -/
def fst : List Bool → List Bool
  | true :: bit :: rest => bit :: fst rest
  | _ => []

/-- Read the suffix after the first delimiter. A word without a delimiter has empty suffix. -/
def snd : List Bool → List Bool
  | false :: rest => rest
  | true :: _ :: rest => snd rest
  | _ => []

@[simp] theorem fst_encode (left right : List Bool) : fst (encode left right) = left := by
  induction left with
  | nil => rfl
  | cons bit left ih => exact congrArg (bit :: ·) ih

@[simp] theorem snd_encode (left right : List Bool) : snd (encode left right) = right := by
  induction left with
  | nil => rfl
  | cons bit left ih => exact ih

/-- Tagging uses two bits per original bit. -/
@[simp] theorem length_tagged (left : List Bool) : (tagged left).length = 2 * left.length := by
  induction left with
  | nil => simp [tagged]
  | cons b bs ih => simp [tagged, List.length_flatMap] at *; lia

/-- The pair encoding has linear length. -/
@[simp] theorem length_encode (left right : List Bool) :
    (encode left right).length = 2 * left.length + right.length + 1 := by
  simp [encode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The encoded pair determines both words uniquely. -/
@[simp] theorem encode_inj {left right left' right' : List Bool} :
    encode left right = encode left' right' ↔ left = left' ∧ right = right' := by
  induction left generalizing left' with
  | nil => cases left' <;> simp [encode, tagged]
  | cons b bs ih =>
    cases left' with
    | nil => simp [encode, tagged]
    | cons b' bs' => simpa [encode, tagged, and_assoc] using
        (show b = b' ∧ encode bs right = encode bs' right' ↔
          b = b' ∧ bs = bs' ∧ right = right' by rw [ih])

/-- Every even cell of a tagged word is its tag. -/
theorem tagged_even (left : List Bool) (i : ℕ) (hi : i < left.length) :
    (tagged left)[2 * i]? = some true := by
  induction left generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [tagged]
    | succ i => simpa [tagged, Nat.mul_add, Nat.add_assoc] using ih i (by simpa using hi)

/-- Every odd cell of a tagged word is its original bit. -/
theorem tagged_odd (left : List Bool) (i : ℕ) (hi : i < left.length) :
    (tagged left)[2 * i + 1]? = left[i]? := by
  induction left generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [tagged]
    | succ i => simpa [tagged, Nat.mul_add, Nat.add_assoc] using ih i (by simpa using hi)

/-- Locate a first-word tag within the full encoding. -/
theorem encode_tag (left right : List Bool) (i : ℕ) (hi : i < left.length) :
    (encode left right)[2 * i]? = some true := by
  rw [encode, List.getElem?_append_left (by simp; lia)]
  exact tagged_even left i hi

/-- Locate a first-word bit within the full encoding. -/
theorem encode_coin (left right : List Bool) (i : ℕ) (hi : i < left.length) :
    (encode left right)[2 * i + 1]? = some left[i] := by
  rw [encode, List.getElem?_append_left (by simp; lia), tagged_odd left i hi,
    List.getElem?_eq_getElem hi]

/-- The tagged prefix is immediately followed by the delimiter. -/
theorem encode_delimiter (left right : List Bool) :
    (encode left right)[2 * left.length]? = some false := by
  simp [encode]

/-- The remaining cells are the second word. -/
theorem encode_input (left right : List Bool) (j : ℕ) :
    (encode left right)[2 * left.length + 1 + j]? = right[j]? := by
  simp [encode, List.getElem?_append_right, Nat.add_assoc, Nat.add_comm 1 j]

end List.BitPair
