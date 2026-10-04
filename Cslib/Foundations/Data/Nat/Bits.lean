/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Size

/-! # Reading little-endian binary words -/

@[expose] public section

namespace Nat

/-- Read a little-endian binary word. Trailing zero bits are allowed. -/
def ofBitsList (word : List Bool) : ℕ := word.foldr bit 0

@[simp] theorem ofBitsList_nil : ofBitsList [] = 0 := rfl

@[simp] theorem ofBitsList_cons (b : Bool) (word : List Bool) :
    ofBitsList (b :: word) = bit b (ofBitsList word) := rfl

@[simp] theorem ofBitsList_bits (n : ℕ) : ofBitsList n.bits = n := by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h ih => simp [bits_append_bit n b h, ih]

theorem bits_injective : Function.Injective bits :=
  Function.LeftInverse.injective ofBitsList_bits

/-- A word of length `length` represents a value below `2 ^ length`, even with trailing zeros. -/
theorem ofBitsList_lt (word : List Bool) : ofBitsList word < 2 ^ word.length := by
  induction word with
  | nil => simp
  | cons b word ih =>
    simpa only [ofBitsList_cons, List.length_cons, bit_lt_two_pow_succ_iff] using ih

theorem length_bits_ofBitsList_le (word : List Bool) :
    (ofBitsList word).bits.length ≤ word.length := by
  rw [size_eq_bits_len, size_le]
  exact ofBitsList_lt word

/-- The zero case is the only time adding a bit shortens the canonical representation. -/
theorem bits_bit (b : Bool) (n : ℕ) :
    (bit b n).bits = if n = 0 ∧ b = false then [] else b :: n.bits := by
  by_cases hn : n = 0
  · subst n
    cases b <;> simp [bit]
  · simp [hn, bits_append_bit n b (fun h => (hn h).elim)]

theorem length_bits_bit_le (b : Bool) (n : ℕ) :
    (bit b n).bits.length ≤ n.bits.length + 1 := by
  rw [bits_bit]
  split <;> simp

/-- Sampling a word of the canonical bit length wastes at most half the possible words. -/
theorem two_pow_size_le_twice (n : ℕ) (hn : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  have hs : 0 < n.size := size_pos.mpr hn
  calc
    2 ^ n.size = 2 ^ (n.size - 1 + 1) := by congr 1; omega
    _ = 2 ^ (n.size - 1) * 2 := Nat.pow_succ _ _
    _ ≤ n * 2 := Nat.mul_le_mul_right 2 (lt_size.mp (by omega))
    _ = 2 * n := Nat.mul_comm _ _

end Nat
