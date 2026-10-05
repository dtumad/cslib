/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.List
public import Cslib.Foundations.Data.Nat.Bits
public import Mathlib.Data.Fin.Embedding

/-!
# Polynomial-time binary representations

Natural numbers use `Nat.bits`, with no padding and the least significant bit first.
Normalization and comparison traverse the representation, without constructing unary values.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

/-- Canonical little-endian binary encoding; zero is the empty word. -/
def binaryEncoding : ℕ ↪ Word := ⟨Nat.bits, Nat.bits_injective⟩

@[simp] theorem binaryEncoding_apply (n : ℕ) : binaryEncoding n = n.bits := rfl

/-- Bounded exponents use the same binary representation as their underlying natural numbers. -/
def finBinaryEncoding (n : ℕ) : Fin n ↪ Word := Fin.valEmbedding.trans binaryEncoding

@[simp] theorem finBinaryEncoding_apply (n : ℕ) (value : Fin n) :
    finBinaryEncoding n value = binaryEncoding value.val := rfl

variable {α : Type} {encode : α → Word}

/-- Read a binary value's bit length in unary, without expanding the value itself. -/
theorem IsPolyTime.binary_size {n : α → ℕ}
    (hn : IsPolyTime encode (fun a => binaryEncoding (n a))) :
    IsPolyTime encode (fun a => unaryEncoding (n a).size) := by
  simpa only [binaryEncoding_apply, Nat.size_eq_bits_len, unaryEncoding_apply] using hn.unaryLength

/-- Add a low bit, removing the redundant zero representation when both inputs are zero. -/
theorem IsPolyTime.binary_bit {n : α → ℕ} {bit : α → Bool}
    (hn : IsPolyTime encode (fun a => binaryEncoding (n a)))
    (hbit : IsPolyTime encode (fun a => [bit a])) :
    IsPolyTime encode (fun a => binaryEncoding (Nat.bit (bit a) (n a))) := by
  have heq (n : ℕ) : (n.bits == []) = decide (n = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact (Nat.bits_injective.eq_iff (b := 0))
  have hzero := (hn.beq (isPolyTime_const encode [])).bool₂ hbit
    (fun zero bit => zero && !bit)
  simpa [binaryEncoding, Nat.bits_bit, heq] using
    hzero.cond (isPolyTime_const encode []) (hbit.cons hn)

/-- Read an arbitrary bit word into the canonical binary representation. -/
theorem IsPolyTime.binary_ofBitsList {word : α → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => binaryEncoding (Nat.ofBitsList (word a))) := by
  have hstep := (isPolyTime_fst binaryEncoding boolEncoding).binary_bit
    (isPolyTime_snd binaryEncoding boolEncoding)
  simpa only [List.foldl_reverse, Function.flip_def, Nat.ofBitsList] using
    hword.reverse.foldl_of_bounded_growth (stateEncoding := binaryEncoding)
      (step := fun n bit => Nat.bit bit n) (initial := fun _ => 0)
      (isPolyTime_const encode []) hstep (growth := 1)
      (fun n bit => Nat.length_bits_bit_le bit n)

private abbrev CompareState := (Word × Word) × Bool

private def compareEncoding : CompareState ↪ Word :=
  pairEncoding (pairEncoding wordEncoding wordEncoding) boolEncoding

private def compareStep (state : CompareState) : CompareState :=
  ((state.1.1.tail, state.1.2.tail),
    if state.1.1.headD false == state.1.2.headD false then state.2 else state.1.2.headD false)

private def compareInvariant (state : CompareState) : Prop :=
  Nat.ofBitsList state.1.1 < Nat.ofBitsList state.1.2 ∨
    Nat.ofBitsList state.1.1 = Nat.ofBitsList state.1.2 ∧ state.2 = true

private theorem compareStep_invariant (state : CompareState) :
    compareInvariant (compareStep state) ↔ compareInvariant state := by
  rcases state with ⟨⟨left, right⟩, carry⟩
  cases left with
  | nil =>
    cases right with
    | nil => simp [compareStep, compareInvariant]
    | cons bit right =>
      cases bit <;> cases carry <;> simp [compareStep, compareInvariant, Nat.bit] <;> omega
  | cons bit left =>
    cases right with
    | nil => cases bit <;> simp [compareStep, compareInvariant, Nat.bit]
    | cons other right =>
      cases bit <;> cases other <;> simp [compareStep, compareInvariant, Nat.bit] <;> omega

private theorem compareStep_iterate (state : CompareState) (count : ℕ) :
    (compareStep^[count] state).1 = (state.1.1.drop count, state.1.2.drop count) ∧
      (compareInvariant (compareStep^[count] state) ↔ compareInvariant state) := by
  induction count generalizing state with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hp, hi⟩ := ih (compareStep state)
    exact ⟨by simpa [compareStep, List.drop_tail] using hp,
      hi.trans (compareStep_invariant state)⟩

/-- Compare arbitrary little-endian words, including words with trailing zero bits. -/
theorem IsPolyTime.ofBitsList_lt {left right : α → Word}
    (hleft : IsPolyTime encode left) (hright : IsPolyTime encode right) :
    IsPolyTime encode (fun a => [decide (Nat.ofBitsList (left a) < Nat.ofBitsList (right a))]) := by
  have hl := (isPolyTime_fst (pairEncoding wordEncoding wordEncoding) boolEncoding).fst
  have hr := (isPolyTime_fst (pairEncoding wordEncoding wordEncoding) boolEncoding).snd
  have hc := isPolyTime_snd (pairEncoding wordEncoding wordEncoding) boolEncoding
  have hstep : IsPolyTime compareEncoding (fun state => compareEncoding (compareStep state)) := by
    apply (hl.tail.pair hr.tail).pair
    simpa only [compareEncoding, wordEncoding, Function.Embedding.refl_apply,
      boolEncoding, Function.Embedding.coeFn_mk, apply_ite] using
      ((hl.headD false).bool₂ (hr.headD false) BEq.beq).cond hc (hr.headD false)
  have hloop := ((hleft.pair hright).pair (right := boolEncoding)
    (g := fun _ => false) (isPolyTime_const encode [false])).iterate_encoded_of_length_le
      (stateEncoding := compareEncoding) (step := compareStep)
      (hleft.unaryLength.unary_add hright.unaryLength) hstep (by
        intro state
        simp only [compareEncoding, compareStep, length_pairEncoding, wordEncoding,
          Function.Embedding.refl_apply, boolEncoding, Function.Embedding.coeFn_mk,
          List.length_singleton, List.length_tail]
        omega)
  have heval (a : α) :
      (compareStep^[(left a).length + (right a).length] ((left a, right a), false)).2 =
        decide (Nat.ofBitsList (left a) < Nat.ofBitsList (right a)) := by
    obtain ⟨hp, hi⟩ := compareStep_iterate ((left a, right a), false)
      ((left a).length + (right a).length)
    simp only [List.drop_eq_nil_of_le (Nat.le_add_right _ _),
      List.drop_eq_nil_of_le (Nat.le_add_left _ _)] at hp
    simp only [compareInvariant, hp, Nat.ofBitsList_nil, lt_self_iff_false, true_and,
      false_or, Bool.false_eq_true, and_false, or_false] at hi
    exact Bool.eq_iff_iff.mpr (by simpa using hi)
  simpa only [heval, boolEncoding, Function.Embedding.coeFn_mk] using hloop.snd

/-- Compare binary natural numbers in time polynomial in their bit lengths. -/
theorem IsPolyTime.binary_lt {left right : α → ℕ}
    (hleft : IsPolyTime encode (fun a => binaryEncoding (left a)))
    (hright : IsPolyTime encode (fun a => binaryEncoding (right a))) :
    IsPolyTime encode (fun a => [decide (left a < right a)]) := by
  simpa only [binaryEncoding_apply, Nat.ofBitsList_bits] using hleft.ofBitsList_lt hright

end Turing.MultiTapeTM
