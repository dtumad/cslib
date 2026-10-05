/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Basic.Sign.Defs

/-!
# Finite tape snapshots

A snapshot records a tape using ordinary lists around its current head. It may retain blank cells,
so copying and encoding it have explicit finite sizes. Its interpretation uses Mathlib's `Tape`;
writing and moving agree exactly with that tape's operations.
-/

@[expose] public section

namespace Turing.Tape

/-- A finite tape representation, with each side listed outward from the current head. -/
@[ext] structure Snapshot (Symbol : Type*) where
  /-- Cells immediately to the left, nearest first. -/
  left : List Symbol
  /-- The cell under the head. -/
  head : Symbol
  /-- Cells immediately to the right, nearest first. -/
  right : List Symbol
deriving DecidableEq, Inhabited

namespace Snapshot

variable {Symbol : Type*} [Inhabited Symbol]

/-- Forget the finite representation, allowing arbitrary blank tails. -/
def toTape (snapshot : Snapshot Symbol) : Tape Symbol :=
  ⟨snapshot.head, ListBlank.mk snapshot.left, ListBlank.mk snapshot.right⟩

/-- Initialize a tape from a finite word. -/
def ofList (word : List Symbol) : Snapshot Symbol :=
  ⟨[], word.headD default, word.tail⟩

/-- Replace only the current cell. -/
def write (symbol : Symbol) (snapshot : Snapshot Symbol) : Snapshot Symbol :=
  { snapshot with head := symbol }

/-- Move one cell, materializing a blank if the representation ends. -/
def move (direction : SignType) (snapshot : Snapshot Symbol) : Snapshot Symbol :=
  match direction with
  | .neg => ⟨snapshot.left.tail, snapshot.left.headD default, snapshot.head :: snapshot.right⟩
  | .zero => snapshot
  | .pos => ⟨snapshot.head :: snapshot.left, snapshot.right.headD default, snapshot.right.tail⟩

@[simp] theorem toTape_head (snapshot : Snapshot Symbol) :
    snapshot.toTape.head = snapshot.head := rfl

@[simp] theorem toTape_ofList (word : List Symbol) : (ofList word).toTape = Tape.mk₁ word := by
  cases word <;> rfl

@[simp] theorem toTape_write (symbol : Symbol) (snapshot : Snapshot Symbol) :
    (snapshot.write symbol).toTape = snapshot.toTape.write symbol := rfl

@[simp] theorem toTape_move_neg (snapshot : Snapshot Symbol) :
    (snapshot.move (-1)).toTape = snapshot.toTape.move .left := by
  cases snapshot with
  | mk left head right => cases left <;> rfl

@[simp] theorem toTape_move_pos (snapshot : Snapshot Symbol) :
    (snapshot.move 1).toTape = snapshot.toTape.move .right := by
  cases snapshot with
  | mk left head right => cases right <;> rfl

@[simp] theorem toTape_move_zero (snapshot : Snapshot Symbol) :
    (snapshot.move 0).toTape = snapshot.toTape := rfl

/-- The interpretation tracks the head's translation on the two-sided tape. -/
theorem nth_move (snapshot : Snapshot Symbol) (direction : SignType) (offset : ℤ) :
    (snapshot.move direction).toTape.nth offset =
      snapshot.toTape.nth (offset + direction.cast) := by
  cases direction with
  | zero => rw [SignType.zero_eq_zero, toTape_move_zero]; simp [SignType.cast]
  | neg =>
    rw [SignType.neg_eq_neg_one, toTape_move_neg, Tape.move_left_nth]
    simp [SignType.cast, sub_eq_add_neg]
  | pos =>
    rw [SignType.pos_eq_one, toTape_move_pos, Tape.move_right_nth]
    rfl

/-- A write affects exactly the current cell. -/
theorem nth_write (snapshot : Snapshot Symbol) (symbol : Symbol) (offset : ℤ) :
    (snapshot.write symbol).toTape.nth offset =
      if offset = 0 then symbol else snapshot.toTape.nth offset := by
  simp

/-- The number of explicitly represented cells, including the current cell. -/
def size (snapshot : Snapshot Symbol) : ℕ := snapshot.left.length + snapshot.right.length + 1

omit [Inhabited Symbol] in
@[simp] theorem size_write (snapshot : Snapshot Symbol) (symbol : Symbol) :
    (snapshot.write symbol).size = snapshot.size := rfl

/-- Moving can allocate at most one blank cell. -/
theorem size_move_le (snapshot : Snapshot Symbol) (direction : SignType) :
    (snapshot.move direction).size ≤ snapshot.size + 1 := by
  cases direction <;> simp [size, move] <;> omega

end Snapshot
end Turing.Tape
