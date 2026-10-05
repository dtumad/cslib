/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Finite
public import Cslib.Computability.Machines.Turing.Tape.Snapshot

/-! # Machine certificates for finite tape snapshots -/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

variable {α Symbol : Type} {input : α → Word} {element : Symbol ↪ Word}

/-- Encode a snapshot's left cells, current cell, and right cells. -/
def snapshotEncoding (element : Symbol ↪ Word) : Tape.Snapshot Symbol ↪ Word where
  toFun tape := pairEncoding (listEncoding element)
    (pairEncoding element (listEncoding element)) (tape.left, tape.head, tape.right)
  inj' := by
    intro a b h
    have hab := (pairEncoding (listEncoding element)
      (pairEncoding element (listEncoding element))).injective h
    exact Tape.Snapshot.ext (congrArg Prod.fst hab)
      (congrArg (fun x => x.2.1) hab) (congrArg (fun x => x.2.2) hab)

@[simp] theorem length_snapshotEncoding (tape : Tape.Snapshot Symbol) :
    (snapshotEncoding element tape).length = 2 * (listEncoding element tape.left).length +
      2 * (element tape.head).length + (listEncoding element tape.right).length + 2 := by
  change (pairEncoding (listEncoding element) (pairEncoding element (listEncoding element))
    (tape.left, tape.head, tape.right)).length = _
  simp only [length_pairEncoding]
  omega

/-- Build the finite snapshot, charging for both sides and the current cell. -/
theorem IsPolyTime.snapshot {left right : α → List Symbol} {head : α → Symbol}
    (hleft : IsPolyTime input (fun a => listEncoding element (left a)))
    (hhead : IsPolyTime input (fun a => element (head a)))
    (hright : IsPolyTime input (fun a => listEncoding element (right a))) :
    IsPolyTime input (fun a => snapshotEncoding element ⟨left a, head a, right a⟩) :=
  hleft.pair (hhead.pair hright)

/-- Read the explicitly stored left side. -/
theorem IsPolyTime.snapshot_left {tape : α → Tape.Snapshot Symbol}
    (htape : IsPolyTime input (fun a => snapshotEncoding element (tape a))) :
    IsPolyTime input (fun a => listEncoding element (tape a).left) :=
  (show IsPolyTime input (fun a => pairEncoding (listEncoding element)
    (pairEncoding element (listEncoding element)) ((tape a).left, (tape a).head, (tape a).right))
      from htape).fst

/-- Read the current cell. -/
theorem IsPolyTime.snapshot_head {tape : α → Tape.Snapshot Symbol}
    (htape : IsPolyTime input (fun a => snapshotEncoding element (tape a))) :
    IsPolyTime input (fun a => element (tape a).head) :=
  (show IsPolyTime input (fun a => pairEncoding (listEncoding element)
    (pairEncoding element (listEncoding element)) ((tape a).left, (tape a).head, (tape a).right))
      from htape).snd.fst

/-- Read the explicitly stored right side. -/
theorem IsPolyTime.snapshot_right {tape : α → Tape.Snapshot Symbol}
    (htape : IsPolyTime input (fun a => snapshotEncoding element (tape a))) :
    IsPolyTime input (fun a => listEncoding element (tape a).right) :=
  (show IsPolyTime input (fun a => pairEncoding (listEncoding element)
    (pairEncoding element (listEncoding element)) ((tape a).left, (tape a).head, (tape a).right))
      from htape).snd.snd

/-- Replace the head cell, retaining both sides. -/
theorem IsPolyTime.snapshot_write {tape : α → Tape.Snapshot Symbol} {value : α → Symbol}
    (htape : IsPolyTime input (fun a => snapshotEncoding element (tape a)))
    (hvalue : IsPolyTime input (fun a => element (value a))) :
    IsPolyTime input (fun a => snapshotEncoding element ((tape a).write (value a))) :=
  htape.snapshot_left.snapshot hvalue htape.snapshot_right

/-- Moving a represented head is an ordinary certified list computation. -/
theorem IsPolyTime.snapshot_move [Inhabited Symbol]
    {tape : α → Tape.Snapshot Symbol} {direction : α → SignType}
    (htape : IsPolyTime input (fun a => snapshotEncoding element (tape a)))
    (hdir : IsPolyTime input (fun a => finiteEncoding SignType (direction a))) :
    IsPolyTime input (fun a => snapshotEncoding element ((tape a).move (direction a))) := by
  apply hdir.finite_cases (branch := fun dir a => snapshotEncoding element ((tape a).move dir))
  intro dir
  cases dir with
  | zero => exact htape
  | neg =>
    exact htape.snapshot_left.list_tail.snapshot (htape.snapshot_left.list_headD default)
      (htape.snapshot_head.list_cons htape.snapshot_right)
  | pos =>
    exact (htape.snapshot_head.list_cons htape.snapshot_left).snapshot
      (htape.snapshot_right.list_headD default) htape.snapshot_right.list_tail

/-- One write changes at most the fixed-size current-cell encoding. -/
theorem length_snapshotEncoding_write_le (tape : Tape.Snapshot Symbol) (symbol : Symbol)
    {bound : ℕ} (hsymbol : (element symbol).length ≤ bound) :
    (snapshotEncoding element (tape.write symbol)).length ≤
      (snapshotEncoding element tape).length + 2 * bound := by
  simp only [length_snapshotEncoding, Tape.Snapshot.write]
  omega

/-- With a fixed alphabet encoding, a head move has constant representation growth. -/
theorem length_snapshotEncoding_move_le [Inhabited Symbol] (tape : Tape.Snapshot Symbol)
    (direction : SignType) {bound : ℕ} (hsymbol : ∀ symbol, (element symbol).length ≤ bound) :
    (snapshotEncoding element (tape.move direction)).length ≤
      (snapshotEncoding element tape).length + (4 * bound + 2) := by
  have hl : (listEncoding element tape.left.tail).length ≤
      (listEncoding element tape.left).length := by
    simpa only [List.drop_one] using length_listEncoding_drop_le element tape.left 1
  have hr : (listEncoding element tape.right.tail).length ≤
      (listEncoding element tape.right).length := by
    simpa only [List.drop_one] using length_listEncoding_drop_le element tape.right 1
  have hh := hsymbol tape.head
  have hleft := hsymbol (tape.left.headD default)
  have hright := hsymbol (tape.right.headD default)
  cases direction <;>
    simp only [Tape.Snapshot.move, length_snapshotEncoding, listEncoding_cons,
      length_pairEncoding] <;> omega

end Turing.MultiTapeTM
