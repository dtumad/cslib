/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeCall
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransferWord
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# Updating a buffered subroutine argument

`tapeUpdate` calls a restoring machine on a buffered argument, then moves its result back
into the argument buffer. The old argument is completely erased, even if the result is
shorter. The result buffer, scratch tapes, and temporary flag are blank on return, so the
same machine can immediately be called again.

The construction uses the existing tape-call adapter, the three-tape word transfer, and
the shared tape embedding and sequencing machinery. The bound accounts for the call,
rewinding, clearing the old argument, and transferring the result.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.TapeCall

variable {k : ℕ} {State : Type} {outerInput : List Bool}

private theorem embed_words (input result output : List Bool) (state : Option State) :
    embed (Fin.natAddEmb k)
      (wordsCfg outerInput state ![result, input, []] output)
      (fun _ _ => none) (fun _ => 0) =
      wordsCfg outerInput state (words k input result) output := by
  have hleft (i : Fin k) : partialInv (Fin.natAddEmb k) (Fin.castAdd 3 i) = none := by
    apply partialInv_eq_none
    rintro ⟨j, he⟩
    have hv := congrArg Fin.val he
    simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at hv
    lia
  have hzero : Fin.natAdd k (0 : Fin 3) = (Fin.last k).castSucc.castSucc := rfl
  have hone : Fin.natAdd k (1 : Fin 3) = (Fin.last (k + 1)).castSucc := rfl
  have htwo : Fin.natAdd k (2 : Fin 3) = Fin.last (k + 2) := rfl
  have hcast (i : Fin k) : i.castAdd 3 = i.castSucc.castSucc.castSucc := rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    induction i using (Fin.addCases (m := k) (n := 3)) with
  | left i =>
    simp only [embed, hleft, wordsCfg] <;> simp [words, hcast]
  | right i =>
    have hinv : partialInv (Fin.natAddEmb k) (Fin.natAdd k i) = some i :=
      partialInv_embed (Fin.natAddEmb k) i
    simp only [embed, hinv, wordsCfg] <;>
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by lia) with rfl | rfl | rfl <;>
      simp [words, hzero, hone, htwo]

/-- Replace the argument buffer by the result, reusing the cleared boundary-flag tape. -/
def adoptResult (k : ℕ) : MultiTapeTM (k + 3) Bool Bool :=
  (TransferWord.machine true true).extendTapes (Fin.natAddEmb k)

/-- Moving the result restores the call layout with the new argument and blank result buffer. -/
theorem runFrom_adoptResult (input result output : List Bool) :
    (adoptResult k).runFrom
      (wordsCfg outerInput (some (adoptResult k).q₀) (words k input result) output)
      (2 * max result.length input.length + 2) =
      wordsCfg outerInput none (words k result []) output := by
  rw [← embed_words, ← embed_words, adoptResult, runFrom_embed]
  change embed _ ((TransferWord.machine true true).runFrom
    (wordsCfg outerInput (some (TransferWord.machine true true).q₀) ![result, input, []] output)
    (2 * max result.length input.length + 2)) _ _ = _
  rw [TransferWord.runFrom_machine]
  rfl

end Turing.MultiTapeTM.TapeCall

namespace Turing.MultiTapeTM
variable {k : ℕ} {State : Type} {outerInput : List Bool}

/-- Compute on a buffered word and replace it by the result, ready for another call. -/
def tapeUpdate (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + 3) Bool ((Bool ⊕ (State ⊕ (RewindWorkState ⊕ Bool))) ⊕ Bool) :=
  tm.tapeCall.seq (TapeCall.adoptResult k)

/-- A complete buffered update preserves the ambient input and output and restores workspace. -/
theorem runFrom_tapeUpdate (tm : MultiTapeTM k Bool State) (input result output : List Bool)
    (cost : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    tm.tapeUpdate.runFrom
      (wordsCfg outerInput (some tm.tapeUpdate.q₀) (TapeCall.words k input []) output)
      (cost + result.length + 2 * max result.length input.length + 8) =
      wordsCfg outerInput none (TapeCall.words k result []) output := by
  have hcall := runFrom_tapeCall (outerInput := outerInput) tm input result output cost h
  have hadopt := TapeCall.runFrom_adoptResult (k := k) (outerInput := outerInput)
    input result output
  have hmain := runFrom_seq hcall rfl hadopt rfl
  simpa [tapeUpdate, Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState, wordsCfg, seq,
    show cost + result.length + 6 + (2 * max result.length input.length + 2) =
      cost + result.length + 2 * max result.length input.length + 8 by lia] using hmain
end Turing.MultiTapeTM
