/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindLast
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Preparing a buffered word for use as input

A completed output buffer has its head just past the word. `prepareInput` rewinds that buffer
and places a left-boundary marker on one fresh tape. It preserves all source work tapes and
heads, the outer input head, and the buffered word, and costs `word.length + 4` transitions.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace PrepareInput

/-- Finite control for marking the input boundary and rewinding the buffered word. -/
abbrev Control := Bool ⊕ RewindWorkState

/-- The flag needed to distinguish the virtual input's two blank endmarkers. -/
def flag : ℤ → Option Bool := Function.update (fun _ => none) (-1) (some true)

/-- Write or erase the cell immediately left of a fresh boundary head, then return to zero. -/
@[simps] def setBoundary (k : ℕ) (symbol : Option Bool) : MultiTapeTM (k + 1) Bool Bool where
  q₀ := false
  tr writing _ _ :=
    { inputTape := 0
      workTapes := Fin.lastCases
        (if writing then (some symbol, 1) else (none, -1)) (fun _ => (none, 0))
      output := none
      state := if writing then none else some true }

theorem runFrom_setBoundary {k : ℕ} {State : Type} {input : List Bool}
    (symbol : Option Bool) (cfg : Cfg (k + 1) Bool State input)
    (hposition : cfg.workTapePos (Fin.last k) = 0) :
    (setBoundary k symbol).runFrom (cfg.withState (some false)) 2 =
      { cfg.withState (none : Option Bool) with
        workTapes := Function.update cfg.workTapes (Fin.last k)
          (Function.update (cfg.workTapes (Fin.last k)) (-1) symbol) } := by
  simp only [runFrom, Function.iterate_succ_apply, Function.iterate_zero, id_eq]
  refine Cfg.ext rfl (by simp [step, setBoundary, Cfg.withState, Action.apply]) ?_ ?_
    (by simp [step, setBoundary, Cfg.withState, Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [step, setBoundary, Cfg.withState, Action.apply, hposition]

/-- Write the left-boundary flag and return its head to zero in two transitions. -/
@[simps!] def markBoundary (k : ℕ) : MultiTapeTM (k + 1) Bool Bool :=
  setBoundary k (some true)

theorem runFrom_markBoundary {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg (k + 1) Bool State input) (hposition : cfg.workTapePos (Fin.last k) = 0) :
    (markBoundary k).runFrom (cfg.withState (some false)) 2 =
      { cfg.withState (none : Option Bool) with
        workTapes := Function.update cfg.workTapes (Fin.last k)
          (Function.update (cfg.workTapes (Fin.last k)) (-1) (some true)) } :=
  runFrom_setBoundary (some true) cfg hposition

/-- Add an unused flag tape to a completed output buffer. -/
def before {k : ℕ} {State : Type} {input : List Bool} (cfg : Cfg k Bool State input) :
    Cfg (k + 2) Bool State input :=
  embed Fin.castSuccEmb (outCfg cfg) (fun _ _ => none) (fun _ => 0)

/-- The same tapes after marking the boundary and rewinding the buffer. -/
def after {k : ℕ} {State State' : Type} {input : List Bool} (cfg : Cfg k Bool State input)
    (state : Option State') : Cfg (k + 2) Bool State' input where
  state := state
  inputPos := cfg.inputPos
  workTapes := Fin.lastCases flag (Fin.lastCases (tapeOfList cfg.output) cfg.workTapes)
  workTapePos := Fin.lastCases 0 (Fin.lastCases 0 cfg.workTapePos)
  output := []

@[simp] theorem after_workTapes_castAdd {k : ℕ} {State State' : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (state : Option State') (i : Fin k) :
    (after cfg state).workTapes (i.castAdd 2) = cfg.workTapes i := by
  change (after cfg state).workTapes i.castSucc.castSucc = _
  simp [after]

@[simp] theorem after_workTapes_zero {k : ℕ} {State State' : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (state : Option State') :
    (after cfg state).workTapes (Fin.natAdd k 0) = tapeOfList cfg.output := by
  change (after cfg state).workTapes (Fin.last k).castSucc = _
  simp [after]

@[simp] theorem after_workTapes_one {k : ℕ} {State State' : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (state : Option State') :
    (after cfg state).workTapes (Fin.natAdd k 1) = flag := by
  change (after cfg state).workTapes (Fin.last (k + 1)) = _
  simp [after]

@[simp] theorem after_workTapePos_castAdd {k : ℕ} {State State' : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (state : Option State') (i : Fin k) :
    (after cfg state).workTapePos (i.castAdd 2) = cfg.workTapePos i := by
  change (after cfg state).workTapePos i.castSucc.castSucc = _
  simp [after]

@[simp] theorem after_workTapePos_natAdd {k : ℕ} {State State' : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (state : Option State') (i : Fin 2) :
    (after cfg state).workTapePos (Fin.natAdd k i) = 0 := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · change (after cfg state).workTapePos (Fin.last k).castSucc = _
    simp [after]
  · change (after cfg state).workTapePos (Fin.last (k + 1)) = _
    simp [after]

private theorem partialInv_last (k : ℕ) : partialInv Fin.castSuccEmb (Fin.last k) = none := by
  apply partialInv_eq_none
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  have := i.isLt
  simp only [Fin.castSuccEmb_apply, Fin.val_castSucc, Fin.val_last] at *
  omega

private theorem partialInv_castSucc (k : ℕ) (i : Fin k) :
    partialInv Fin.castSuccEmb i.castSucc = some i := partialInv_embed Fin.castSuccEmb i

theorem mark_before {k : ℕ} {State : Type} {input : List Bool} (cfg : Cfg k Bool State input) :
    (markBoundary (k + 1)).runFrom ((before cfg).withState (some false)) 2 =
      embed Fin.castSuccEmb ((outCfg cfg).withState (none : Option Bool))
        (fun _ => flag) (fun _ => 0) := by
  rw [runFrom_markBoundary]
  · refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
      simp [before, embed, Cfg.withState, flag, partialInv_last, partialInv_castSucc]
  · simp [before, embed, partialInv_last]

end PrepareInput

/-- Turn a completed output buffer and a blank flag tape into a ready virtual input. -/
def prepareInput (k : ℕ) : MultiTapeTM (k + 2) Bool PrepareInput.Control :=
  (PrepareInput.markBoundary (k + 1)).seq ((rewindLast k).extendTapes Fin.castSuccEmb)

/-- Preparation restores both virtual-input heads, preserves the word and every source tape,
and works equally for the empty word. -/
theorem runFrom_prepareInput {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) :
    (prepareInput k).runFrom ((PrepareInput.before cfg).withState (some (prepareInput k).q₀))
      (cfg.output.length + 4) = PrepareInput.after cfg none := by
  let marker := PrepareInput.markBoundary (k + 1)
  let rewind := (rewindLast k).extendTapes Fin.castSuccEmb
  let initial := (PrepareInput.before cfg).withState (some false)
  have hmark := PrepareInput.mark_before cfg
  have hrewind : rewind.runFrom ((marker.runFrom initial 2).withState (some rewind.q₀))
      (cfg.output.length + 2) =
      embed Fin.castSuccEmb (RewindLast.config (outCfg cfg) none 0)
        (fun _ => PrepareInput.flag) (fun _ => 0) := by
    rw [hmark]
    change rewind.runFrom
      (embed Fin.castSuccEmb ((outCfg cfg).withState (some RewindWorkState.start))
        (fun _ => PrepareInput.flag) (fun _ => 0)) _ = _
    rw [runFrom_embed, runFrom_rewindLast (outCfg cfg) cfg.output
      (outCfg_workTapes_last cfg) (outCfg_workTapePos_last cfg)]
  have hseq := runFrom_seq (tm₀ := marker) (cfg := initial) (t₀ := 2)
    rfl (by rw [hmark]; rfl) hrewind rfl
  change (prepareInput k).runFrom
    ((PrepareInput.before cfg).withState (some (prepareInput k).q₀)) _ = _ at hseq
  rw [show 2 + (cfg.output.length + 2) = cfg.output.length + 4 by omega] at hseq
  rw [hseq]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | last => simp [Sequential.rightCfg, Cfg.mapState, embed, PrepareInput.after,
      PrepareInput.partialInv_last]
  | cast i =>
    induction i using Fin.lastCases <;>
      simp [Sequential.rightCfg, Cfg.mapState, embed, PrepareInput.after, RewindLast.config,
        outCfg, Cfg.withState, PrepareInput.partialInv_castSucc]

end Turing.MultiTapeTM
