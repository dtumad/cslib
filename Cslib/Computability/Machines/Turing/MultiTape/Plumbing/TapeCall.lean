/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Calling a subroutine on work-tape words

`tapeCall` invokes a machine that restores its scratch tapes and input head. The machine reads
its input from a work-tape word, and its result is written to a separate work tape. The ambient
input and output are untouched. All heads and scratch tapes are restored before the call returns.

The layout reserves the source machine's `k` scratch tapes, then a result buffer, an input
buffer, and a temporary boundary flag. The result buffer and scratch tapes start blank.
`TapeCall.words` describes this layout using the shared word-configuration interface.

The construction reuses output and input redirection, sequential composition, boundary marking,
and the shared work-head rewind. Boundary clearing is the same two-transition routine with a
blank symbol. Its complete bound is `cost + result.length + 6`; no buffer preparation or
head restoration is omitted. Together with `restoreWork`, this gives arbitrary polynomial-time
functions the interface needed for calls inside bounded loops.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.TapeCall

variable {k : ℕ} {State : Type} {outerInput : List Bool}

/-- Scratch words, result buffer, input buffer, and a blank temporary flag. -/
def words (k : ℕ) (input result : List Bool) : Fin (k + 3) → List Bool :=
  Fin.lastCases [] (Fin.lastCases input (Fin.lastCases result (fun _ => [])))

/-- The intermediate call layout, with a result frontier and an optional boundary marker. -/
def config (input outerInput : List Bool) (state : Option State) (result : List Bool)
    (position : ℤ) (flag : Option Bool) (output : List Bool) :
    Cfg (k + 3) Bool State outerInput where
  state := state
  inputPos := 1
  workTapes := Fin.lastCases (Function.update (fun _ => none) (-1) flag)
    (Fin.lastCases (tapeOfList input) (Fin.lastCases (tapeOfList result) (fun _ _ => none)))
  workTapePos := Fin.lastCases 0 (Fin.lastCases 0 (Fin.lastCases position (fun _ => 0)))
  output := output

/-- The result buffer immediately follows the source scratch tapes. -/
def outputTape (k : ℕ) : Fin (k + 3) := (Fin.last k).castSucc.castSucc

/-- A returned call is again in the shared word-holding normal form. -/
theorem config_words (input result output : List Bool) (state : Option State) :
    config (k := k) input outerInput state result 0 none output =
      wordsCfg outerInput state (words k input result) output := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | last => simp [config, wordsCfg, words]
  | cast i =>
    induction i using Fin.lastCases with
    | last => simp [config, wordsCfg, words]
    | cast i =>
      induction i using Fin.lastCases <;> simp [config, wordsCfg, words]

private theorem config_inCfg (input result output : List Bool) (state : Option State) :
    config (k := k) input outerInput state result result.length (some true) output =
      inCfg true ((outCfg (wordsCfg input state (fun _ : Fin k => []) result)).withOutput output)
        outerInput := by
  have hcast (i : Fin (k + 1)) : i.castAdd 2 = i.castSucc.castSucc := rfl
  have hzero : Fin.natAdd (k + 1) (0 : Fin 2) = (Fin.last (k + 1)).castSucc := rfl
  have hone : Fin.natAdd (k + 1) (1 : Fin 2) = Fin.last (k + 2) := rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    induction i using (Fin.addCases (m := k + 1) (n := 2)) with
  | left i =>
    induction i using Fin.lastCases <;>
      simp only [config, inCfg, outCfg, Cfg.withOutput, wordsCfg, Fin.append_left,
        Fin.lastCases_last, Fin.lastCases_castSucc] <;>
      simp [hcast]
  | right i =>
    rcases (show i = 0 ∨ i = 1 by lia) with rfl | rfl <;>
      simp only [config, inCfg, outCfg, Cfg.withOutput, wordsCfg, Fin.append_right] <;>
      simp [hzero, hone]

private theorem runFrom_setBoundary (input result output : List Bool) (state : Option State)
    (position : ℤ) (flag symbol : Option Bool) :
    (PrepareInput.setBoundary (k + 2) symbol).runFrom
      ((config (k := k) input outerInput state result position flag output).withState (some false))
      2 =
      config input outerInput none result position symbol output := by
  rw [PrepareInput.runFrom_setBoundary _ _ (by simp [config])]
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  induction i using Fin.lastCases <;>
    simp [config]

private theorem runFrom_rewind (input result output : List Bool) (state : Option State)
    (flag : Option Bool) :
    ((rewindWork Bool).extendTapes (tapeEmb (outputTape k))).runFrom
      ((config (k := k) input outerInput state result result.length flag output).withState
        (some ((rewindWork Bool).extendTapes (tapeEmb (outputTape k))).q₀)) (result.length + 2) =
      config input outerInput none result 0 flag output := by
  have hhead (position : ℤ) :
      (config (k := k) input outerInput state result position flag output).workTapePos =
        Function.update (fun _ => 0) (outputTape k) position := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [config, outputTape, Fin.ext_iff]
    | cast i =>
      induction i using Fin.lastCases with
      | last => simp [config, outputTape, Fin.ext_iff]
      | cast i =>
        induction i using Fin.lastCases with
        | last => simp [config, outputTape]
        | cast i => simp [config, outputTape, Fin.ext_iff,
            Nat.ne_of_lt i.isLt]
  have htape :
      (config (k := k) input outerInput state result result.length flag output).workTapes
        (outputTape k) = tapeOfList result := by simp [config, outputTape]
  have hrun := runFrom_rewindWork_none_tapeEmb (1 : Fin (outerInput.length + 2))
    (config (k := k) input outerInput state result result.length flag output).workTapes
    (fun _ => 0) output htape (p := result.length) le_rfl
  rw [← hhead] at hrun
  convert hrun using 1
  · rfl
  · refine Cfg.ext rfl rfl rfl ?_ rfl
    exact hhead 0

private theorem runFrom_simulation (tm : MultiTapeTM k Bool State) (input result output : List Bool)
    (cost : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    tm.outputToTape.inputFromTape.runFrom
      (config input outerInput (some tm.q₀) [] 0 (some true) output) cost =
        config input outerInput none result result.length (some true) output := by
  change tm.outputToTape.inputFromTape.runFrom
    (config input outerInput (some tm.q₀) [] ([] : List Bool).length (some true) output) cost = _
  rw [config_inCfg, runFrom_inCfg, runFrom_outputToTape_withOutput, runFrom_outCfg, h,
    ← config_inCfg]

end Turing.MultiTapeTM.TapeCall

namespace Turing.MultiTapeTM

variable {k : ℕ} {State : Type} {outerInput : List Bool}

/-- Invoke a restoring machine using work-tape buffers for its input and result. -/
def tapeCall (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + 3) Bool (Bool ⊕ (State ⊕ (RewindWorkState ⊕ Bool))) :=
  (PrepareInput.setBoundary (k + 2) (some true)).seq
    (tm.outputToTape.inputFromTape.seq
      (((rewindWork Bool).extendTapes (tapeEmb (TapeCall.outputTape k))).seq
        (PrepareInput.setBoundary (k + 2) none)))

/-- A restoring subroutine produces a buffered result with every head reset, preserving the
external output. -/
theorem runFrom_tapeCall (tm : MultiTapeTM k Bool State) (input result output : List Bool)
    (cost : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    tm.tapeCall.runFrom
      (wordsCfg outerInput (some tm.tapeCall.q₀) (TapeCall.words k input []) output)
      (cost + result.length + 6) =
      wordsCfg outerInput none (TapeCall.words k input result) output := by
  have hprepare := TapeCall.runFrom_setBoundary (k := k) (outerInput := outerInput)
    input [] output (some false) 0 none (some true)
  have hsimulate := TapeCall.runFrom_simulation (outerInput := outerInput) tm input result output
    cost h
  have hrewind := TapeCall.runFrom_rewind (k := k) (outerInput := outerInput)
    input result output (none : Option State) (some true)
  have hclear := TapeCall.runFrom_setBoundary (k := k) (outerInput := outerInput)
    input result output (none : Option RewindWorkState) 0 (some true) none
  have htail := runFrom_seq hrewind rfl hclear rfl
  have hmiddle :=
    runFrom_seq hsimulate rfl
      (show (((rewindWork Bool).extendTapes (tapeEmb (TapeCall.outputTape k))).seq
          (PrepareInput.setBoundary (k + 2) none)).runFrom
        ((TapeCall.config (k := k) input outerInput (none : Option State) result result.length
          (some true) output).withState
            (some (((rewindWork Bool).extendTapes (tapeEmb (TapeCall.outputTape k))).seq
              (PrepareInput.setBoundary (k + 2) none)).q₀)) (result.length + 2 + 2) =
        TapeCall.config input outerInput none result 0 none output from by
          simpa [Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState, Cfg.withState,
            TapeCall.config, seq] using htail) rfl
  have hmain :=
    runFrom_seq hprepare rfl
      (show (tm.outputToTape.inputFromTape.seq
          (((rewindWork Bool).extendTapes (tapeEmb (TapeCall.outputTape k))).seq
            (PrepareInput.setBoundary (k + 2) none))).runFrom
        ((TapeCall.config (k := k) input outerInput (none : Option Bool) [] 0 (some true)
          output).withState (some (tm.outputToTape.inputFromTape.seq
          (((rewindWork Bool).extendTapes (tapeEmb (TapeCall.outputTape k))).seq
            (PrepareInput.setBoundary (k + 2) none))).q₀))
        (cost + (result.length + 2 + 2)) =
        TapeCall.config input outerInput none result 0 none output from by
          simpa [Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState, Cfg.withState,
            TapeCall.config, seq, inputFromTape, outputToTape] using hmiddle) rfl
  have htime : 2 + (cost + (result.length + 2 + 2)) = cost + result.length + 6 := by lia
  simpa [tapeCall, ← TapeCall.config_words, Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState,
    Cfg.withState, TapeCall.config, seq, htime] using hmain

end Turing.MultiTapeTM
