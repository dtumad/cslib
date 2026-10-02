/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeUpdate
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.UnaryRepeat
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputPrefix

/-!
# Machines for bounded iteration

This module collects the machine construction behind the polynomial-time iteration rule.
Initialization and the unary iteration count are computed by restoring subroutines.
Every iteration replaces the current word, and the result is finally copied to the output.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.Iteration

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Run a restoring subroutine, buffer its output, and rewind the resulting word. -/
def buffer (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + 1) Bool (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq (rewindLast k)

theorem runFrom_buffer (tm : MultiTapeTM k Bool State) (result output : List Bool) (cost : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    (buffer tm).runFrom (wordsCfg input (some (buffer tm).q₀) (fun _ => []) output)
      (cost + result.length + 2) =
      wordsCfg input none (Fin.lastCases result (fun _ => [])) output := by
  have hwrite := runFrom_outCfg tm (wordsCfg input (some tm.q₀) (fun _ => []) []) cost
  rw [h] at hwrite
  have hrewind := runFrom_rewindLast (outCfg (wordsCfg input (none : Option State)
    (fun _ : Fin k => []) result)) result (by simp) (by simp)
  have hmain := runFrom_seq hwrite rfl hrewind rfl
  have hzero : (buffer tm).runFrom
      (wordsCfg input (some (buffer tm).q₀) (fun _ => []) [])
      (cost + result.length + 2) =
      wordsCfg input none (Fin.lastCases result (fun _ => [])) [] := by
    convert hmain using 1
    · congr 1
      refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
        induction i using Fin.lastCases <;>
        simp [wordsCfg, Sequential.leftCfg, Cfg.mapState, outCfg]
    · refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
        induction i using Fin.lastCases <;>
        simp [wordsCfg, Sequential.rightCfg, Cfg.mapState, RewindLast.config, Cfg.withState,
          outCfg]
  have hprefix := congrArg (Cfg.prependOutput · output) hzero
  rw [← runFrom_prependOutput] at hprefix
  simpa [Cfg.prependOutput, wordsCfg] using hprefix

/-- Copy a selected word tape to the output. -/
def emit (tape : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work tape with
    | some bit =>
      { inputTape := 0, workTapes := fun i => (none, if i = tape then 1 else 0),
        output := some bit, state := some () }
    | none =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

private def emitConfig (tape : Fin k) (words : Fin k → List Bool) (output : List Bool)
    (state : Option Unit) (position : ℕ) : Cfg k Bool Unit input :=
  { wordsCfg input state words (output ++ (words tape).take position) with
    workTapePos := Function.update (fun _ => 0) tape position }

private theorem step_emit (tape : Fin k) (words : Fin k → List Bool) (output : List Bool)
    (position : ℕ) (h : position < (words tape).length) :
    (emit tape).step (emitConfig (input := input) tape words output (some ()) position) =
      emitConfig tape words output (some ()) (position + 1) := by
  have hread : (emitConfig (input := input) tape words output (some ()) position).workTapeSymbols
      tape = some (words tape)[position] := by
    simp [emitConfig, Cfg.workTapeSymbols, List.getElem?_eq_getElem h]
  rw [step_apply_of_state rfl]
  simp only [emit, hread]
  refine Cfg.ext rfl (by simp [Action.apply, emitConfig]) rfl ?_ ?_
  · funext i
    by_cases hi : i = tape <;> simp [Action.apply, emitConfig, hi]
  · change (output ++ (words tape).take position) ++ [(words tape)[position]] =
      output ++ (words tape).take (position + 1)
    rw [List.take_add_one]
    simp only [List.getElem?_eq_getElem h, Option.toList_some, List.append_assoc]

private theorem runFrom_emit (tape : Fin k) (words : Fin k → List Bool) (output : List Bool) :
    (emit tape).runFrom (wordsCfg input (some ()) words output) ((words tape).length + 1) =
      emitConfig tape words output none (words tape).length := by
  have hstart : wordsCfg input (some ()) words output =
      emitConfig tape words output (some ()) 0 := by
    simp [emitConfig, wordsCfg]
  have hscan (position : ℕ) (hp : position ≤ (words tape).length) :
      (emit tape).runFrom (emitConfig (input := input) tape words output (some ()) 0) position =
        emitConfig tape words output (some ()) position := by
    induction position with
    | zero => rfl
    | succ position ih =>
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia)]
      exact step_emit tape words output position (by lia)
  rw [hstart, runFrom, Function.iterate_succ_apply', ← runFrom, hscan _ le_rfl]
  simp [step, emit, emitConfig, wordsCfg, Cfg.workTapeSymbols, Action.apply]

/-- Use the first scratch tapes and one selected buffer among the final four tapes. -/
def bufferEmbedding (k : ℕ) (slot : Fin 4) : Fin (k + 1) ↪ Fin (k + 4) where
  toFun := Fin.lastCases (Fin.natAdd k slot) (Fin.castAdd 4)
  inj' := by
    intro i j h
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have hv := congrArg Fin.val h
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_natAdd,
          Fin.val_castAdd] at hv
        lia
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have hv := congrArg Fin.val h
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_natAdd,
          Fin.val_castAdd] at hv
        lia
      | cast j =>
        apply Fin.ext
        simpa using congrArg Fin.val h

/-- Run a restoring machine into a selected buffer, preserving the other buffers. -/
def bufferAt (tm : MultiTapeTM k Bool State) (slot : Fin 4) :
    MultiTapeTM (k + 4) Bool (State ⊕ RewindWorkState) :=
  (buffer tm).extendTapes (bufferEmbedding k slot)

theorem runFrom_bufferAt (tm : MultiTapeTM k Bool State) (slot : Fin 4)
    (words : Fin (k + 4) → List Bool) (result output : List Bool) (cost : ℕ)
    (hscratch : ∀ i : Fin k, words (i.castAdd 4) = [])
    (hblank : words (Fin.natAdd k slot) = [])
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    (bufferAt tm slot).runFrom
      (wordsCfg input (some (bufferAt tm slot).q₀) words output)
      (cost + result.length + 2) =
      wordsCfg input none (Function.update words (Fin.natAdd k slot) result) output := by
  have hinitial : words ∘ bufferEmbedding k slot = fun _ => [] := by
    funext i
    induction i using Fin.lastCases <;>
      simp [bufferEmbedding, hscratch, hblank]
  have hfinal : Function.update words (Fin.natAdd k slot) result ∘ bufferEmbedding k slot =
      Fin.lastCases result (fun _ => []) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [bufferEmbedding]
    | cast i =>
      have hne : i.castAdd 4 ≠ Fin.natAdd k slot := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        lia
      simp [bufferEmbedding, hne, hscratch]
  apply runFrom_extendTapes_words
  · simpa only [hinitial, hfinal] using runFrom_buffer tm result output cost h
  · intro i hi
    apply Function.update_of_ne
    intro he
    apply hi
    exact ⟨Fin.last k, by simpa [bufferEmbedding] using he.symm⟩

/-- The argument and the unary counter, with blank scratch and temporary buffers. -/
def words (k : ℕ) (argument : List Bool) (count : ℕ) : Fin (k + 4) → List Bool :=
  Fin.lastCases (List.replicate count true) (TapeCall.words k argument [])

private theorem words_scratch (argument : List Bool) (count : ℕ) (i : Fin k) :
    words k argument count (i.castAdd 4) = [] := by
  change words k argument count i.castSucc.castSucc.castSucc.castSucc = []
  simp [words, TapeCall.words]

private theorem words_buffer (argument : List Bool) (count : ℕ) (slot : Fin 4) :
    words k argument count (Fin.natAdd k slot) =
      ![[], argument, [], List.replicate count true] slot := by
  rcases (show slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 by lia) with rfl | rfl | rfl | rfl
  · change words k argument count (Fin.last k).castSucc.castSucc.castSucc = _
    simp [words, TapeCall.words]
  · change words k argument count (Fin.last (k + 1)).castSucc.castSucc = _
    simp [words, TapeCall.words]
  · change words k argument count (Fin.last (k + 2)).castSucc = _
    simp [words, TapeCall.words]
  · change words k argument count (Fin.last (k + 3)) = _
    simp [words]

private theorem words_zero : words k [] 0 = fun _ => [] := by
  funext i
  induction i using (Fin.addCases (m := k) (n := 4)) with
  | left i => exact words_scratch [] 0 i
  | right i =>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by lia) with rfl | rfl | rfl | rfl <;>
      simp [words_buffer]

private theorem words_update_argument (argument : List Bool) (count : ℕ) :
    Function.update (words k [] count) (Fin.natAdd k (1 : Fin 4)) argument =
      words k argument count := by
  funext i
  induction i using (Fin.addCases (m := k) (n := 4)) with
  | left i =>
    have hne : i.castAdd 4 ≠ Fin.natAdd k (1 : Fin 4) := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      lia
    simp [Function.update_of_ne hne, words_scratch]
  | right i =>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by lia) with rfl | rfl | rfl | rfl <;>
      simp [words_buffer, Fin.ext_iff]

private theorem words_update_count (argument : List Bool) (count : ℕ) :
    Function.update (words k argument 0) (Fin.natAdd k (3 : Fin 4)) (List.replicate count true) =
      words k argument count := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    change Function.update (words k argument 0) (Fin.last (k + 3))
      (List.replicate count true) (Fin.last (k + 3)) = _
    simp [words]
  | cast i =>
    change Function.update (words k argument 0) (Fin.last (k + 3))
      (List.replicate count true) i.castSucc = _
    simp [words]

/-- Initialize the state and loop count, run the changing-state loop, then output its result. -/
def machine {InitState CountState : Type}
    (initializer : MultiTapeTM k Bool InitState) (counter : MultiTapeTM k Bool CountState)
    (step : MultiTapeTM k Bool State) :
    MultiTapeTM (k + 4) Bool
      ((((InitState ⊕ RewindWorkState) ⊕ (CountState ⊕ RewindWorkState)) ⊕
        (((Bool ⊕ (State ⊕ (RewindWorkState ⊕ Bool))) ⊕ Bool) ⊕ Fin 3)) ⊕ Unit) :=
  (((bufferAt initializer 1).seq (bufferAt counter 3)).seq step.tapeUpdate.repeatUnary).seq
    (emit (Fin.natAdd k (1 : Fin 4)))

/-- The complete iteration machine, including initialization, counting, every update, and output.
Only the words actually reached by the loop need a common size and step-time bound. -/
theorem machine_spec {InitState CountState : Type}
    (initializer : MultiTapeTM k Bool InitState) (counter : MultiTapeTM k Bool CountState)
    (step : MultiTapeTM k Bool State) (values : ℕ → List Bool)
    (count initialTime countTime stepTime size : ℕ)
    (hinitial : initializer.runFrom
      (wordsCfg input (some initializer.q₀) (fun _ => []) []) initialTime =
        wordsCfg input none (fun _ => []) (values 0))
    (hcount : counter.runFrom (wordsCfg input (some counter.q₀) (fun _ => []) []) countTime =
      wordsCfg input none (fun _ => []) (List.replicate count true))
    (hstep : ∀ index < count,
      step.runFrom (wordsCfg (values index) (some step.q₀) (fun _ => []) []) stepTime =
        wordsCfg (values index) none (fun _ => []) (values (index + 1)))
    (hsize : ∀ index ≤ count, (values index).length ≤ size) :
    let compiled := machine initializer counter step
    let cfg := compiled.runFrom (compiled.initCfg input)
      (initialTime + countTime + 2 * size + count * (stepTime + 3 * size + 11) + count + 7)
    cfg.state = none ∧ cfg.output = values count := by
  have hprepare : (bufferAt initializer 1).runFrom
      (wordsCfg input (some (bufferAt initializer 1).q₀) (words k [] 0) [])
      (initialTime + (values 0).length + 2) =
      wordsCfg input none (words k (values 0) 0) [] := by
    simpa only [words_update_argument] using
      runFrom_bufferAt initializer 1 (words k [] 0) (values 0) [] initialTime
        (words_scratch [] 0) (by simp [words_buffer]) hinitial
  have hcounter : (bufferAt counter 3).runFrom
      (wordsCfg input (some (bufferAt counter 3).q₀) (words k (values 0) 0) [])
      (countTime + count + 2) =
      wordsCfg input none (words k (values 0) count) [] := by
    simpa only [words_update_count, List.length_replicate] using
      runFrom_bufferAt counter 3 (words k (values 0) 0) (List.replicate count true) [] countTime
        (words_scratch (values 0) 0) (by simp [words_buffer]) hcount
  have hbody (index : ℕ) (hi : index < count) :
      step.tapeUpdate.runFrom
        (wordsCfg input (some step.tapeUpdate.q₀) (TapeCall.words k (values index) []) [])
        (stepTime + 3 * size + 8) =
        wordsCfg input none (TapeCall.words k (values (index + 1)) []) [] := by
    have hrun := runFrom_tapeUpdate (outerInput := input) step
      (values index) (values (index + 1)) [] stepTime (hstep index hi)
    have hbound : stepTime + (values (index + 1)).length +
        2 * max (values (index + 1)).length (values index).length + 8 ≤
        stepTime + 3 * size + 8 := by
      have := hsize index (by lia)
      have := hsize (index + 1) (by lia)
      lia
    rw [runFrom_eq_of_halt _ _ hbound (by rw [hrun]; rfl)]
    exact hrun
  have hloop : step.tapeUpdate.repeatUnary.runFrom
      (wordsCfg input (some step.tapeUpdate.repeatUnary.q₀) (words k (values 0) count) [])
      (count * (stepTime + 3 * size + 11) + 2) =
      wordsCfg input none (words k (values count) count) [] := by
    change step.tapeUpdate.repeatUnary.runFrom
      (wordsCfg input (some step.tapeUpdate.repeatUnary.q₀)
        (Fin.lastCases (List.replicate count true) (TapeCall.words k (values 0) [])) []) _ =
      wordsCfg input none
        (Fin.lastCases (List.replicate count true) (TapeCall.words k (values count) [])) []
    simpa only [show stepTime + 3 * size + 8 + 3 = stepTime + 3 * size + 11 by lia] using
      runFrom_repeatUnary_states step.tapeUpdate (fun index => TapeCall.words k (values index) [])
        (fun _ => []) (stepTime + 3 * size + 8) count hbody
  have hsetup := runFrom_seq_words _ _ _ _ _ _ _ _ _ _ hprepare hcounter
  have hsteps := runFrom_seq_words _ _ _ _ _ _ _ _ _ _ hsetup hloop
  have hemit := runFrom_emit (input := input) (Fin.natAdd k (1 : Fin 4))
    (words k (values count) count) []
  simp only [words_buffer, Matrix.cons_val_one] at hemit
  have hmain := runFrom_seq hsteps rfl hemit rfl
  have hrun : (machine initializer counter step).runFrom
      (wordsCfg input (some (machine initializer counter step).q₀) (fun _ => []) [])
      (initialTime + (values 0).length + 2 + (countTime + count + 2) +
        (count * (stepTime + 3 * size + 11) + 2) + ((values count).length + 1)) =
      Sequential.rightCfg (emitConfig (Fin.natAdd k (1 : Fin 4))
        (words k (values count) count) [] none (values count).length) := by
    simpa [machine, words_zero, Sequential.leftCfg, seq] using hmain
  dsimp only
  simp only [initCfg, Cfg.init_eq_wordsCfg]
  have hbound : initialTime + (values 0).length + 2 + (countTime + count + 2) +
      (count * (stepTime + 3 * size + 11) + 2) + ((values count).length + 1) ≤
      initialTime + countTime + 2 * size + count * (stepTime + 3 * size + 11) + count + 7 := by
    have := hsize 0 (by lia)
    have := hsize count le_rfl
    lia
  rw [runFrom_eq_of_halt _ _ hbound (by rw [hrun]; rfl), hrun]
  simp [Sequential.rightCfg, Cfg.mapState, emitConfig, words_buffer]

end Turing.MultiTapeTM.Iteration
