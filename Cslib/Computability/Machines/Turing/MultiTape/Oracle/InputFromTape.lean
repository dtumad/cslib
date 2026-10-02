/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Running an oracle machine on a buffered input

The two fresh work tapes hold the virtual input and its left-boundary marker. This reuses the
deterministic machine's clamped-input simulation. All random choices and oracle interactions
remain unchanged, and the outer machine's real input is never moved or inspected.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State : Type} {input : List Bool}

namespace InputFromTape

/-- Move the virtual input and boundary heads together, clamping at either end. -/
def action (a : Action k Bool State) (symbol flag : Option Bool) : Action (k + 2) Bool State :=
  { a with
    inputTape := 0
    workTapes := Fin.append a.workTapes
      (fun _ => (none, MultiTapeTM.clampMove symbol flag a.inputTape)) }

/-- Embed the source input on work tapes while retaining its oracle communication tapes. -/
def config (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    Config (k + 2) State outerInput :=
  { cfg with
    tapes := { MultiTapeTM.inCfg true cfg.tapes outerInput with inputPos := outerPosition } }

@[simp] theorem config_state (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2))
    (i : Fin k) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (i.castAdd 2) =
      cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.inCfg_workTapeSymbols_castAdd (outerInput := outerInput) cfg.tapes i

@[simp] theorem config_inputSymbol (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 0) =
      cfg.tapes.inputSymbol := by
  exact MultiTapeTM.inCfg_workTapeSymbols_vip (outerInput := outerInput) cfg.tapes

@[simp] theorem config_flagSymbol (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 1) =
      if cfg.tapes.inputPos.val = 0 then some true else none := by
  exact MultiTapeTM.inCfg_workTapeSymbols_flag (outerInput := outerInput) cfg.tapes

@[simp] theorem config_answerSymbol (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem config_queryBuffer (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem config_output (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.output = cfg.tapes.output := rfl

theorem step_config (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2))
    (a : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (config cfg outerInput outerPosition).step
        (action a cfg.tapes.inputSymbol (if cfg.tapes.inputPos.val = 0 then some true else none))
        bit move = config (cfg.step a bit move) outerInput outerPosition := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl (by simp [config, Config.step, action, Action.apply, MultiTapeTM.inCfg])
    ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases <;>
    simp [config, Config.step, action, Action.apply, MultiTapeTM.inCfg,
      MultiTapeTM.val_moveInputPos_sub_one_eq_clampMove true]

theorem receive_config (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2))
    (next : State) (answer : List Bool) :
    (config cfg outerInput outerPosition).receive next answer =
      config (cfg.receive next answer) outerInput outerPosition := rfl

end InputFromTape

/-- Read the input from two fresh work tapes: a word and its boundary marker. -/
@[simps! initial] def inputFromTape (machine : OracleTM k State) : OracleTM (k + 2) State :=
  Turing.OracleTM.mk (machine.initial) fun state _ work answer coin =>
    match machine.transition state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2))
        answer coin with
    | .step action bit move => .step
      (InputFromTape.action action (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1))) bit move
    | .query next => .query next

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem inputFromTape_transition (machine : OracleTM k State) :
    (inputFromTape machine).transition =
  fun state _ work answer coin =>
    match machine.transition state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2))
        answer coin with
    | .step action bit move => .step
      (InputFromTape.action action (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1))) bit move
    | .query next => .query next := by
  funext state symbol work answer coin
  simp only [inputFromTape, Turing.OracleTM.transition_mk]

/-- Virtual input preserves the complete clocked program, including oracle effects. -/
theorem runConfigFrom_inputFromTape (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runConfigFrom fuel (InputFromTape.config cfg outerInput outerPosition) =
      (fun final => InputFromTape.config final outerInput outerPosition) <$>
        machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, InputFromTape.config_state, hs,
        InputFromTape.config_workTapeSymbols,
        InputFromTape.config_inputSymbol, InputFromTape.config_flagSymbol,
        InputFromTape.config_answerSymbol, inputFromTape_transition, map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | step action bit move => simp only [InputFromTape.step_config, ih]
      | query next => simp [InputFromTape.receive_config, ih, map_bind]

/-- The buffered input has exactly the source's output program. -/
theorem runFrom_inputFromTape (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (outerInput : List Bool)
    (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runFrom fuel (InputFromTape.config cfg outerInput outerPosition) =
      machine.runFrom fuel cfg := by
  rw [runFrom_eq_map_runConfigFrom, runConfigFrom_inputFromTape, ← comp_map]
  exact (runFrom_eq_map_runConfigFrom machine fuel cfg).symm

end Turing.OracleTM
