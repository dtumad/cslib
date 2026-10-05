/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Simulation
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Running an oracle machine on a buffered input

The two fresh work tapes hold the virtual input and its left-boundary marker. This reuses the
deterministic machine's clamped-input simulation. All random choices and oracle interactions
remain unchanged, and the outer machine's real input is never moved or inspected.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} {input : List Bool}

namespace InputFromTape

/-- Move the virtual input and boundary heads together, clamping at either end. -/
def action (a : Turing.Action k Bool State) (symbol flag : Option Bool) :
    Turing.Action (k + 2) Bool State :=
  { a with
    inputTape := 0
    workTapes := Fin.append a.workTapes
      (fun _ => (none, MultiTapeTM.clampMove symbol flag a.inputTape)) }

/-- Embed the source input on work tapes while retaining its oracle communication tapes. -/
def config (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    Config (k + 2) Bool State Oracle outerInput :=
  { cfg with
    tapes := { MultiTapeTM.inCfg true cfg.tapes outerInput with inputPos := outerPosition } }

@[simp] theorem config_state (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2))
    (i : Fin k) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (i.castAdd 2) =
      cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.inCfg_workTapeSymbols_castAdd (outerInput := outerInput) cfg.tapes i

@[simp] theorem config_inputSymbol (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 0) =
      cfg.tapes.inputSymbol := by
  exact MultiTapeTM.inCfg_workTapeSymbols_vip (outerInput := outerInput) cfg.tapes

@[simp] theorem config_flagSymbol (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.workTapeSymbols (Fin.natAdd k 1) =
      if cfg.tapes.inputPos.val = 0 then some true else none := by
  exact MultiTapeTM.inCfg_workTapeSymbols_flag (outerInput := outerInput) cfg.tapes

@[simp] theorem config_answerSymbols (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem config_channels (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).channels = cfg.channels := rfl

@[simp] theorem config_output (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    (config cfg outerInput outerPosition).tapes.output = cfg.tapes.output := rfl

theorem step_config (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2))
    (a : Turing.Action k Bool State) (bit : Oracle → Option Bool) (move : Oracle → SignType) :
    (config cfg outerInput outerPosition).step
        (action a cfg.tapes.inputSymbol (if cfg.tapes.inputPos.val = 0 then some true else none))
        bit move = config (cfg.step a bit move) outerInput outerPosition := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl (by simp [config, Config.step, action, Action.apply, MultiTapeTM.inCfg])
    ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases <;>
    simp [config, Config.step, action, Action.apply, MultiTapeTM.inCfg,
      MultiTapeTM.val_moveInputPos_sub_one_eq_clampMove true]

variable [DecidableEq Oracle]

theorem receive_config (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2))
    (oracle : Oracle) (next : State) (answer : List Bool) :
    (config cfg outerInput outerPosition).receive oracle next answer =
      config (cfg.receive oracle next answer) outerInput outerPosition := rfl

end InputFromTape

/-- Read the input from two fresh work tapes: a word and its boundary marker. -/
@[simps! initial] def inputFromTape (machine : MultiTapePTM k Bool State Oracle) :
    MultiTapePTM (k + 2) Bool State Oracle :=
  { initial := machine.initial
    tr := fun state _ work answer coin =>
    match machine.tr state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2))
        answer coin with
    | .step action bit move => .step
      (InputFromTape.action action (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1))) bit move
    | .query oracle next => .query oracle next }

variable [DecidableEq Oracle]

/-- Virtual input preserves the complete clocked program, including oracle effects. -/
theorem runConfigFrom_inputFromTape (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runConfigFrom fuel (InputFromTape.config cfg outerInput outerPosition) =
      (fun final => InputFromTape.config final outerInput outerPosition) <$>
        machine.runConfigFrom fuel cfg := by
  refine runConfigFrom_simulation machine machine.inputFromTape
    (fun cfg => InputFromTape.config cfg outerInput outerPosition) ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, InputFromTape.config_state, hs, InputFromTape.config_workTapeSymbols,
      InputFromTape.config_inputSymbol, InputFromTape.config_flagSymbol,
      InputFromTape.config_answerSymbols, inputFromTape, map_bind]
    apply bind_congr
    intro bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      with
    | step action symbol move =>
      simpa only [map_pure, pure_bind] using congrArg pure
        (InputFromTape.step_config cfg outerInput outerPosition action symbol move)
    | query oracle next => simp [InputFromTape.receive_config]

/-- The buffered input has exactly the source's output program. -/
theorem runFrom_inputFromTape (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input)
    (outerInput : List Bool) (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runFrom fuel (InputFromTape.config cfg outerInput outerPosition) =
      machine.runFrom fuel cfg := by
  simp only [runFrom, runConfigFrom_inputFromTape, ← comp_map]
  rfl

end Turing.MultiTapePTM
