/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Buffering an oracle machine's output

The machine writes its result to a fresh last work tape, whose head remains at the end of the
written word. The real output stays empty. Every source transition and oracle interaction is
preserved, so the buffered word can subsequently be used as another machine's input.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State : Type} {input : List Bool}

namespace OutputToTape

/-- Redirect an emitted bit to the fresh work tape. -/
def action (a : Action k Bool State) : Action (k + 1) Bool State where
  inputTape := a.inputTape
  workTapes := Fin.lastCases
    (match a.output with
      | none => (none, 0)
      | some bit => (some (some bit), 1)) a.workTapes
  output := none
  state := a.state

/-- The buffered configuration retains both oracle communication tapes. -/
def config (cfg : Config k State input) : Config (k + 1) State input :=
  { cfg with tapes := MultiTapeTM.outCfg cfg.tapes }

@[simp] theorem config_state (cfg : Config k State input) :
    (config cfg).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_inputSymbol (cfg : Config k State input) :
    (config cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k State input) (i : Fin k) :
    (config cfg).tapes.workTapeSymbols i.castSucc = cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.outCfg_workTapeSymbols_castSucc cfg.tapes i

@[simp] theorem config_answerSymbol (cfg : Config k State input) :
    (config cfg).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem config_queryBuffer (cfg : Config k State input) :
    (config cfg).queryBuffer = cfg.queryBuffer := rfl

/-- A local output step appends exactly one cell at the write frontier. -/
theorem step_config (cfg : Config k State input) (a : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (config cfg).step (action a) bit move = config (cfg.step a bit move) := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | cast i => simp [config, action, Config.step, Action.apply, MultiTapeTM.outCfg]
  | last =>
    cases h : a.output <;>
      simp [config, action, Config.step, Action.apply, MultiTapeTM.outCfg, h,
        tapeOfList_append_single, SignType.cast]

theorem receive_config (cfg : Config k State input) (next : State) (answer : List Bool) :
    (config cfg).receive next answer = config (cfg.receive next answer) := rfl

end OutputToTape

/-- Buffer all output on a fresh work tape without changing the source's oracle interaction. -/
@[simps! initial] def outputToTape (machine : OracleTM k State) : OracleTM (k + 1) State :=
  Turing.OracleTM.mk (machine.initial) fun state symbol work answer coin =>
    match machine.transition state symbol (fun i => work i.castSucc) answer coin with
    | .step action bit move => .step (OutputToTape.action action) bit move
    | .query next => .query next

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem outputToTape_transition (machine : OracleTM k State) :
    (outputToTape machine).transition =
  fun state symbol work answer coin =>
    match machine.transition state symbol (fun i => work i.castSucc) answer coin with
    | .step action bit move => .step (OutputToTape.action action) bit move
    | .query next => .query next := by
  funext state symbol work answer coin
  simp only [outputToTape, Turing.OracleTM.transition_mk]

/-- Output redirection preserves the entire program and accounts for every buffered bit. -/
theorem runConfigFrom_outputToTape (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) :
    machine.outputToTape.runConfigFrom fuel (OutputToTape.config cfg) =
      OutputToTape.config <$> machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, OutputToTape.config_state, hs, OutputToTape.config_inputSymbol,
        OutputToTape.config_workTapeSymbols, OutputToTape.config_answerSymbol,
        outputToTape_transition, map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin <;>
        simp [OutputToTape.step_config, OutputToTape.receive_config, ih, map_bind]

/-- Buffering starts on an ordinary blank work tape; no auxiliary word is supplied. -/
theorem initialConfig_outputToTape (machine : OracleTM k State) (input : List Bool) :
    machine.outputToTape.initialConfig input =
      OutputToTape.config (machine.initialConfig input) := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [initialConfig, OutputToTape.config, MultiTapeTM.outCfg, Cfg.init]

end Turing.OracleTM
