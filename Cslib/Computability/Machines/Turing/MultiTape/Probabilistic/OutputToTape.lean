/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Simulation
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Buffering an oracle machine's output

The machine writes its result to a fresh last work tape, whose head remains at the end of the
written word. The real output stays empty. Every source transition and oracle interaction is
preserved, so the buffered word can subsequently be used as another machine's input.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} {input : List Bool}

namespace OutputToTape

/-- Redirect an emitted bit to the fresh work tape. -/
def action (a : Turing.Action k Bool State) : Turing.Action (k + 1) Bool State where
  inputTape := a.inputTape
  workTapes := Fin.lastCases
    (match a.output with
      | none => (none, 0)
      | some bit => (some (some bit), 1)) a.workTapes
  output := none
  state := a.state

/-- The buffered configuration retains both oracle communication tapes. -/
def config (cfg : Config k Bool State Oracle input) : Config (k + 1) Bool State Oracle input :=
  { cfg with tapes := MultiTapeTM.outCfg cfg.tapes }

@[simp] theorem config_state (cfg : Config k Bool State Oracle input) :
    (config cfg).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_inputSymbol (cfg : Config k Bool State Oracle input) :
    (config cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k Bool State Oracle input) (i : Fin k) :
    (config cfg).tapes.workTapeSymbols i.castSucc = cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.outCfg_workTapeSymbols_castSucc cfg.tapes i

@[simp] theorem config_answerSymbols (cfg : Config k Bool State Oracle input) :
    (config cfg).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem config_channels (cfg : Config k Bool State Oracle input) :
    (config cfg).channels = cfg.channels := rfl

/-- A local output step appends exactly one cell at the write frontier. -/
theorem step_config (cfg : Config k Bool State Oracle input) (a : Turing.Action k Bool State)
    (bit : Oracle → Option Bool) (move : Oracle → SignType) :
    (config cfg).step (action a) bit move = config (cfg.step a bit move) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | cast i => simp [config, action, Config.step, Action.apply, MultiTapeTM.outCfg]
  | last =>
    cases h : a.output <;>
      simp [config, action, Config.step, Action.apply, MultiTapeTM.outCfg, h,
        tapeOfList_append_single, SignType.cast]

variable [DecidableEq Oracle]

theorem receive_config (cfg : Config k Bool State Oracle input)
    (oracle : Oracle) (next : State) (answer : List Bool) :
    (config cfg).receive oracle next answer = config (cfg.receive oracle next answer) := rfl

end OutputToTape

/-- Buffer all output on a fresh work tape without changing the source's oracle interaction. -/
@[simps! initial] def outputToTape (machine : MultiTapePTM k Bool State Oracle) :
    MultiTapePTM (k + 1) Bool State Oracle :=
  { initial := machine.initial
    tr := fun state symbol work answer coin =>
    match machine.tr state symbol (fun i => work i.castSucc) answer coin with
    | .step action bit move => .step (OutputToTape.action action) bit move
    | .query oracle next => .query oracle next }

variable [DecidableEq Oracle]

/-- Output redirection preserves the entire program and accounts for every buffered bit. -/
theorem runConfigFrom_outputToTape (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) :
    machine.outputToTape.runConfigFrom fuel (OutputToTape.config cfg) =
      OutputToTape.config <$> machine.runConfigFrom fuel cfg := by
  refine runConfigFrom_simulation machine machine.outputToTape OutputToTape.config ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, OutputToTape.config_state, hs, OutputToTape.config_inputSymbol,
      OutputToTape.config_workTapeSymbols, OutputToTape.config_answerSymbols, outputToTape,
      map_bind]
    apply bind_congr
    intro bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [OutputToTape.step_config, OutputToTape.receive_config]

omit [DecidableEq Oracle] in
/-- Buffering starts on an ordinary blank work tape; no auxiliary word is supplied. -/
theorem initialConfig_outputToTape (machine : MultiTapePTM k Bool State Oracle)
    (input : List Bool) :
    machine.outputToTape.initialConfig input =
      OutputToTape.config (machine.initialConfig input) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [initialConfig, OutputToTape.config, MultiTapeTM.outCfg, Cfg.init]

end Turing.MultiTapePTM
