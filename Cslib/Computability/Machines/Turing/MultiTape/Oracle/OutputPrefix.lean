/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle

/-!
# Retaining an existing output prefix
An oracle machine cannot read its output tape. Prepending a word to the existing output therefore
preserves its execution and oracle interactions, and prepends the same word to its final output.
These are configuration invariance lemmas: writing the prefix is separate, charged machine work.
-/

@[expose] public section

namespace Turing.OracleTM

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Change only the already written output, inserting a prefix. -/
def Config.prefixOutput (cfg : Config k State input) (pre : List Bool) : Config k State input :=
  { cfg with tapes := cfg.tapes.prependOutput pre }

@[simp] theorem Config.prefixOutput_state (cfg : Config k State input) (pre : List Bool) :
    (cfg.prefixOutput pre).tapes.state = cfg.tapes.state := rfl

@[simp] theorem Config.prefixOutput_inputSymbol (cfg : Config k State input) (pre : List Bool) :
    (cfg.prefixOutput pre).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.prefixOutput_workTapeSymbols (cfg : Config k State input)
    (pre : List Bool) :
    (cfg.prefixOutput pre).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem Config.prefixOutput_answerSymbol (cfg : Config k State input) (pre : List Bool) :
    (cfg.prefixOutput pre).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem Config.prefixOutput_queryBuffer (cfg : Config k State input) (pre : List Bool) :
    (cfg.prefixOutput pre).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem Config.prefixOutput_output (cfg : Config k State input) (pre : List Bool) :
    (cfg.prefixOutput pre).tapes.output = pre ++ cfg.tapes.output := rfl

theorem Config.step_prefixOutput (cfg : Config k State input) (pre : List Bool)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (cfg.prefixOutput pre).step action bit move =
      (cfg.step action bit move).prefixOutput pre := by
  simp only [Config.prefixOutput, Config.step, Action.apply_prependOutput]

theorem Config.receive_prefixOutput (cfg : Config k State input) (pre : List Bool)
    (next : State) (answer : List Bool) :
    (cfg.prefixOutput pre).receive next answer =
      (cfg.receive next answer).prefixOutput pre := rfl

/-- An unreadable output prefix leaves the complete execution unchanged. -/
theorem runConfigFrom_prefixOutput (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (pre : List Bool) :
    machine.runConfigFrom fuel (cfg.prefixOutput pre) =
      (fun final => final.prefixOutput pre) <$> machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, Config.prefixOutput_state, hs, Config.prefixOutput_inputSymbol,
        Config.prefixOutput_workTapeSymbols, Config.prefixOutput_answerSymbol, map_bind]
      congr 1
      funext coin
      split <;> simp [Config.step_prefixOutput, Config.receive_prefixOutput, ih, map_bind]

/-- The final word retains the same prefix. -/
theorem runFrom_prefixOutput (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (pre : List Bool) :
    machine.runFrom fuel (cfg.prefixOutput pre) =
      (pre ++ ·) <$> machine.runFrom fuel cfg := by
  simp only [runFrom_eq_map_runConfigFrom, runConfigFrom_prefixOutput, ← comp_map,
    Config.prefixOutput_output, Function.comp_def]

end Turing.OracleTM
