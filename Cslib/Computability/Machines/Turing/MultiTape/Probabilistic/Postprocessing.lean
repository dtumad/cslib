/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Mapping a probabilistic machine's output

A fixed symbol substitution changes only the write-only output tape. It preserves the clock,
control flow, and all oracle interactions, including shared private state.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {Response : Query → Type}
  {input : List Symbol}

/-- Apply a fixed function to each emitted output symbol, with no extra transitions. -/
@[simps! initial] def mapOutput (machine : MultiTapePTM k Symbol State Oracle)
    (f : Symbol → Symbol) : MultiTapePTM k Symbol State Oracle where
  initial := machine.initial
  tr state symbol work answer coin :=
    match machine.tr state symbol work answer coin with
    | .step action bit move => .step { action with output := action.output.map f } bit move
    | .query op next => .query op next

@[simp] theorem mapOutput_tr (machine : MultiTapePTM k Symbol State Oracle)
    (f : Symbol → Symbol) (state : State) (symbol : Option Symbol)
    (work : Fin k → Option Symbol) (answer : Oracle → Option Symbol) (coin : Bool) :
    (machine.mapOutput f).tr state symbol work answer coin =
      match machine.tr state symbol work answer coin with
      | .step action bit move => .step { action with output := action.output.map f } bit move
      | .query op next => .query op next := rfl

/-- Change only the already written output symbols in a complete configuration. -/
def mapOutputConfig (cfg : Config k Symbol State Oracle input) (f : Symbol → Symbol) :
    Config k Symbol State Oracle input :=
  { cfg with tapes := cfg.tapes.withOutput (cfg.tapes.output.map f) }

private theorem step_mapOutputConfig (cfg : Config k Symbol State Oracle input)
    (f : Symbol → Symbol) (action : Turing.Action k Symbol State)
    (bit : Oracle → Option Symbol) (move : Oracle → SignType) :
    (mapOutputConfig cfg f).step { action with output := action.output.map f } bit move =
      mapOutputConfig (cfg.step action bit move) f := by
  cases h : action.output <;>
    simp [mapOutputConfig, Config.step, Cfg.withOutput, Turing.Action.apply, h]

variable [DecidableEq Oracle]

private theorem receive_mapOutputConfig (cfg : Config k Symbol State Oracle input)
    (f : Symbol → Symbol) (op : Oracle) (next : State) (answer : List Symbol) :
    (mapOutputConfig cfg f).receive op next answer =
      mapOutputConfig (cfg.receive op next answer) f := rfl

/-- Output substitution preserves the complete program, without changing any oracle call. -/
theorem runConfigFrom_mapOutput (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (f : Symbol → Symbol) (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    (machine.mapOutput f).runConfigFrom query fuel (mapOutputConfig cfg f) =
      (fun final => mapOutputConfig final f) <$> machine.runConfigFrom query fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, mapOutputConfig, Cfg.withOutput, hs]
    | some state =>
      simp only [runConfigFrom,
        show (mapOutputConfig cfg f).tapes.state = cfg.tapes.state from rfl, hs, map_bind]
      congr 1
      funext coin
      change (match (machine.mapOutput f).tr state cfg.tapes.inputSymbol
          cfg.tapes.workTapeSymbols cfg.answerSymbols coin with
        | .step action bit move =>
          (machine.mapOutput f).runConfigFrom query fuel
            ((mapOutputConfig cfg f).step action bit move)
        | .query op next => do
          let answer ← query op (cfg.channels op).queryBuffer
          (machine.mapOutput f).runConfigFrom query fuel
            ((mapOutputConfig cfg f).receive op next answer)) = _
      simp only [mapOutput_tr]
      cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols coin
        <;> simp only [step_mapOutputConfig, receive_mapOutputConfig, ih, map_bind]

/-- The clocked output is the symbolwise map of the original clocked output. -/
theorem run_mapOutput (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (f : Symbol → Symbol) (fuel : ℕ) (input : List Symbol) :
    (machine.mapOutput f).run query fuel input = List.map f <$> machine.run query fuel input := by
  have hinitial : (machine.mapOutput f).initialConfig input =
      mapOutputConfig (machine.initialConfig input) f := rfl
  simp only [run, runFrom, hinitial, runConfigFrom_mapOutput, ← comp_map]
  rfl

end Turing.MultiTapePTM
