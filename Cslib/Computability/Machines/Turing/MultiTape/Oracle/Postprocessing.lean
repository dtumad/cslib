/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle

/-!
# Mapping the output bits of an oracle machine

A fixed Boolean function can be applied to each emitted bit in the same transition. The machine
does not read its output tape, so this changes neither subsequent control flow nor oracle queries.
In particular, complementing an adversary's final Boolean answer preserves PPT, with the same clock.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Apply a fixed Boolean function to each bit written on the output tape. -/
@[simps! initial] def mapOutput (machine : OracleTM k State) (f : Bool → Bool) : OracleTM k State :=
  Turing.OracleTM.mk (machine.initial) fun state symbol work answer coin =>
    match machine.transition state symbol work answer coin with
    | .step action bit move => .step { action with output := action.output.map f } bit move
    | .query next => .query next

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem mapOutput_transition (machine : OracleTM k State) (f : Bool → Bool) :
    (mapOutput machine f).transition =
  fun state symbol work answer coin =>
    match machine.transition state symbol work answer coin with
    | .step action bit move => .step { action with output := action.output.map f } bit move
    | .query next => .query next := by
  funext state symbol work answer coin
  simp only [mapOutput, Turing.OracleTM.transition_mk]

/-- Change only the bits already written on the output tape. -/
def Config.mapOutput (cfg : Config k State input) (f : Bool → Bool) : Config k State input :=
  { cfg with tapes := cfg.tapes.withOutput (cfg.tapes.output.map f) }

@[simp] theorem Config.mapOutput_state (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).tapes.state = cfg.tapes.state := rfl

@[simp] theorem Config.mapOutput_inputSymbol (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.mapOutput_workTapeSymbols (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem Config.mapOutput_answerSymbol (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem Config.mapOutput_queryBuffer (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem Config.mapOutput_output (cfg : Config k State input) (f : Bool → Bool) :
    (cfg.mapOutput f).tapes.output = cfg.tapes.output.map f := rfl

theorem Config.step_mapOutput (cfg : Config k State input) (f : Bool → Bool)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (cfg.mapOutput f).step { action with output := action.output.map f } bit move =
      (cfg.step action bit move).mapOutput f := by
  cases h : action.output <;> simp [Config.mapOutput, Config.step, Cfg.withOutput, Action.apply, h]

theorem Config.receive_mapOutput (cfg : Config k State input) (f : Bool → Bool)
    (next : State) (answer : List Bool) :
    (cfg.mapOutput f).receive next answer = (cfg.receive next answer).mapOutput f := rfl

/-- Output postprocessing preserves the complete oracle interaction, without adding steps. -/
theorem runFrom_mapOutput (machine : OracleTM k State) (f : Bool → Bool) (fuel : ℕ)
    (cfg : Config k State input) :
    (machine.mapOutput f).runFrom fuel (cfg.mapOutput f) =
      List.map f <$> machine.runFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runFrom_succ, Config.mapOutput_state, hs, Config.mapOutput_inputSymbol,
        Config.mapOutput_workTapeSymbols, Config.mapOutput_answerSymbol, mapOutput_transition,
        map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin <;>
        simp [Config.step_mapOutput, Config.receive_mapOutput, ih, map_bind]

/-- Postprocessing from the initial configuration. -/
theorem run_mapOutput (machine : OracleTM k State) (f : Bool → Bool) (fuel : ℕ)
    (input : List Bool) :
    (machine.mapOutput f).run fuel input = List.map f <$> machine.run fuel input := by
  exact runFrom_mapOutput machine f fuel (machine.initialConfig input)

end Turing.OracleTM
