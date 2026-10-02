/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Mathlib.Data.Fintype.EquivFin

/-!
# Renaming finite control states

Renaming control states preserves the complete clocked program, including every oracle query.
This lets machine constructions use ordinary finite products and sums of state types, while the
complexity predicates use a canonical `Fin` state space.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State State' : Type} {input : List Bool}

/-- Rename a machine's control states without changing its tape actions. -/
@[simps! initial] def rename (machine :
    OracleTM k State) (e : State ≃ State') :
    OracleTM k State' :=
  Turing.OracleTM.mk (e machine.initial) fun state symbol work answer coin =>
    match machine.transition (e.symm state) symbol work answer coin with
    | .step action bit move => .step { action with state := action.state.map e } bit move
    | .query next => .query (e next)

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem rename_transition (machine : OracleTM k State) (e : State ≃ State') :
    (rename machine e).transition =
  fun state symbol work answer coin =>
    match machine.transition (e.symm state) symbol work answer coin with
    | .step action bit move => .step { action with state := action.state.map e } bit move
    | .query next => .query (e next) := by
  funext state symbol work answer coin
  simp only [rename, Turing.OracleTM.transition_mk]

/-- Rename the control state in a configuration. -/
def Config.rename (cfg : Config k State input) (e : State ≃ State') : Config k State' input :=
  { cfg with tapes := cfg.tapes.mapState (Option.map e) }

@[simp] theorem Config.rename_state (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).tapes.state = cfg.tapes.state.map e := rfl

@[simp] theorem Config.rename_inputSymbol (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.rename_workTapeSymbols (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem Config.rename_answerSymbol (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem Config.rename_queryBuffer (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem Config.rename_output (cfg : Config k State input) (e : State ≃ State') :
    (cfg.rename e).tapes.output = cfg.tapes.output := rfl

theorem Config.step_rename (cfg : Config k State input) (e : State ≃ State')
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (cfg.rename e).step { action with state := action.state.map e } bit move =
      (cfg.step action bit move).rename e := rfl

theorem Config.receive_rename (cfg : Config k State input) (e : State ≃ State')
    (next : State) (answer : List Bool) :
    (cfg.rename e).receive (e next) answer = (cfg.receive next answer).rename e := rfl

/-- Renaming preserves the entire probabilistic program, including oracle interactions. -/
theorem runConfigFrom_rename (machine : OracleTM k State) (e : State ≃ State') (fuel : ℕ)
    (cfg : Config k State input) :
    (machine.rename e).runConfigFrom fuel (cfg.rename e) =
      (fun final => final.rename e) <$> machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, Config.rename_state, hs, Option.map_some,
        Config.rename_inputSymbol, Config.rename_workTapeSymbols, Config.rename_answerSymbol,
        rename_transition, Equiv.symm_apply_apply, map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin <;> simp [Config.step_rename, Config.receive_rename, ih, map_bind]

/-- Renaming preserves the output program from any configuration. -/
theorem runFrom_rename (machine : OracleTM k State) (e : State ≃ State') (fuel : ℕ)
    (cfg : Config k State input) :
    (machine.rename e).runFrom fuel (cfg.rename e) = machine.runFrom fuel cfg := by
  rw [runFrom_eq_map_runConfigFrom, runConfigFrom_rename, ← comp_map]
  exact (runFrom_eq_map_runConfigFrom machine fuel cfg).symm

/-- Renaming preserves the output program from the initial configuration. -/
theorem run_rename (machine : OracleTM k State) (e : State ≃ State') (fuel : ℕ)
    (input : List Bool) : (machine.rename e).run fuel input = machine.run fuel input :=
  runFrom_rename machine e fuel (machine.initialConfig input)

end Turing.OracleTM
