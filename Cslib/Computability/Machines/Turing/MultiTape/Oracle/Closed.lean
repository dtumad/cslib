/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Halting

/-!
# Eliminating the empty oracle of a closed machine

A closed PPT witness uses only an oracle returning the empty word. `closed` replaces each such
query by a local transition and suppresses writes to the query buffer. Its communication tapes
therefore stay empty. This permits subsequent closed computations to start with fresh
communication tapes, without introducing spurious queries to an external oracle.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State OracleState : Type} {input : List Bool}

namespace Closed

/-- Locally handle an empty-answer query by changing only the control state. -/
def queryAction (next : State) : Action k Bool State where
  inputTape := 0
  workTapes := fun _ => (none, 0)
  output := none
  state := some next

/-- Clear all oracle communication while preserving ordinary tapes and control state. -/
def config (cfg : Config k State input) : Config k State input where
  tapes := cfg.tapes

@[simp] theorem config_state (cfg : Config k State input) :
    (config cfg).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_inputSymbol (cfg : Config k State input) :
    (config cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k State input) :
    (config cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

theorem step_config (cfg : Config k State input) (action : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (config cfg).step action none 0 = config (cfg.step action bit move) := rfl

theorem query_config (cfg : Config k State input) (next : State) :
    (config cfg).step (queryAction next) none 0 = config (cfg.receive next []) := by
  simp [config, Config.step, queryAction, Config.receive, Action.apply]

theorem answerSymbol_eq_none (cfg : Config k State input) (h : cfg.answer = []) :
    cfg.answerSymbol = none := by
  simp [Config.answerSymbol, h]

end Closed

/-- Replace the empty-answer oracle by local computation, with exactly the same time cost. -/
@[simps! initial] def closed (machine : OracleTM k State) : OracleTM k State :=
  Turing.OracleTM.mk (machine.initial) fun state symbol work _ coin =>
    match machine.transition state symbol work none coin with
    | .step action _ _ => .step action none 0
    | .query next => .step (Closed.queryAction next) none 0

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem closed_transition (machine : OracleTM k State) :
    (closed machine).transition =
  fun state symbol work _ coin =>
    match machine.transition state symbol work none coin with
    | .step action _ _ => .step action none 0
    | .query next => .step (Closed.queryAction next) none 0 := by
  funext state symbol work answer coin
  simp only [closed, Turing.OracleTM.transition_mk]

/-- Eliminating the empty oracle preserves every ordinary tape and leaves any external private
state untouched. Both query construction and query submission retain their original cost. -/
theorem runState_runConfigFrom_closed (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Config k State input) (s : OracleState) (hanswer : cfg.answer = []) :
    OracleComp.runState oracle (machine.closed.runConfigFrom fuel (Closed.config cfg)) s =
      (OracleComp.eval (fun _ => PMF.pure []) (machine.runConfigFrom fuel cfg)).map
        (fun final => (Closed.config final, s)) := by
  induction fuel generalizing cfg with
  | zero => simp [PMF.pure_map]
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs, PMF.pure_map]
    | some state =>
      have hsymbol := Closed.answerSymbol_eq_none cfg hanswer
      simp only [runConfigFrom_succ, Closed.config_state, hs, Closed.config_inputSymbol,
        Closed.config_workTapeSymbols, hsymbol, closed_transition, OracleComp.uniform,
        OracleComp.runState_sample_bind, OracleComp.eval_bind, OracleComp.eval_sample,
        PMF.map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols none coin with
      | step action bit move =>
        simp only [Closed.step_config cfg action bit move]
        exact ih (cfg.step action bit move) hanswer
      | query next =>
        simp only [Closed.query_config, OracleComp.eval_bind, OracleComp.eval_query,
          PMF.pure_bind]
        exact ih (cfg.receive next []) rfl

/-- The closed machine has the original closed output distribution under any external oracle. -/
theorem runState_closed (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (input : List Bool) (s : OracleState) :
    OracleComp.runState oracle (machine.closed.run fuel input) s =
      (OracleComp.eval (fun _ => PMF.pure []) (machine.run fuel input)).map
        (fun output => (output, s)) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_closed machine oracle fuel (machine.initialConfig input) s rfl)
  simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.runState_map, OracleComp.eval_map,
    PMF.map_comp, Function.comp_def, Closed.config, initialConfig] using h

/-- The local replacement also preserves genuine halting. -/
theorem HaltsWithin.closed {machine : OracleTM k State} {fuel : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) : machine.closed.HaltsWithin fuel input := by
  intro OracleState oracle s final s' hfinal
  change (final, s') ∈ (OracleComp.runState oracle
    (machine.closed.runConfigFrom fuel (Closed.config (machine.initialConfig input))) s).support
    at hfinal
  rw [runState_runConfigFrom_closed machine oracle fuel _ s rfl] at hfinal
  obtain ⟨sourceFinal, hsource, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  have hpure : (sourceFinal, ()) ∈ (OracleComp.runState
      (fun _ (_ : Unit) => PMF.pure ([], ()))
      (machine.runConfigFrom fuel (machine.initialConfig input)) ()).support := by
    have heval := OracleComp.runState_stateless (fun _ => PMF.pure [])
      (machine.runConfigFrom fuel (machine.initialConfig input)) ()
    simp only [PMF.pure_map] at heval
    rw [heval]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sourceFinal, hsource, rfl⟩
  have hhalt := h Unit (fun _ _ => PMF.pure ([], ())) () sourceFinal () hpure
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  simpa [hhalt] using hstate.symm

end Turing.OracleTM
