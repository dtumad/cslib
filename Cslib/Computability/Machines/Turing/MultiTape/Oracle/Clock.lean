/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Simulation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# An internal clock on a work tape

`withClock machine` reserves one additional work tape for a unary execution budget. Each `true`
cell allows exactly one source transition; the first other cell stops the machine. A source
transition takes two target transitions, including when it queries a stateful oracle. Once the
source halts, the controller consumes the remaining budget without changing the source tapes.

This module implements the clock consumer. Initializing the budget tape is a separate computation:
the correctness theorem does not give a machine a polynomial-sized tape for free.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State OracleState : Type} {input : List Bool}

namespace Clock

/-- A phase bit and the source state; the source may already have halted. -/
abbrev Control (State : Type) := Bool × Option State

/-- Add the budget tape to a source configuration. A true phase bit means the next transition
advances the budget head; a false phase bit means the next transition simulates the source. -/
def config (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (ticking : Bool) : Config (k + 1) (Control State) input where
  tapes :=
    { state := some (ticking, cfg.tapes.state)
      inputPos := cfg.tapes.inputPos
      workTapes := Fin.lastCases tape cfg.tapes.workTapes
      workTapePos := Fin.lastCases position cfg.tapes.workTapePos
      output := cfg.tapes.output }
  queryBuffer := cfg.queryBuffer
  answer := cfg.answer
  answerPos := cfg.answerPos

/-- A controller transition which leaves all tapes unchanged. -/
def idle (next : Option (Control State)) : Action (k + 1) Bool (Control State) where
  inputTape := 0
  workTapes := fun _ => (none, 0)
  output := none
  state := next

/-- Advance the clock head by one cell, leaving every source tape unchanged. -/
def tick (next : Option State) : Action (k + 1) Bool (Control State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, 1) (fun _ => (none, 0))
  output := none
  state := some (false, next)

/-- A source action, followed by the clock-advance phase. -/
def liftAction (action : Action k Bool State) : Action (k + 1) Bool (Control State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 0) action.workTapes
  output := action.output
  state := some (true, action.state)

end Clock

/-- Run a machine under a unary budget stored on a fresh last work tape. -/
@[simps! initial] def withClock (machine :
    OracleTM k State) :
    OracleTM (k + 1) (Clock.Control State) :=
  Turing.OracleTM.mk ((false, some machine.initial)) fun control symbol work answer coin =>
    if control.1 then .step (Clock.tick control.2) none 0
    else if work (Fin.last k) = some true then
      match control.2 with
      | none => .step (Clock.idle (some (true, none))) none 0
      | some state =>
        match machine.transition state symbol (fun i => work i.castSucc) answer coin with
        | .step action bit move => .step (Clock.liftAction action) bit move
        | .query next => .query (true, some next)
    else .step (Clock.idle none) none 0

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem withClock_transition (machine : OracleTM k State) :
    (withClock machine).transition =
  fun control symbol work answer coin =>
    if control.1 then .step (Clock.tick control.2) none 0
    else if work (Fin.last k) = some true then
      match control.2 with
      | none => .step (Clock.idle (some (true, none))) none 0
      | some state =>
        match machine.transition state symbol (fun i => work i.castSucc) answer coin with
        | .step action bit move => .step (Clock.liftAction action) bit move
        | .query next => .query (true, some next)
    else .step (Clock.idle none) none 0 := by
  funext state symbol work answer coin
  simp only [withClock, Turing.OracleTM.transition_mk]

namespace Clock

@[simp] theorem config_state (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.state = some (ticking, cfg.tapes.state) := rfl

@[simp] theorem config_inputSymbol (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols_castSucc (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) (i : Fin k) :
    (config cfg tape position ticking).tapes.workTapeSymbols i.castSucc =
      cfg.tapes.workTapeSymbols i := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_workTapeSymbols_last (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.workTapeSymbols (Fin.last k) = tape position := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_answerSymbol (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem config_queryBuffer (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem config_output (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.output = cfg.tapes.output := rfl

theorem step_liftAction (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (config cfg tape position false).step (liftAction action) bit move =
      config (cfg.step action bit move) tape position true := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [config, liftAction, Config.step, Action.apply]

theorem receive_config (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (next : State) (answer : List Bool) :
    (config cfg tape position false).receive (true, some next) answer =
      config (cfg.receive next answer) tape position true := rfl

theorem step_tick (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position true).step (tick cfg.tapes.state) none 0 =
      config cfg tape (position + 1) false := by
  refine Config.ext ?_ (by simp [Config.step]) rfl (by simp [Config.step, config])
  refine Cfg.ext rfl (by simp [config, tick, Config.step, Action.apply]) ?_ ?_
    (by simp [config, tick, Config.step, Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [config, tick, Config.step, Action.apply]

theorem step_idle (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (ticking : Bool) (next : Option (Control State)) :
    (config cfg tape position ticking).step (idle next) none 0 =
      { config cfg tape position ticking with tapes :=
          (config cfg tape position ticking).tapes.withState next } := by
  simp [config, idle, Config.step, Action.apply, Cfg.withState]

theorem step_pause (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position false).step (idle (some (true, cfg.tapes.state))) none 0 =
      config cfg tape position true := by
  rw [step_idle]
  rfl

/-- Advancing the clock is deterministic and leaves the private oracle state alone. -/
theorem runState_tick (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom 1 (config cfg tape position true)) s =
      PMF.pure (config cfg tape (position + 1) false, s) := by
  simp only [runConfigFrom_zero, runConfigFrom_succ, config_state, withClock_transition,
    ↓reduceIte, step_tick,
    OracleComp.uniform, OracleComp.runState_sample_bind, OracleComp.runState_pure, PMF.bind_const]

/-- An available clock cell permits exactly one source transition and one clock advance. -/
theorem runState_pair (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState)
    (hcell : tape position = some true) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom 2 (config cfg tape position false)) s =
      (OracleComp.runState oracle (machine.runConfigFrom 1 cfg) s).map
        (fun (final, s') => (config final tape (position + 1) false, s')) := by
  conv_lhs => rw [runConfigFrom_succ]
  conv_rhs => rw [runConfigFrom_succ]
  simp only [config_state, withClock_transition, Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hcell, config_inputSymbol,
    config_workTapeSymbols_castSucc, config_answerSymbol]
  cases hs : cfg.tapes.state with
  | none =>
    simp only [OracleComp.uniform, OracleComp.runState_sample_bind]
    rw [← hs, step_pause]
    simp [runState_tick, PMF.pure_map]
  | some state =>
    simp only [OracleComp.uniform, OracleComp.runState_sample_bind, PMF.map_bind]
    congr 1
    funext coin
    cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin with
    | step action bit move =>
      simp only
      rw [step_liftAction, runState_tick]
      simp [PMF.pure_map]
    | query next =>
      simp only [config_queryBuffer, OracleComp.runState_bind, OracleComp.runState_query,
        PMF.map_bind]
      congr 1
      funext result
      rw [receive_config, runState_tick]
      simp [PMF.pure_map]

/-- Simulating a bounded prefix advances only the clock head in the extra tape. -/
theorem runState_prefix (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (fuel : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < fuel → tape (position + i) = some true) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom (2 * fuel) (config cfg tape position false)) s =
      (OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s).map
        (fun (final, s') => (config final tape (position + fuel) false, s')) := by
  have hstep : ∀ i, i < fuel → ∀ (cfg : Config k State input) (s : OracleState),
      OracleComp.runState oracle
        (machine.withClock.runConfigFrom 2 (config cfg tape (position + i) false)) s =
        (OracleComp.runState oracle (machine.runConfigFrom 1 cfg) s).map
          (fun (final, s') => (config final tape (position + (i + 1 : ℕ)) false, s')) := by
    intro i hi cfg s
    simpa [Nat.cast_add, add_assoc] using
      runState_pair machine oracle cfg tape (position + i) s (hbudget i hi)
  simpa only [Nat.cast_zero, add_zero] using
    runState_runConfigFrom_mul_indexed machine machine.withClock 2 fuel
      (fun i cfg => config cfg tape (position + i) false) oracle hstep cfg s

/-- Stop the controller, retaining the source tapes and the exhausted budget tape. -/
def stopped (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    Config (k + 1) (Control State) input :=
  { config cfg tape position false with tapes :=
      (config cfg tape position false).tapes.withState none }

@[simp] theorem stopped_state (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) : (stopped cfg tape position).tapes.state = none := rfl

@[simp] theorem stopped_output (cfg : Config k State input) (tape : ℤ → Option Bool)
    (position : ℤ) : (stopped cfg tape position).tapes.output = cfg.tapes.output := rfl

/-- At the budget's end the controller halts without taking another source step or oracle call. -/
theorem runState_stop (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState)
    (hstop : tape position ≠ some true) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom 1 (config cfg tape position false)) s =
      PMF.pure (stopped cfg tape position, s) := by
  simp only [runConfigFrom_zero, runConfigFrom_succ, config_state, withClock_transition,
    Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hstop, step_idle, OracleComp.uniform,
    OracleComp.runState_sample_bind, OracleComp.runState_pure, PMF.bind_const]
  rfl

end Clock

/-- A unary budget implements the source's external cutoff with a machine that halts.
All source tapes and the complete private oracle state are preserved, even for nonhalting sources.
The final source control state is discarded when the controller halts. -/
theorem runState_runConfigFrom_withClock (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom (2 * budget + 1)
        (Clock.config cfg tape position false)) s =
      (OracleComp.runState oracle (machine.runConfigFrom budget cfg) s).map
        (fun (final, s') => (Clock.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.runState_bind, Clock.runState_prefix machine oracle cfg tape
    position budget s hbudget, PMF.bind_map]
  simp only [Function.comp_def, Clock.runState_stop machine oracle _ tape _ _ hstop]
  rfl

/-- Additional time after the budget has expired cannot change any output or oracle effect. -/
theorem runState_runConfigFrom_withClock_add (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    OracleComp.runState oracle
      (machine.withClock.runConfigFrom (2 * budget + 1 + padding)
        (Clock.config cfg tape position false)) s =
      (OracleComp.runState oracle (machine.runConfigFrom budget cfg) s).map
        (fun (final, s') => (Clock.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.runState_bind,
    runState_runConfigFrom_withClock machine oracle cfg tape position budget s hbudget hstop,
    PMF.bind_map]
  simp only [Function.comp_def, runConfigFrom_halted _ _ _ (Clock.stopped_state ..),
    OracleComp.runState_pure]
  rfl

/-- In particular, the output and private oracle state agree with the original clocked run. -/
theorem runState_runFrom_withClock (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    OracleComp.runState oracle
      (machine.withClock.runFrom (2 * budget + 1 + padding)
        (Clock.config cfg tape position false)) s =
      OracleComp.runState oracle (machine.runFrom budget cfg) s := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_withClock_add machine oracle cfg tape position budget padding s
      hbudget hstop)
  simpa [runFrom_eq_map_runConfigFrom, OracleComp.runState_map, PMF.map_comp,
    Function.comp_def] using h

/-- Every supported final configuration is halted once the unary budget has expired. -/
theorem withClock_halted (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true)
    (final : Config (k + 1) (Clock.Control State) input) (s' : OracleState)
    (hfinal : (final, s') ∈ (OracleComp.runState oracle
      (machine.withClock.runConfigFrom (2 * budget + 1 + padding)
        (Clock.config cfg tape position false)) s).support) :
    final.tapes.state = none := by
  rw [runState_runConfigFrom_withClock_add machine oracle cfg tape position budget padding s
    hbudget hstop] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  exact hstate.symm

end Turing.OracleTM
