/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Probabilistic oracle Turing machines

A binary multi-tape machine with a write-only query buffer and a read-only answer tape. An ordinary
step reads only the symbols under the heads and one fresh fair bit, writes at most one query bit
and one output bit, and moves each head by at most one cell. A query step sends the buffer, clears
it, installs the answer, resets the answer head, and enters a specified state. It costs one step;
writing the query and reading the answer cost ordinary steps. The oracle's own computation is
external to this cost model.

`run` unfolds a bounded computation into `OracleComp`. Exhausting the clock returns the output
already written. The clock counts machine transitions, including local computation, rather than
just random draws or oracle calls. Every transition consumes a fresh fair bit, which deterministic
transitions can ignore. Coin choices remain distinct even when they give the same successor.

This is the compact single-operation interface to `MultiTapePTM`; both use the same evaluator.
The state type is deliberately unrestricted here; the definition of PPT imposes finite control.
Simulation equivalences with other oracle-machine conventions and a compiler from unrestricted
Lean programs are not supplied by this module.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Chapters 1, 7 and 9.
-/

@[expose] public section

namespace Turing

open Cslib

/-- A local tape action, or a call using the query buffer. -/
inductive OracleAction (k : ℕ) (State : Type) where
  /-- An ordinary action, an optional query bit, and movement of the answer head. -/
  | step (action : Action k Bool State) (queryBit : Option Bool) (answerMove : SignType)
  /-- Submit the query buffer and resume in `next`. -/
  | query (next : State)

/-- The compact single-operation action syntax is a view of the common action type. -/
def OracleAction.coreEquiv (k : ℕ) (State : Type) :
    MultiTapeMachine.Action k Bool State Unit ≃ OracleAction k State where
  toFun
    | .step action bit move => .step action (bit ()) (move ())
    | .query _ next => .query next
  invFun
    | .step action bit move => .step action (fun _ => bit) (fun _ => move)
    | .query next => .query () next
  left_inv action := by cases action <;> rfl
  right_inv action := by cases action <;> rfl

/-- A binary fair-coin machine with one oracle operation. Finiteness of the control is imposed
by the complexity layer; the representation is the same core used by `MultiTapeNTM`. -/
abbrev OracleTM (k : ℕ) (State : Type) := MultiTapePTM k Bool State Unit

namespace OracleTM

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Construct a single-operation machine using the compact transition-table interface. -/
def mk (initial : State) (transition : State → Option Bool → (Fin k → Option Bool) →
    Option Bool → Bool → OracleAction k State) : OracleTM k State where
  initial := initial
  tr state symbol work answer coin :=
    (OracleAction.coreEquiv k State).symm (transition state symbol work (answer ()) coin)

/-- Inspect a single-operation transition without exposing functions on `Unit`. -/
def transition (machine : OracleTM k State) (state : State) (symbol : Option Bool)
    (work : Fin k → Option Bool) (answer : Option Bool) (coin : Bool) : OracleAction k State :=
  OracleAction.coreEquiv k State (machine.tr state symbol work (fun _ => answer) coin)

@[simp] theorem initial_mk (initial : State) (transition : State → Option Bool →
    (Fin k → Option Bool) → Option Bool → Bool → OracleAction k State) :
    (mk initial transition).initial = initial := rfl

@[simp] theorem transition_mk (initial state : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Option Bool → Bool →
      OracleAction k State) (symbol : Option Bool) (work : Fin k → Option Bool)
    (answer : Option Bool) (coin : Bool) :
    (mk initial transition).transition state symbol work answer coin =
      transition state symbol work answer coin :=
  (OracleAction.coreEquiv k State).apply_symm_apply _

/-- The compact interface describes every single-operation fair-coin machine. -/
theorem mk_initial_transition (machine : OracleTM k State) :
    mk machine.initial machine.transition = machine := by
  cases machine
  simp [mk, transition]

/-- Translate a compact transition back to the common core, retaining its coin label. -/
theorem tr_eq (machine : OracleTM k State) (state : State) (symbol : Option Bool)
    (work : Fin k → Option Bool) (answer : Unit → Option Bool) (coin : Bool) :
    machine.tr state symbol work answer coin = (OracleAction.coreEquiv k State).symm
      (machine.transition state symbol work (answer ()) coin) :=
  ((OracleAction.coreEquiv k State).symm_apply_apply _).symm

/-- A machine configuration, including the two oracle communication tapes. -/
@[ext] structure Config (k : ℕ) (State : Type) (input : List Bool) where
  /-- The ordinary input, work and output tapes and control state. -/
  tapes : Cfg k Bool State input
  /-- Bits written since the previous query. -/
  queryBuffer : List Bool := []
  /-- The most recent oracle answer, inaccessible except through the answer head. -/
  answer : List Bool := []
  /-- Answer-tape head position; the first answer bit is at position zero. -/
  answerPos : ℤ := 0

/-- Read one answer-tape cell. Cells outside the answer are blank. -/
def Config.answerSymbol (cfg : Config k State input) : Option Bool :=
  if 0 ≤ cfg.answerPos then cfg.answer[cfg.answerPos.toNat]? else none

/-- Apply one ordinary transition. -/
def Config.step (cfg : Config k State input) (action : Action k Bool State)
    (queryBit : Option Bool) (answerMove : SignType) : Config k State input where
  tapes := action.apply cfg.tapes
  queryBuffer := cfg.queryBuffer ++ queryBit.toList
  answer := cfg.answer
  answerPos := cfg.answerPos + answerMove

/-- Install an answer and clear the submitted query. -/
def Config.receive (cfg : Config k State input) (next : State) (answer : List Bool) :
    Config k State input where
  tapes := { cfg.tapes with state := some next }
  answer := answer

/-- The compact configuration as a single-channel configuration of the common core. -/
def Config.toCore (cfg : Config k State input) : MultiTapeMachine.Config k Bool State Unit input :=
  ⟨cfg.tapes, fun _ => ⟨cfg.queryBuffer, cfg.answer, cfg.answerPos⟩⟩

/-- Read the single communication channel through the compact interface. -/
def Config.ofCore (cfg : MultiTapeMachine.Config k Bool State Unit input) : Config k State input :=
  ⟨cfg.tapes, (cfg.channels ()).queryBuffer, (cfg.channels ()).answer, (cfg.channels ()).answerPos⟩

/-- The compact configuration and the core carry exactly the same information. -/
def Config.coreEquiv : Config k State input ≃ MultiTapeMachine.Config k Bool State Unit input where
  toFun := Config.toCore
  invFun := Config.ofCore
  left_inv cfg := by cases cfg; rfl
  right_inv cfg := by cases cfg; rfl

@[simp] theorem Config.toCore_tapes (cfg : Config k State input) :
    cfg.toCore.tapes = cfg.tapes := rfl

@[simp] theorem Config.toCore_answerSymbols (cfg : Config k State input) :
    cfg.toCore.answerSymbols = fun _ => cfg.answerSymbol := rfl

@[simp] theorem Config.toCore_queryBuffer (cfg : Config k State input) :
    (cfg.toCore.channels ()).queryBuffer = cfg.queryBuffer := rfl

/-- Ordinary tape steps commute with the configuration equivalence without a slowdown. -/
theorem Config.toCore_step (cfg : Config k State input) (action : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (cfg.step action bit move).toCore = cfg.toCore.step action (fun _ => bit) (fun _ => move) := rfl

/-- Query submission and reply installation commute with the configuration equivalence. -/
theorem Config.toCore_receive (cfg : Config k State input) (next : State) (answer : List Bool) :
    (cfg.receive next answer).toCore = cfg.toCore.receive () next answer := by
  apply MultiTapeMachine.Config.ext rfl
  funext oracle
  cases oracle
  simp [Config.toCore, Config.receive]

/-- The initial configuration has empty work, output and oracle tapes. -/
def initialConfig (machine : OracleTM k State) (input : List Bool) : Config k State input where
  tapes := Cfg.init machine.initial input

/-- Run the common evaluator, presenting its single channel through the compact configuration. -/
noncomputable def runConfigFrom (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) :
    OracleComp (List Bool) (fun _ => List Bool) (Config k State input) :=
  Config.ofCore <$> MultiTapePTM.runConfigFrom machine (fun _ => OracleComp.query) fuel cfg.toCore

/-- Observe the output of a bounded execution of the common machine core. -/
noncomputable def runFrom (machine : OracleTM k State) (fuel : ℕ) (cfg : Config k State input) :
    OracleComp (List Bool) (fun _ => List Bool) (List Bool) :=
  (fun final => final.tapes.output) <$> machine.runConfigFrom fuel cfg

/-- Run a clocked machine from its initial configuration. -/
noncomputable def run (machine : OracleTM k State) (fuel : ℕ) (input : List Bool) :
    OracleComp (List Bool) (fun _ => List Bool) (List Bool) :=
  machine.runFrom fuel (machine.initialConfig input)

@[simp] theorem runConfigFrom_zero (machine : OracleTM k State) (cfg : Config k State input) :
    machine.runConfigFrom 0 cfg = pure cfg := by
  simp [runConfigFrom, Config.ofCore, Config.toCore]

/-- One transition in the compact interface is one transition of the common evaluator. -/
theorem runConfigFrom_succ (machine : OracleTM k State) (fuel : ℕ) (cfg : Config k State input) :
    machine.runConfigFrom (fuel + 1) cfg = (match cfg.tapes.state with
    | none => pure cfg
    | some state => do
      let coin ← OracleComp.uniform Bool
      match machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | .step action bit move => machine.runConfigFrom fuel (cfg.step action bit move)
      | .query next =>
        let answer ← OracleComp.query cfg.queryBuffer
        machine.runConfigFrom fuel (cfg.receive next answer)) := by
  cases hs : cfg.tapes.state with
  | none =>
    simp [runConfigFrom, MultiTapePTM.runConfigFrom, hs, Config.toCore, Config.ofCore]
  | some state =>
    simp only [runConfigFrom, MultiTapePTM.runConfigFrom, Config.toCore_tapes, hs,
      Config.toCore_answerSymbols, tr_eq, map_bind]
    congr 1
    funext coin
    cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin with
    | step action bit move => rfl
    | query next =>
      simp only [OracleAction.coreEquiv, Equiv.coe_fn_symm_mk,
        Config.toCore_queryBuffer, ← Config.toCore_receive, map_bind]

@[simp] theorem runConfigFrom_halted (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (h : cfg.tapes.state = none) :
    machine.runConfigFrom fuel cfg = pure cfg := by
  cases fuel <;> simp [runConfigFrom_succ, h]

/-- The output is the projection of the complete final configuration. -/
theorem runFrom_eq_map_runConfigFrom (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) :
    machine.runFrom fuel cfg = (fun final => final.tapes.output) <$>
      machine.runConfigFrom fuel cfg := rfl

@[simp] theorem runFrom_zero (machine : OracleTM k State) (cfg : Config k State input) :
    machine.runFrom 0 cfg = pure cfg.tapes.output := by simp [runFrom]

/-- The compact one-step equation for the output-only evaluator. -/
theorem runFrom_succ (machine : OracleTM k State) (fuel : ℕ) (cfg : Config k State input) :
    machine.runFrom (fuel + 1) cfg = (match cfg.tapes.state with
    | none => pure cfg.tapes.output
    | some state => do
      let coin ← OracleComp.uniform Bool
      match machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | .step action bit move => machine.runFrom fuel (cfg.step action bit move)
      | .query next =>
        let answer ← OracleComp.query cfg.queryBuffer
        machine.runFrom fuel (cfg.receive next answer)) := by
  cases hs : cfg.tapes.state with
  | none => simp [runFrom, hs]
  | some state =>
    simp only [runFrom, runConfigFrom_succ, hs, map_bind]
    congr 1
    funext coin
    split <;> simp only [map_bind]

@[simp] theorem runFrom_halted (machine : OracleTM k State) (fuel : ℕ)
    (cfg : Config k State input) (h : cfg.tapes.state = none) :
    machine.runFrom fuel cfg = pure cfg.tapes.output := by
  simp [runFrom, h]

/-- The compact view preserves every part of a bounded computation, including pending queries. -/
theorem runConfigFrom_core (machine : OracleTM k State) (fuel : ℕ) (cfg : Config k State input) :
    MultiTapePTM.runConfigFrom machine (fun _ => OracleComp.query) fuel cfg.toCore =
      Config.toCore <$> machine.runConfigFrom fuel cfg := by
  rw [runConfigFrom, ← comp_map]
  exact (id_map _).symm

/-- The common evaluator preserves the output at exactly the same clock, with the same queries. -/
theorem runFrom_core (machine : OracleTM k State) (fuel : ℕ) (cfg : Config k State input) :
    MultiTapePTM.runFrom machine (fun _ => OracleComp.query) fuel cfg.toCore =
      machine.runFrom fuel cfg := by
  rw [MultiTapePTM.runFrom, runConfigFrom_core, ← comp_map, runFrom_eq_map_runConfigFrom]
  rfl

/-- The single-operation facade and common core have the same initial execution. -/
theorem run_core (machine : OracleTM k State) (fuel : ℕ) (input : List Bool) :
    MultiTapePTM.run machine (fun _ => OracleComp.query) fuel input = machine.run fuel input :=
  runFrom_core machine fuel (machine.initialConfig input)

/-- Splitting a clock preserves the entire interaction, including queries across the split. -/
theorem runConfigFrom_add (machine : OracleTM k State) (first second : ℕ)
    (cfg : Config k State input) :
    machine.runConfigFrom (first + second) cfg =
      (machine.runConfigFrom first cfg >>= machine.runConfigFrom second) := by
  simp only [runConfigFrom, MultiTapePTM.runConfigFrom_add, map_bind, bind_map_left]
  rfl

/-- A run can be paused, then resumed to obtain its output. -/
theorem runFrom_add (machine : OracleTM k State) (first second : ℕ)
    (cfg : Config k State input) :
    machine.runFrom (first + second) cfg =
      (machine.runConfigFrom first cfg >>= machine.runFrom second) := by
  simp only [runFrom_eq_map_runConfigFrom, runConfigFrom_add, map_bind]
  rfl

/-- One ordinary step writes at most one query bit. -/
theorem length_queryBuffer_step_le (cfg : Config k State input) (action : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (cfg.step action bit move).queryBuffer.length ≤ cfg.queryBuffer.length + 1 := by
  simp only [Config.step, List.length_append]
  exact Nat.add_le_add_left bit.length_toList_le _

/-- One ordinary step writes at most one output bit. -/
theorem length_output_step_le (cfg : Config k State input) (action : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (cfg.step action bit move).tapes.output.length ≤ cfg.tapes.output.length + 1 := by
  simp only [Config.step, Action.apply, List.length_append]
  exact Nat.add_le_add_left action.output.length_toList_le _

/-- Even an oracle with arbitrarily long answers cannot make the machine write more than one
output bit per transition. The bound holds on every positive-probability execution. -/
theorem length_output_runFrom_le {OracleState : Type} (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Config k State input) (s s' : OracleState) (output : List Bool)
    (h : (output, s') ∈ (OracleComp.runState oracle (machine.runFrom fuel cfg) s).support) :
    output.length ≤ cfg.tapes.output.length + fuel := by
  rw [← runFrom_core] at h
  exact MultiTapePTM.length_output_runFrom_le machine (fun _ => OracleComp.query)
    oracle fuel cfg.toCore s s' output h

/-- The output-size bound specialized to memoryless oracle evaluation. -/
theorem length_output_eval_runFrom_le (machine : OracleTM k State)
    (oracle : List Bool → PMF (List Bool)) (fuel : ℕ) (cfg : Config k State input)
    (output : List Bool)
    (h : output ∈ (OracleComp.eval oracle (machine.runFrom fuel cfg)).support) :
    output.length ≤ cfg.tapes.output.length + fuel := by
  apply length_output_runFrom_le machine
    (fun q (s : Unit) => (oracle q).map (fun a => (a, s))) fuel cfg () () output
  rw [OracleComp.runState_stateless]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨output, h, rfl⟩

end OracleTM

end Turing
