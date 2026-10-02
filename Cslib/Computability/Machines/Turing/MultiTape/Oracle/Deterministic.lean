/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Deterministic machines as probabilistic oracle machines

The embedding ignores the fresh coin and never calls its oracle. It preserves the number of
transitions, the output, and the oracle's private state. This supplies the machine-level bridge
from deterministic polynomial time to probabilistic polynomial time.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State OracleState : Type} {input : List Bool}

/-- Embed a deterministic machine without changing its control states or work tapes. -/
@[simps! initial] def ofDeterministic (machine : MultiTapeTM k Bool State) : OracleTM k State :=
  Turing.OracleTM.mk machine.q₀ fun state symbol work _ _ =>
    .step (machine.tr state symbol work) none 0

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem ofDeterministic_transition (machine : MultiTapeTM k Bool State) :
    (ofDeterministic machine).transition =
  fun state symbol work _ _ =>
    .step (machine.tr state symbol work) none 0 := by
  funext state symbol work answer coin
  simp only [ofDeterministic, Turing.OracleTM.transition_mk]

/-- Deterministic execution preserves the oracle communication tapes and private state. -/
theorem runState_runConfigFrom_ofDeterministic (machine : MultiTapeTM k Bool State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle ((ofDeterministic machine).runConfigFrom fuel cfg) s =
      PMF.pure ({ cfg with tapes := machine.runFrom cfg.tapes fuel }, s) := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      have hh : machine.runFrom cfg.tapes (fuel + 1) = cfg.tapes :=
        Function.iterate_fixed (MultiTapeTM.step_of_halt hs) _
      simp [runConfigFrom_halted _ _ _ hs, hh]
    | some state =>
      simp only [runConfigFrom_succ, hs, ofDeterministic_transition, OracleComp.uniform,
        OracleComp.runState_sample_bind, ih, PMF.bind_const]
      congr 1
      simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply]
      rw [MultiTapeTM.step_apply_of_state hs]
      simp [Config.step]

/-- A deterministic computation has the same output under every stateful oracle, which is left
unchanged. No assumption about the oracle's answers or efficiency is needed. -/
theorem runState_ofDeterministic (machine : MultiTapeTM k Bool State)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle ((ofDeterministic machine).runFrom fuel cfg) s =
      PMF.pure ((machine.runFrom cfg.tapes fuel).output, s) := by
  simp [runFrom, OracleComp.runState_map, runState_runConfigFrom_ofDeterministic, PMF.pure_map]

/-- The closed output distribution of the embedded deterministic machine. -/
theorem eval_ofDeterministic (machine : MultiTapeTM k Bool State)
    (oracle : List Bool → PMF (List Bool)) (fuel : ℕ) (cfg : Config k State input) :
    OracleComp.eval oracle ((ofDeterministic machine).runFrom fuel cfg) =
      PMF.pure (machine.runFrom cfg.tapes fuel).output := by
  have h := congrArg (PMF.map Prod.fst) (runState_ofDeterministic machine
    (fun q (s : Unit) => (oracle q).map (fun a => (a, s))) fuel cfg ())
  rw [OracleComp.runState_stateless] at h
  simpa [PMF.map, Function.comp_def] using h

end Turing.OracleTM
