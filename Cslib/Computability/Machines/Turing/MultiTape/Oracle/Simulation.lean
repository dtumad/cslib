/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle

/-!
# Clock-preserving simulations of probabilistic oracle machines
A machine transformation can implement one source transition by a fixed block of target
transitions. `runState_runConfigFrom_mul` lifts the one-block simulation to arbitrary clocks,
preserving both the final configuration and the oracle's private state.
The indexed version also permits the embedding to change after each step, for example to track
the head of an internal clock tape.
The statement includes halted configurations. This ensures that padding a halted source run is
also simulated correctly. No assumption that the source halts before its clock expires is needed.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k k' : ℕ} {State State' OracleState : Type} {input input' : List Bool}

/-- A bounded simulation may update its configuration embedding after each source transition.
This accounts for private bookkeeping, such as advancing a separate clock tape. -/
theorem runState_runConfigFrom_mul_indexed (source : OracleTM k State)
    (target : OracleTM k' State') (delay fuel : ℕ)
    (embed : ℕ → Config k State input → Config k' State' input')
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (hstep : ∀ i, i < fuel → ∀ cfg s,
      OracleComp.runState oracle (target.runConfigFrom delay (embed i cfg)) s =
        (OracleComp.runState oracle (source.runConfigFrom 1 cfg) s).map
          (fun (final, s') => (embed (i + 1) final, s')))
    (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle (target.runConfigFrom (delay * fuel) (embed 0 cfg)) s =
      (OracleComp.runState oracle (source.runConfigFrom fuel cfg) s).map
        (fun (final, s') => (embed fuel final, s')) := by
  induction fuel generalizing embed cfg s with
  | zero => simp [PMF.pure_map]
  | succ fuel ih =>
    rw [show delay * (fuel + 1) = delay + delay * fuel by rw [Nat.mul_succ, Nat.add_comm],
      target.runConfigFrom_add, OracleComp.runState_bind, hstep 0 (by omega), PMF.bind_map]
    rw [show fuel + 1 = 1 + fuel by omega, source.runConfigFrom_add,
      OracleComp.runState_bind, PMF.map_bind]
    simp only [Function.comp_def]
    congr 1
    funext result
    simpa [Nat.add_comm] using ih (fun i => embed (i + 1))
      (fun i hi => hstep (i + 1) (by omega)) result.1 result.2

/-- A simulation of one transition by `delay` transitions preserves every clocked run.
The oracle's final state is included, so the theorem applies to adaptive, stateful interactions. -/
theorem runState_runConfigFrom_mul (source : OracleTM k State) (target : OracleTM k' State')
    (embed : Config k State input → Config k' State' input') (delay : ℕ)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (hstep : ∀ cfg s,
      OracleComp.runState oracle (target.runConfigFrom delay (embed cfg)) s =
        (OracleComp.runState oracle (source.runConfigFrom 1 cfg) s).map
          (fun (final, s') => (embed final, s')))
    (fuel : ℕ) (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle (target.runConfigFrom (delay * fuel) (embed cfg)) s =
      (OracleComp.runState oracle (source.runConfigFrom fuel cfg) s).map
        (fun (final, s') => (embed final, s')) :=
  runState_runConfigFrom_mul_indexed source target delay fuel (fun _ => embed) oracle
    (fun _ _ => hstep) cfg s

end Turing.OracleTM
