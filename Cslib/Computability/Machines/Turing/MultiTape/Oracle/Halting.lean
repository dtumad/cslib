/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Rename
public import Cslib.Probability.PMF

/-!
# Halting bounds for oracle machines
`HaltsWithin` requires every supported execution to halt within the bound, against every
stateful oracle. It concerns the machine's control state, not merely its externally stopped output.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State State' : Type}

/-- The machine has halted by `fuel` on every supported execution, for every stateful oracle. -/
def HaltsWithin (machine : OracleTM k State) (fuel : ℕ) (input : List Bool) : Prop :=
  ∀ (OracleState : Type) (oracle : List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (final : Config k State input) (s' : OracleState),
    (final, s') ∈ (OracleComp.runState oracle
      (machine.runConfigFrom fuel (machine.initialConfig input)) s).support →
    final.tapes.state = none

/-- Once every supported execution has halted, extra time preserves the complete distribution. -/
theorem runState_runConfigFrom_add_of_halted {OracleState : Type} {input : List Bool}
    (machine : OracleTM k State) (oracle : List Bool → StateT OracleState PMF (List Bool))
    (cfg : Config k State input) (fuel padding : ℕ) (s : OracleState)
    (hhalt : ∀ result ∈ (OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s).support,
      result.1.tapes.state = none) :
    OracleComp.runState oracle (machine.runConfigFrom (fuel + padding) cfg) s =
      OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s := by
  rw [runConfigFrom_add, OracleComp.runState_bind]
  conv_rhs => rw [← PMF.bind_pure (OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s)]
  apply Probability.PMF.bind_congr_on_support
  rintro ⟨final, s'⟩ hfinal
  simp only [runConfigFrom_halted _ _ _ (hhalt _ hfinal), OracleComp.runState_pure]

/-- Enumerating finite control states preserves actual halting. -/
theorem HaltsWithin.rename {machine : OracleTM k State} {fuel : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) (e : State ≃ State') :
    (machine.rename e).HaltsWithin fuel input := by
  intro OracleState oracle s final s' hfinal
  change (final, s') ∈ (OracleComp.runState oracle
    ((machine.rename e).runConfigFrom fuel ((machine.initialConfig input).rename e)) s).support
    at hfinal
  rw [runConfigFrom_rename, OracleComp.runState_map] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, hsource, heq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp hfinal
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  simpa [h OracleState oracle s sourceFinal sourceState hsource] using hstate.symm

/-- In particular, every supported run against a memoryless oracle has halted. -/
theorem HaltsWithin.eval {machine : OracleTM k State} {fuel : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) (oracle : List Bool → PMF (List Bool))
    (final : Config k State input)
    (hfinal : final ∈ (OracleComp.eval oracle
      (machine.runConfigFrom fuel (machine.initialConfig input))).support) :
    final.tapes.state = none := by
  apply h Unit (fun q s => (oracle q).map (fun answer => (answer, s))) () final ()
  rw [OracleComp.runState_stateless]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

/-- Any larger clock gives the same final configurations once a halting bound is known. -/
theorem HaltsWithin.runState_runConfigFrom_eq {machine : OracleTM k State}
    {fuel : ℕ} {input : List Bool} (h : machine.HaltsWithin fuel input)
    {OracleState : Type} (oracle : List Bool → StateT OracleState PMF (List Bool))
    (larger : ℕ) (s : OracleState) (hle : fuel ≤ larger) :
    OracleComp.runState oracle (machine.runConfigFrom larger (machine.initialConfig input)) s =
      OracleComp.runState oracle (machine.runConfigFrom fuel (machine.initialConfig input)) s := by
  have hh := runState_runConfigFrom_add_of_halted machine oracle (machine.initialConfig input)
    fuel (larger - fuel) s (fun result hresult => h _ oracle s result.1 result.2 hresult)
  simpa only [Nat.add_sub_of_le hle] using hh

/-- A halting bound remains valid when increased. -/
theorem HaltsWithin.mono {machine : OracleTM k State} {fuel larger : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) (hle : fuel ≤ larger) :
    machine.HaltsWithin larger input := by
  intro OracleState oracle s final s' hfinal
  rw [h.runState_runConfigFrom_eq oracle larger s hle] at hfinal
  exact h OracleState oracle s final s' hfinal

/-- Padding a halting machine's clock preserves its observable output distribution. -/
theorem HaltsWithin.eval_run_eq {machine : OracleTM k State} {fuel : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) (oracle : List Bool → PMF (List Bool))
    (larger : ℕ) (hle : fuel ≤ larger) :
    OracleComp.eval oracle (machine.run larger input) =
      OracleComp.eval oracle (machine.run fuel input) := by
  have hh := congrArg (PMF.map (fun result => result.1.tapes.output))
    (h.runState_runConfigFrom_eq (fun q (s : Unit) => (oracle q).map (fun answer => (answer, s)))
      larger () hle)
  rw [OracleComp.runState_stateless, OracleComp.runState_stateless] at hh
  simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.eval_map, PMF.map_comp,
    Function.comp_def] using hh

end Turing.OracleTM
