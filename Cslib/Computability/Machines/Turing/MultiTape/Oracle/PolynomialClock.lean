/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Clock
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Halting
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Prepend
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareClock
public import Mathlib.Basic.Finite.Prod

/-!
# Compiling external polynomial clocks into halting machines
`withPolynomialClock machine c d` starts with blank work tapes, constructs its unary budget,
and simulates exactly the bounded source computation. It then halts, including when the source
would run forever. Both preparation and simulation have an explicit polynomial runtime bound.
The construction preserves the output and the private state of every stateful oracle.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

namespace InternalClock

/-- Preparation and simulation both have finite control whenever the source does. -/
abbrev Control (coefficient degree : ℕ) (State : Type) :=
  MultiTapeTM.PolynomialClock.PrepareControl coefficient degree ⊕ Clock.Control State

/-- Coefficient of a monomial bounding initialization and the clocked simulation. -/
def overhead (coefficient degree : ℕ) : ℕ := 6 ^ degree * (coefficient + 1) + 3 * coefficient + 5

/-- A polynomial runtime for the entire compiled machine. -/
def time (coefficient degree length : ℕ) : ℕ :=
  overhead coefficient degree * (length + 1) ^ (degree + 1)

theorem time_le (coefficient degree length : ℕ) :
    MultiTapeTM.PolynomialClock.prepareTime coefficient degree length +
      (2 * (coefficient * (length + 1) ^ degree) + 1) ≤ time coefficient degree length := by
  have hpower : 1 ≤ (length + 1) ^ degree := Nat.one_le_pow _ _ (by omega)
  have hnext : (length + 1) ^ degree ≤ (length + 1) ^ (degree + 1) := by
    rw [pow_succ]
    nlinarith
  have hscaled := Nat.mul_le_mul_left (3 * coefficient) hnext
  simp only [MultiTapeTM.PolynomialClock.prepareTime, time, overhead]
  nlinarith

/-- Scratch tapes left by preparation, added after the source's work tapes. -/
def reserve {k : ℕ} {State : Type} {input : List Bool} (degree : ℕ)
    (cfg : Config k State input) : Config (k + degree) State input :=
  cfg.embed (Fin.castAddEmb degree)
    (fun _ => tapeOfList (List.replicate (input.length + 1) true)) (fun _ => 0)

/-- Unary budget tape for the source clock. -/
def tape (coefficient degree length : ℕ) : ℤ → Option Bool :=
  tapeOfList (List.replicate (coefficient * (length + 1) ^ degree) true)

/-- The final configuration retains all source data but replaces its control state by a halt. -/
def stopped {k : ℕ} {State : Type} {input : List Bool} (coefficient degree : ℕ)
    (cfg : Config k State input) :
    Config (k + degree + 1) (Control coefficient degree State) input :=
  Prepend.right (Clock.stopped (reserve degree cfg) (tape coefficient degree input.length)
    (coefficient * (input.length + 1) ^ degree : ℕ))

@[simp] theorem stopped_state {k : ℕ} {State : Type} {input : List Bool}
    (coefficient degree : ℕ) (cfg : Config k State input) :
    (stopped coefficient degree cfg).tapes.state = none := rfl

@[simp] theorem stopped_output {k : ℕ} {State : Type} {input : List Bool}
    (coefficient degree : ℕ) (cfg : Config k State input) :
    (stopped coefficient degree cfg).tapes.output = cfg.tapes.output := rfl

theorem tape_cell (coefficient degree length i : ℕ)
    (hi : i < coefficient * (length + 1) ^ degree) :
    tape coefficient degree length (0 + i) = some true := by
  simp [tape, tapeOfList_ofNat, hi]

theorem tape_end (coefficient degree length : ℕ) :
    tape coefficient degree length (0 + (coefficient * (length + 1) ^ degree : ℕ)) ≠
      some true := by
  simp only [tape, zero_add, tapeOfList_ofNat]
  simp

private theorem partialInv_castAdd_natAdd (k degree : ℕ) (i : Fin degree) :
    MultiTapeTM.partialInv (Fin.castAddEmb degree) (Fin.natAdd k i) = none := by
  apply MultiTapeTM.partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at this
  have := j.isLt
  omega

/-- The deterministic preparation produces precisely the initial simulation configuration. -/
theorem prepared {k : ℕ} {State Preparation : Type} (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool) :
    ({ tapes := (wordsCfg input (none : Option Preparation)
        (MultiTapeTM.PolynomialClock.preparedWords k coefficient degree input.length) []).withState
        (some (false, some machine.initial)) } :
        Config (k + degree + 1) (Clock.Control State) input) =
      Clock.config (reserve degree (machine.initialConfig input))
        (tape coefficient degree input.length) 0 false := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | last => simp [wordsCfg, Cfg.withState, Clock.config,
      MultiTapeTM.PolynomialClock.preparedWords, tape]
  | cast i =>
    simp only [wordsCfg, Cfg.withState, Clock.config,
      MultiTapeTM.PolynomialClock.preparedWords, Fin.lastCases_castSucc]
    induction i using Fin.addCases with
    | left i =>
      have hi := MultiTapeTM.partialInv_embed (Fin.castAddEmb degree) i
      simp only [Fin.castAddEmb_apply] at hi
      simp [reserve, Config.embed, MultiTapeTM.embed, initialConfig, Cfg.init, hi]
    | right i =>
      simp [reserve, Config.embed, MultiTapeTM.embed, partialInv_castAdd_natAdd]

end InternalClock

/-- Realize an external polynomial cutoff by a machine that prepares its own clock and halts. -/
def withPolynomialClock {k : ℕ} {State : Type} (machine : OracleTM k State)
    (coefficient degree : ℕ) :
    OracleTM (k + degree + 1) (InternalClock.Control coefficient degree State) :=
  ((machine.extendTapes (Fin.castAddEmb degree)).withClock).prepend
    (MultiTapeTM.PolynomialClock.prepare k coefficient degree)

variable {k : ℕ} {State OracleState : Type}

/-- The full compiled execution preserves all source data and oracle effects. Its initial work
tapes are blank, and the bound pays for constructing and rewinding the clock. -/
theorem runState_runConfigFrom_withPolynomialClock (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ) (s : OracleState)
    (hbound : InternalClock.time coefficient degree input.length ≤ fuel) :
    OracleComp.runState oracle
      ((machine.withPolynomialClock coefficient degree).runConfigFrom fuel
        ((machine.withPolynomialClock coefficient degree).initialConfig input)) s =
      (OracleComp.runState oracle
        (machine.runConfigFrom (coefficient * (input.length + 1) ^ degree)
          (machine.initialConfig input)) s).map
        (fun (final, s') => (InternalClock.stopped coefficient degree final, s')) := by
  let preparation := MultiTapeTM.PolynomialClock.prepare k coefficient degree
  let continuation := (machine.extendTapes (Fin.castAddEmb degree)).withClock
  let cfg := preparation.initCfg input
  let budget := coefficient * (input.length + 1) ^ degree
  have hprepare := MultiTapeTM.PolynomialClock.runFrom_prepare k coefficient degree input
  change preparation.runFrom cfg _ = _ at hprepare
  obtain ⟨elapsed, helapsed, hhalts⟩ := MultiTapeTM.exists_haltsAt (tm := preparation)
    (cfg := cfg) (t := MultiTapeTM.PolynomialClock.prepareTime coefficient degree input.length)
    (by rw [hprepare]; rfl)
  have hfinal : preparation.runFrom cfg elapsed =
      wordsCfg input none
        (MultiTapeTM.PolynomialClock.preparedWords k coefficient degree input.length) [] := by
    rw [← hhalts.runFrom_eq helapsed, hprepare]
  have hle : elapsed + (2 * budget + 1) ≤ fuel := by
    have := InternalClock.time_le coefficient degree input.length
    omega
  let padding := fuel - (elapsed + (2 * budget + 1))
  have htime : fuel = elapsed + (2 * budget + 1 + padding) := by omega
  change OracleComp.runState oracle
    ((continuation.prepend preparation).runConfigFrom fuel (Prepend.left continuation cfg)) s = _
  rw [htime, runState_runConfigFrom_prepend continuation preparation oracle cfg elapsed _ s
    hhalts.2 hhalts.halted, hfinal]
  simp only [continuation, withClock_initial, extendTapes_initial]
  rw [InternalClock.prepared (Preparation := MultiTapeTM.PolynomialClock.PrepareControl
    coefficient degree) machine coefficient degree input]
  rw [runState_runConfigFrom_withClock_add _ oracle _ _ 0 budget padding s
    (InternalClock.tape_cell coefficient degree input.length)
    (InternalClock.tape_end coefficient degree input.length)]
  simp only [InternalClock.reserve, runConfigFrom_embed, OracleComp.runState_map, PMF.map_comp,
    zero_add]
  rfl

/-- The compiled output and oracle state agree with the original externally clocked run. -/
theorem runState_withPolynomialClock (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ) (s : OracleState)
    (hbound : InternalClock.time coefficient degree input.length ≤ fuel) :
    OracleComp.runState oracle
      ((machine.withPolynomialClock coefficient degree).run fuel input) s =
      OracleComp.runState oracle
        (machine.run (coefficient * (input.length + 1) ^ degree) input) s := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_withPolynomialClock machine coefficient degree input oracle fuel s
      hbound)
  simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.runState_map, PMF.map_comp,
    Function.comp_def] using h

/-- The same compiler preserves the closed output distribution. -/
theorem eval_withPolynomialClock (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool) (oracle : List Bool → PMF (List Bool))
    (fuel : ℕ) (hbound : InternalClock.time coefficient degree input.length ≤ fuel) :
    OracleComp.eval oracle ((machine.withPolynomialClock coefficient degree).run fuel input) =
      OracleComp.eval oracle (machine.run (coefficient * (input.length + 1) ^ degree) input) := by
  have h := congrArg (PMF.map Prod.fst) (runState_withPolynomialClock machine coefficient degree
    input (fun q (s : Unit) => (oracle q).map (fun answer => (answer, s))) fuel () hbound)
  rw [OracleComp.runState_stateless, OracleComp.runState_stateless] at h
  simpa [PMF.map, Function.comp_def] using h

/-- Every supported final configuration is halted, independently of the oracle and random bits. -/
theorem withPolynomialClock_halted (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ) (s : OracleState)
    (hbound : InternalClock.time coefficient degree input.length ≤ fuel)
    (final : Config (k + degree + 1) (InternalClock.Control coefficient degree State) input)
    (s' : OracleState)
    (hfinal : (final, s') ∈ (OracleComp.runState oracle
      ((machine.withPolynomialClock coefficient degree).runConfigFrom fuel
        ((machine.withPolynomialClock coefficient degree).initialConfig input)) s).support) :
    final.tapes.state = none := by
  rw [runState_runConfigFrom_withPolynomialClock machine coefficient degree input oracle fuel s
    hbound] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact (congrArg (fun result => result.1.tapes.state) heq).symm

/-- The compiled machine satisfies a halting bound against every stateful oracle. -/
theorem withPolynomialClock_haltsWithin (machine : OracleTM k State)
    (coefficient degree : ℕ) (input : List Bool) (fuel : ℕ)
    (hbound : InternalClock.time coefficient degree input.length ≤ fuel) :
    (machine.withPolynomialClock coefficient degree).HaltsWithin fuel input :=
  fun _ oracle s final s' hfinal => withPolynomialClock_halted machine coefficient degree input
    oracle fuel s hbound final s' hfinal

end Turing.OracleTM
