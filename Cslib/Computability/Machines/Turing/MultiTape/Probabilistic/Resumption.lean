/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Resumption

/-!
# Unbounded execution of probabilistic machines

`runUnbounded` executes a machine without a transition budget, as a resumption over its coin and
query operations: runs that never halt are infinite paths. Every live transition flips a coin,
even when the transition table ignores it, so each transition is an operation of the resumption.

When every path halts within a transition budget, the unbounded execution is the bounded one
embedded as a resumption (`HaltsWithin.runUnbounded_eq`).
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- A configuration, or a query awaiting its answer after the transition's coin. -/
abbrev ExecutionState (k : ℕ) (State Oracle : Type) (input : List Bool) :=
  Config k Bool State Oracle input ⊕ (Config k Bool State Oracle input × Oracle × State)

/-- Halt with the configuration, or perform the next coin or query operation. -/
def executionStep (machine : MultiTapePTM k Bool State Oracle) :
    ExecutionState k State Oracle input → Config k Bool State Oracle input ⊕
      (effects Oracle).Obj (ExecutionState k State Oracle input)
  | .inl cfg => match cfg.tapes.state with
    | none => .inl cfg
    | some state => .inr (.mk (.inl ()) fun bit =>
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | .step action symbol move => .inl (cfg.step action symbol move)
      | .query oracle next => .inr (cfg, oracle, next))
  | .inr (cfg, oracle, next) =>
    .inr (.mk (.inr (oracle, (cfg.channels oracle).queryBuffer))
      fun answer => .inl (cfg.receive oracle next answer))

/-- Execute without a transition budget. -/
def runUnbounded (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) :
    Resumption (effects Oracle) (Config k Bool State Oracle input) :=
  Resumption.corec machine.executionStep (.inl cfg)

/-- Unbounded execution is one transition followed by unbounded execution. -/
theorem runUnbounded_eq_step_bind (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) :
    machine.runUnbounded cfg = (machine.step cfg).toResumption.bind machine.runUnbounded := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    rw [← Resumption.dest_inj]
    simp only [runUnbounded, Resumption.dest_corec, executionStep, hs, step, coin, hAdd_B,
      Sum.map_inr, PFunctor.map_eq, bind_pure_comp, FreeM.toResumption_bind',
      FreeM.toResumption_lift, Resumption.bind_eq_bind, bind_assoc, Resumption.dest_lift_bind',
      Sum.inr.injEq]
    congr 1
    funext bit
    cases h : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
      cfg.answerSymbols bit
    · simp [h, runUnbounded]
    · simp [h, ← Resumption.dest_inj, runUnbounded, executionStep, query, Function.comp_def]

/-- A halted machine returns immediately. -/
theorem runUnbounded_halted (machine : MultiTapePTM k Bool State Oracle)
    {cfg : Config k Bool State Oracle input} (h : cfg.tapes.state = none) :
    machine.runUnbounded cfg = pure cfg := by
  simp [← Resumption.dest_inj, runUnbounded, executionStep, h]

/-- A budget bounding every path from a configuration bounds, with one fewer transition, every path
from each configuration it can step to. -/
theorem HaltsWithin.of_canReturn_step {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg cfg' : Config k Bool State Oracle input} (h : machine.HaltsWithin (fuel + 1) cfg)
    (hstep : MonadAttach.CanReturn (machine.step cfg) cfg') : machine.HaltsWithin fuel cfg' :=
  fun final hfinal => h final ((FreeM.canReturn_bind' _ _ _).mpr ⟨cfg', hstep, hfinal⟩)

/-- When every path halts within a budget, unbounded execution is the bounded execution. -/
theorem HaltsWithin.runUnbounded_eq {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg) :
    machine.runUnbounded cfg = (machine.runConfigFrom fuel cfg).toResumption := by
  induction fuel generalizing cfg with
  | zero => simpa using machine.runUnbounded_halted (h cfg rfl)
  | succ fuel ih =>
    rw [runUnbounded_eq_step_bind, runConfigFrom_succ, FreeM.toResumption_bind',
      ← WeaklyLawfulMonadAttach.map_attach (x := machine.step cfg)]
    simp only [FreeM.toResumption_map', Resumption.bind_eq_bind, bind_map_left]
    congr 1
    funext ⟨cfg', hcfg'⟩
    exact ih (h.of_canReturn_step hcfg')

end Turing.MultiTapePTM
