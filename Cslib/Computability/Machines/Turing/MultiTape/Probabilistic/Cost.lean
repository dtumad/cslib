/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered

/-!
# Oracle-query bounds from machine clocks

A transition submits at most one oracle request. A selected family of requests therefore
inherits the transition bound, without counting the private coin used at each transition.
These bounds apply to the machine's native free program, including unfinished executions.
-/

public section

namespace Turing.MultiTapePTM

open PFunctor MultiTapeMachine

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- Each transition contributes at most one selected external request. -/
theorem queryBoundP_step_le (machine : MultiTapePTM k Bool State Oracle)
    (select : (effects Oracle).A → Bool) (hcoin : select (.inl ()) = false)
    (cfg : Config k Bool State Oracle input) :
    FreeM.queryBoundP select (machine.step cfg) ≤ 1 := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, hs]
    refine le_trans (FreeM.queryBoundP_bind_le select coin _ 1 ?_) ?_
    · intro bit
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move => simp
      | query port next =>
        simp only [query, FreeM.queryBoundP_lift_bind (P := effects Oracle),
          FreeM.queryBoundP_pure, ENat.iSup_zero, add_zero]
        split <;> simp
    · simp [coin, FreeM.queryBoundP_lift (P := effects Oracle), hcoin]

/-- Selected oracle calls in a bounded execution are bounded by its transition fuel. -/
theorem queryBoundP_runConfigFrom_le (machine : MultiTapePTM k Bool State Oracle)
    (select : (effects Oracle).A → Bool) (hcoin : select (.inl ()) = false)
    (fuel : ℕ) (cfg : Config k Bool State Oracle input) :
    FreeM.queryBoundP select (machine.runConfigFrom fuel cfg) ≤ fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    rw [runConfigFrom_succ]
    exact (FreeM.queryBoundP_bind_le select _ _ fuel ih).trans (by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        add_le_add_right (queryBoundP_step_le machine select hcoin cfg) (fuel : ℕ∞))

/-- Observing the completed output adds no oracle calls. -/
theorem queryBoundP_run_le (machine : MultiTapePTM k Bool State Oracle)
    (select : (effects Oracle).A → Bool) (hcoin : select (.inl ()) = false)
    (fuel : ℕ) (input : List Bool) :
    FreeM.queryBoundP select (machine.run fuel input) ≤ fuel := by
  simpa only [run, runFrom, FreeM.queryBoundP_map] using
    queryBoundP_runConfigFrom_le machine select hcoin fuel (machine.initialConfig input)

end Turing.MultiTapePTM
