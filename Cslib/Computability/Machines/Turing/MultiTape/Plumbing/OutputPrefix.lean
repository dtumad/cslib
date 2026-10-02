/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Preserving previously written output

A machine cannot inspect or overwrite its output tape. Prepending previously written output
therefore commutes with every step and with an entire run. These lemmas are adapted from the
`concat-combinator` branch's `Plumbing/Basic` module to the current configuration API.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A step cannot observe the output accumulated before it. -/
theorem step_prependOutput (tm : MultiTapeTM k Symbol State) (pre : List Symbol)
    (cfg : Cfg k Symbol State input) :
    tm.step (cfg.prependOutput pre) = (tm.step cfg).prependOutput pre := by
  cases hs : cfg.state <;> simp [step, hs, Action.apply_prependOutput]

/-- Previously accumulated output survives an entire run unchanged. -/
theorem runFrom_prependOutput (tm : MultiTapeTM k Symbol State) (pre : List Symbol)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) :
    tm.runFrom (cfg.prependOutput pre) fuel = (tm.runFrom cfg fuel).prependOutput pre :=
  (Function.Semiconj.iterate_right (f := (Cfg.prependOutput · pre))
    (fun cfg => (step_prependOutput tm pre cfg).symm) fuel cfg).symm

end Turing.MultiTapeTM
