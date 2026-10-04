/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Simulations preserving the complete interaction

A simulation of one transition extends to every clocked run. Equality of free programs retains
all coin choices, named requests, and continuations, independently of an oracle interpretation.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {k k' : ℕ} {State State' Oracle : Type} [DecidableEq Oracle]
  {input input' : List Bool}

/-- A map commuting with one transition commutes with every bounded run. -/
theorem runConfigFrom_simulation (source : MultiTapePTM k Bool State Oracle)
    (target : MultiTapePTM k' Bool State' Oracle)
    (embed : Config k Bool State Oracle input → Config k' Bool State' Oracle input')
    (hstep : ∀ cfg, target.step (embed cfg) = embed <$> source.step cfg)
    (fuel : ℕ) (cfg : Config k Bool State Oracle input) :
    target.runConfigFrom fuel (embed cfg) = embed <$> source.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    simp only [runConfigFrom_succ, hstep, bind_map_left, map_bind]
    exact bind_congr ih

end Turing.MultiTapePTM
