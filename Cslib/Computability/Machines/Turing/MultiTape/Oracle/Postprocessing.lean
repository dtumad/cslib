/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Postprocessing

/-!
# Mapping the output bits of an oracle machine

A fixed Boolean function can be applied to each emitted bit in the same transition. The machine
does not read its output tape, so this changes neither subsequent control flow nor oracle queries.
In particular, complementing an adversary's final Boolean answer preserves PPT, with the same clock.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State : Type}

/-- Apply a fixed Boolean function to each emitted bit, using the common machine construction. -/
@[simps! initial] def mapOutput (machine : OracleTM k State) (f : Bool → Bool) : OracleTM k State :=
  MultiTapePTM.mapOutput machine f

/-- Postprocessing preserves the entire oracle interaction and the clock. -/
theorem run_mapOutput (machine : OracleTM k State) (f : Bool → Bool) (fuel : ℕ)
    (input : List Bool) :
    (machine.mapOutput f).run fuel input = List.map f <$> machine.run fuel input := by
  simpa only [mapOutput, run_core] using MultiTapePTM.run_mapOutput machine
    (fun _ => OracleComp.query) f fuel input

end Turing.OracleTM
