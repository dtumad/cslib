/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-!
# Polynomial-time certificates for finite word transducers

Finite control and a finite input alphabet give a uniform bound on emitted block lengths.
The deterministic transducer compiler therefore supplies a single finite machine with a linear
runtime bound, independently of the input. Clients need only specify the value-level transducer.
-/

@[expose] public section

namespace Cslib.Automata.DeterministicTransducer

open Probability Turing.MultiTapeTM

/-- Every finite-state binary word transducer computes a polynomial-time function. -/
theorem isPolyTime {α State : Type} [Finite State] (encode : α → Word)
    (transducer : DeterministicTransducer Bool Bool State) :
    IsPolyTime encode (fun a => transducer.eval (encode a)) := by
  classical
  let := Fintype.ofFinite State
  let width := Finset.univ.sup
    (fun pair : State × Option Bool => (Transducer.block transducer pair.1 pair.2).length)
  have hwidth (state : State) (symbol : Option Bool) :
      (Transducer.block transducer state symbol).length ≤ width :=
    Finset.le_sup (f := fun pair : State × Option Bool =>
      (Transducer.block transducer pair.1 pair.2).length) (Finset.mem_univ (state, symbol))
  apply isPolyTime_of_finite_machine (Transducer.machine transducer width) (width + 1) 1
  intro a
  have hrun := Transducer.computesInTimeAndSpace transducer width hwidth (encode a)
  simpa only [pow_one] using And.intro hrun.1 hrun.2.1

end Cslib.Automata.DeterministicTransducer
