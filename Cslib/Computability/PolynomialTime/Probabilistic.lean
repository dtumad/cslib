/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure

/-!
# Uniform probabilistic polynomial time

A certificate consists of one finite-control fair-coin machine and one polynomial clock,
fixed before the input. Halting is required on every coin and oracle-response path. Correctness
preserves the joint output and oracle state for every countable stateful kernel interpretation.
Named operations share that state; oracle execution is external to the transition clock.
The machine has finitely many communication ports and a fixed binding from ports to operation
names. Distinct ports may call the same operation, sharing its hidden state.

The output encoding is fixed and injective. Machine timeout remains distinct from every encoded
output, including an algorithm's own failure value. No efficient implementation is inferred from
finite result types, operation counts, or the existence of a separate machine for each input.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory MultiTapeTM

variable {Oracle : Type}
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- A bounded machine realizes a program against every countable stateful oracle environment.
The encoded output and the final shared state are compared together. -/
def Realizes {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
    (machine : MultiTapePTM k Bool State Ports) (dispatch : Ports → Oracle)
    (fuel : ℕ) (input : Word) (encode : α ↪ Word) (program : (effects Oracle).FreeM α) : Prop :=
  ∀ (S : Type) [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S)) (state : S),
    FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
      (machine.run fuel input) state =
      FreeM.runKernel (effectKernel oracle) ((fun a => some (encode a)) <$> program) state

/-- A single finite machine realizes all inputs within one pathwise polynomial clock.
The operation-name type is finite; query payloads and answers are arbitrary binary words. -/
def IsPPT {α β : Type} (input : α ↪ Word) (output : β ↪ Word)
    (program : α → (effects Oracle).FreeM β) : Prop :=
  Finite Oracle ∧ ∃ (k ports : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State (Fin ports)) (dispatch : Fin ports → Oracle) (c d : ℕ),
    ∀ a,
      machine.HaltsWithin (c * ((input a).length + 1) ^ d) (machine.initialConfig (input a)) ∧
      machine.Realizes dispatch (c * ((input a).length + 1) ^ d) (input a) output (program a)

/-- Once all paths halt, extending the clock preserves the complete interaction semantics. -/
theorem Realizes.mono {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
    {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle}
    {fuel fuel' : ℕ} {input : Word} {encode : α ↪ Word} {program : (effects Oracle).FreeM α}
    (h : machine.Realizes dispatch fuel input encode program)
    (hhalt : machine.HaltsWithin fuel (machine.initialConfig input)) (hle : fuel ≤ fuel') :
    machine.Realizes dispatch fuel' input encode program := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  intro S _ _ _ oracle state
  simpa only [run, runFrom, hhalt.runConfigFrom_add] using h S oracle state

end Turing.MultiTapePTM
