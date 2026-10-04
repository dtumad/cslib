/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Automata.Transducers.Transducer

/-!
# Deterministic word transducers

A deterministic transducer reads one input symbol at a time, updates its state, and emits a word.
It may also emit a final word after reading the input. Finiteness of the control is imposed by
clients that need a finite-state machine. The evaluation and translation relation contain no
Turing-machine representations or resource accounting.
-/

@[expose] public section

namespace Cslib.Automata

/-- A deterministic transducer with an output word at each transition and at the end of input. -/
structure DeterministicTransducer (InSymbol OutSymbol : Type v) (State : Type u) where
  /-- Initial control state. -/
  initial : State
  /-- The next state after reading a symbol. -/
  next : State → InSymbol → State
  /-- The word emitted while reading a symbol. -/
  output : State → InSymbol → List OutSymbol
  /-- The word emitted at the end of input. -/
  finish : State → List OutSymbol

namespace DeterministicTransducer

variable {InSymbol OutSymbol : Type v} {State : Type u}

/-- Evaluate the transducer from a supplied state. -/
def evalFrom (machine : DeterministicTransducer InSymbol OutSymbol State) :
    State → List InSymbol → List OutSymbol
  | state, [] => machine.finish state
  | state, symbol :: input =>
    machine.output state symbol ++ machine.evalFrom (machine.next state symbol) input

/-- Evaluate the transducer from its initial state. -/
def eval (machine : DeterministicTransducer InSymbol OutSymbol State) (input : List InSymbol) :
    List OutSymbol := machine.evalFrom machine.initial input

instance : Transducer (DeterministicTransducer InSymbol OutSymbol State) InSymbol OutSymbol where
  Translates machine input output := machine.eval input = output

/-- Substitute a fixed word for each input symbol. -/
def flatMap (code : InSymbol → List OutSymbol) :
    DeterministicTransducer InSymbol OutSymbol Unit where
  initial := ()
  next _ _ := ()
  output _ symbol := code symbol
  finish _ := []

@[simp] theorem eval_flatMap (code : InSymbol → List OutSymbol) (input : List InSymbol) :
    (flatMap code).eval input = input.flatMap code := by
  change (flatMap code).evalFrom () input = _
  induction input with
  | nil => rfl
  | cons symbol input ih => simpa [evalFrom, flatMap] using congrArg (code symbol ++ ·) ih

/-- Accumulate a state while scanning the input and emit a word determined by the final state. -/
def fold (next : State → InSymbol → State) (initial : State)
    (finish : State → List OutSymbol) : DeterministicTransducer InSymbol OutSymbol State where
  initial := initial
  next := next
  output _ _ := []
  finish := finish

@[simp] theorem eval_fold (next : State → InSymbol → State) (initial : State)
    (finish : State → List OutSymbol) (input : List InSymbol) :
    (fold next initial finish).eval input = finish (input.foldl next initial) := by
  have h (state : State) :
      (fold next initial finish).evalFrom state input = finish (input.foldl next state) := by
    induction input generalizing state with
    | nil => rfl
    | cons symbol input ih => simpa [evalFrom, fold] using ih (next state symbol)
  exact h initial

end DeterministicTransducer
end Cslib.Automata
