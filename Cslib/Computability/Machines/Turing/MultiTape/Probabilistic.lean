/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Machine
public import Cslib.Languages.Probabilistic.Basic

/-!
# Fair-coin multi-tape machines

`MultiTapePTM` specializes the common machine table to one action per Boolean coin value.
Its oracle type defaults to `Empty`, giving an oracle-free machine. An inhabited oracle type
enables named communication channels without changing the choice mechanism.

`runConfigFrom` unfolds one machine transition per unit of fuel. Its handler interprets
query instructions; it is external to the machine's step count. Keeping the handler explicit lets
the same execution theorem apply to plain oracle calls and to oracle substitution. It does not
assert that an arbitrary handler is efficient.

The complete configuration survives clock exhaustion, including pending query buffers.
The addition theorem is an equality of programs, so it preserves the interaction with every
stateful oracle, not only the distribution of the output.

The query handler can route several finite operation tags through a single shared game state.
This permits a hashing operation and another operation that internally uses the same hash oracle
to share a lazy-sampling table. The machine imposes neither independence between operations nor a
finite bound on their request domains. Finiteness of the operation type belongs to the PPT layer.
-/

@[expose] public section

namespace Turing

open Cslib

/-- A machine with one transition for each fresh fair coin; by default it has no oracle channels. -/
abbrev MultiTapePTM (k : ℕ) (Symbol State : Type) (Oracle : Type := Empty) :=
  MultiTapeMachine k Symbol State Oracle (fun α => Bool → α)

namespace MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {Response : Query → Type}
  {input : List Symbol} [DecidableEq Oracle]

/-- Unfold a bounded run, retaining the entire configuration on halting or clock exhaustion. -/
noncomputable def runConfigFrom (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol)) :
    ℕ → Config k Symbol State Oracle input →
      OracleComp Query Response (Config k Symbol State Oracle input)
  | 0, cfg => pure cfg
  | fuel + 1, cfg => match cfg.tapes.state with
    | none => pure cfg
    | some state => do
      let coin ← OracleComp.uniform Bool
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | .step action symbol move =>
        machine.runConfigFrom query fuel (cfg.step action symbol move)
      | .query oracle next =>
        let answer ← query oracle (cfg.channels oracle).queryBuffer
        machine.runConfigFrom query fuel (cfg.receive oracle next answer)

/-- Observe the output of a bounded execution. -/
noncomputable def runFrom (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    OracleComp Query Response (List Symbol) :=
  (fun final => final.tapes.output) <$> machine.runConfigFrom query fuel cfg

/-- Run from blank work and communication tapes. -/
noncomputable def run (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (fuel : ℕ) (input : List Symbol) : OracleComp Query Response (List Symbol) :=
  machine.runFrom query fuel (machine.initialConfig input)

@[simp] theorem runConfigFrom_zero (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFrom query 0 cfg = pure cfg := rfl

@[simp] theorem runConfigFrom_halted (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (h : cfg.tapes.state = none) :
    machine.runConfigFrom query fuel cfg = pure cfg := by
  cases fuel <;> simp [runConfigFrom, h]

/-- Pausing and resuming preserves the entire program and uses exactly the sum of the two clocks. -/
theorem runConfigFrom_add (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (first second : ℕ) (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFrom query (first + second) cfg =
      (machine.runConfigFrom query first cfg >>= machine.runConfigFrom query second) := by
  induction first generalizing cfg with
  | zero => simp
  | succ first ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [Nat.succ_add, runConfigFrom, hs, bind_assoc]
      congr 1
      funext coin
      split <;> simp [ih, bind_assoc]

/-- Resume a paused execution and then observe its output. -/
theorem runFrom_add (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (first second : ℕ) (cfg : Config k Symbol State Oracle input) :
    machine.runFrom query (first + second) cfg =
      (machine.runConfigFrom query first cfg >>= machine.runFrom query second) := by
  simp only [runFrom, runConfigFrom_add, map_bind]
  rfl

/-- Forget the fair-coin presentation, retaining precisely the permitted actions. This forgetful
map is useful for reachability; the probabilistic machine keeps its coin-indexed table. -/
def toNondeterministic (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapeMachine k Symbol State Oracle Set where
  initial := machine.initial
  tr state symbol work answer := Set.range (machine.tr state symbol work answer)

end MultiTapePTM

end Turing
