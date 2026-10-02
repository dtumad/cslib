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

/-- Oracle substitution commutes with clocked execution. The handler may share private state
across all operation names. -/
theorem simulate_runConfigFrom {Query' : Type} {Response' : Query' → Type}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp.simulate handler (machine.runConfigFrom query fuel cfg) =
      machine.runConfigFrom (fun op word => OracleComp.simulate handler (query op word))
        fuel cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [runConfigFrom, hs, OracleComp.simulate_bind, OracleComp.uniform,
        OracleComp.simulate_sample]
      congr 1
      funext coin
      split <;> simp only [OracleComp.simulate_bind, ih]

/-- Substituting the query handler preserves the complete output program. -/
theorem simulate_run {Query' : Type} {Response' : Query' → Type}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (fuel : ℕ)
    (input : List Symbol) :
    OracleComp.simulate handler (machine.run query fuel input) =
      machine.run (fun op word => OracleComp.simulate handler (query op word)) fuel input := by
  simp only [run, runFrom, OracleComp.simulate_map, simulate_runConfigFrom]

@[simp] theorem runFrom_zero (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (cfg : Config k Symbol State Oracle input) : machine.runFrom query 0 cfg =
      pure cfg.tapes.output := by simp [runFrom, runConfigFrom]

/-- Unfold one transition while observing only the output. -/
theorem runFrom_succ (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    machine.runFrom query (fuel + 1) cfg = (match cfg.tapes.state with
    | none => pure cfg.tapes.output
    | some state => do
      let coin ← OracleComp.uniform Bool
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | .step action symbol move => machine.runFrom query fuel (cfg.step action symbol move)
      | .query oracle next => do
        let answer ← query oracle (cfg.channels oracle).queryBuffer
        machine.runFrom query fuel (cfg.receive oracle next answer)) := by
  cases hs : cfg.tapes.state with
  | none => simp [runFrom, runConfigFrom, hs]
  | some state =>
    simp only [runFrom, runConfigFrom, hs, map_bind]
    congr 1
    funext coin
    split <;> simp only [map_bind]

/-- Every supported execution writes at most one output symbol per transition, regardless of
the lengths of oracle replies or the private state shared by the handlers. -/
theorem length_output_runFrom_le {OracleState : Type}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (Response q)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) (s s' : OracleState) (output : List Symbol)
    (h : (output, s') ∈ (OracleComp.runState oracle (machine.runFrom query fuel cfg) s).support) :
    output.length ≤ cfg.tapes.output.length + fuel := by
  induction fuel generalizing cfg s with
  | zero =>
    simp only [runFrom_zero, OracleComp.runState_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    simp [h.1]
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runFrom_succ, hs, OracleComp.runState_pure, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at h
      simp [h.1]
    | some state =>
      simp only [runFrom_succ, hs, OracleComp.uniform, OracleComp.runState_sample_bind,
        PMF.mem_support_bind_iff] at h
      obtain ⟨coin, _, h⟩ := h
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        rw [ha] at h
        have hout := ih _ _ h
        have hstep : (cfg.step action symbol move).tapes.output.length ≤
            cfg.tapes.output.length + 1 := by
          simp only [Config.step, Turing.Action.apply, List.length_append]
          exact Nat.add_le_add_left action.output.length_toList_le _
        lia
      | query op next =>
        simp only [ha, OracleComp.runState_bind, PMF.mem_support_bind_iff] at h
        obtain ⟨⟨answer, nextState⟩, _, h⟩ := h
        have hout := ih _ _ h
        simp only [Config.receive] at hout
        lia

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
