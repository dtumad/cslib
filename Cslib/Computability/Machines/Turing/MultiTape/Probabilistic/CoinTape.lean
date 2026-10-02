/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Probability.BitString

/-!
# Explicit random tapes

`runConfigFromCoins` replays the shared fair-coin machine using a supplied list of bits.
Every live transition, including a query instruction, consumes one bit. An exhausted list returns
the complete current configuration. A halted machine ignores any remaining bits.

Sampling a tape of length `fuel` uniformly in advance gives exactly the original clocked
execution, including the final state of every stateful oracle. In the query case the proof
commutes an independent draw of the remaining private coins with the query handler's effects.
Thus the result also applies to randomized handlers and several operations sharing one state.

The replay function is monad-polymorphic. With deterministic replies it specializes to `Id`,
giving a deterministic function of the input and random tape. This operational equality does
not by itself certify a deterministic machine implementing replay from an encoded pair of tapes.
-/

@[expose] public section

namespace Turing.MultiTapePTM
open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {Response : Query → Type}
  {input : List Symbol} [DecidableEq Oracle]

/-- Replay a machine with an explicit coin list, stopping on halting or when the list ends.
Only the query handler can have effects; replay itself draws no randomness. -/
def runConfigFromCoins {m : Type → Type*} [Monad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → m (List Symbol)) :
    List Bool → Config k Symbol State Oracle input → m (Config k Symbol State Oracle input)
  | [], cfg => pure cfg
  | coin :: coins, cfg => match cfg.tapes.state with
    | none => pure cfg
    | some state =>
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | .step action symbol move =>
        runConfigFromCoins machine query coins (cfg.step action symbol move)
      | .query oracle next => do
        let answer ← query oracle (cfg.channels oracle).queryBuffer
        runConfigFromCoins machine query coins (cfg.receive oracle next answer)

/-- A halted machine ignores the remaining coins. -/
theorem runConfigFromCoins_halted {m : Type → Type*} [Monad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → m (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input)
    (h : cfg.tapes.state = none) : runConfigFromCoins machine query coins cfg = pure cfg := by
  cases coins <;> simp [runConfigFromCoins, h]

/-- Sampling all machine coins in advance preserves the final configuration and the oracle's
private state. The sampled tape is private to the machine. -/
theorem runState_runConfigFrom_eq_coins {OracleState : Type}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (Response q))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    OracleComp.runState oracle (runConfigFrom machine query fuel cfg) s =
      (uniformBits fuel).bind (fun coins =>
        runConfigFromCoins machine (fun op word => OracleComp.runState oracle (query op word))
          coins cfg s) := by
  induction fuel generalizing cfg s with
  | zero => simp [runConfigFromCoins]; rfl
  | succ fuel ih =>
    rw [uniformBits_succ]
    cases hstate : cfg.tapes.state with
    | none => simp [runConfigFrom, hstate, runConfigFromCoins_halted]; rfl
    | some state =>
      simp only [runConfigFrom, hstate, OracleComp.runState_bind, OracleComp.uniform,
        OracleComp.runState_sample, PMF.bind_map, Function.comp_def, PMF.bind_bind]
      congr 1
      funext coin
      cases haction : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        simp only [runConfigFromCoins, hstate, haction]
        exact ih _ _
      | query op next =>
        simp only [runConfigFromCoins, hstate, haction, OracleComp.runState_bind]
        simp_rw [ih]
        exact PMF.bind_comm _ _ _

/-- Stateful interpretation commutes with replaying a fixed coin tape. -/
theorem runState_runConfigFromCoins {OracleState : Type}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (Response q))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    OracleComp.runState oracle (runConfigFromCoins machine query coins cfg) s =
      runConfigFromCoins machine (fun op word => OracleComp.runState oracle (query op word))
        coins cfg s := by
  induction coins generalizing cfg s with
  | nil => rfl
  | cons coin coins ih =>
    cases hstate : cfg.tapes.state with
    | none => simp [runConfigFromCoins, hstate]; rfl
    | some state =>
      simp only [runConfigFromCoins, hstate]
      cases haction : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move => exact ih _ _
      | query op next =>
        simp only [OracleComp.runState_bind]
        change (_ : PMF _) = (OracleComp.runState oracle (query _ _) s).bind _
        congr 1
        funext pair
        exact ih _ _

/-- A clocked execution is the average of its fixed-coin executions. -/
theorem eval_runConfigFrom_eq_coins
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → PMF (Response q))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    OracleComp.eval oracle (runConfigFrom machine query fuel cfg) =
      (uniformBits fuel).bind (fun coins =>
        OracleComp.eval oracle (runConfigFromCoins machine query coins cfg)) := by
  have h := runState_runConfigFrom_eq_coins machine query
    (fun q (s : Unit) => (oracle q).map (fun a => (a, s))) fuel cfg ()
  simp_rw [← runState_runConfigFromCoins, OracleComp.runState_stateless] at h
  have h' := congrArg (PMF.map Prod.fst) h
  simpa [PMF.map, Function.comp_def] using h'

/-- Deterministic replies make a fixed-coin execution deterministic. -/
theorem eval_runConfigFromCoins_of_pure
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → PMF (Response q))
    (answer : Oracle → List Symbol → List Symbol)
    (hquery : ∀ op word, OracleComp.eval oracle (query op word) = PMF.pure (answer op word))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input) :
    OracleComp.eval oracle (runConfigFromCoins machine query coins cfg) =
      PMF.pure (runConfigFromCoins (m := Id) machine answer coins cfg) := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons coin coins ih =>
    cases hstate : cfg.tapes.state with
    | none => simp [runConfigFromCoins, hstate]; rfl
    | some state =>
      simp only [runConfigFromCoins, hstate]
      split
      · exact ih _
      · simp only [OracleComp.eval_bind, hquery, PMF.pure_bind]
        exact ih _

/-- With deterministic replies, execution is a deterministic function of a uniform coin tape. -/
theorem eval_runConfigFrom_eq_map_coins
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → PMF (Response q))
    (answer : Oracle → List Symbol → List Symbol)
    (hquery : ∀ op word, OracleComp.eval oracle (query op word) = PMF.pure (answer op word))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    OracleComp.eval oracle (runConfigFrom machine query fuel cfg) =
      (uniformBits fuel).map (fun coins =>
        runConfigFromCoins (m := Id) machine answer coins cfg) := by
  rw [eval_runConfigFrom_eq_coins]
  simp_rw [eval_runConfigFromCoins_of_pure machine query oracle answer hquery]
  rfl

/-- Observe the output of a fixed-coin execution. -/
def runFromCoins {m : Type → Type*} [Monad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → m (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input) : m (List Symbol) :=
  (fun final => final.tapes.output) <$> runConfigFromCoins machine query coins cfg

/-- Replay from blank work and communication tapes. -/
def runCoins {m : Type → Type*} [Monad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → m (List Symbol))
    (coins : List Bool) (input : List Symbol) : m (List Symbol) :=
  runFromCoins machine query coins (machine.initialConfig input)

/-- A run from the initial configuration is a deterministic function of its coins when the
query replies are deterministic. -/
theorem eval_run_eq_map_coins
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (oracle : (q : Query) → PMF (Response q))
    (answer : Oracle → List Symbol → List Symbol)
    (hquery : ∀ op word, OracleComp.eval oracle (query op word) = PMF.pure (answer op word))
    (fuel : ℕ) (input : List Symbol) :
    OracleComp.eval oracle (run machine query fuel input) =
      (uniformBits fuel).map (fun coins => runCoins (m := Id) machine answer coins input) := by
  simp only [run, runFrom, OracleComp.eval_map,
    eval_runConfigFrom_eq_map_coins machine query oracle answer hquery, PMF.map_comp]
  rfl

/-- Replaying concatenated coin tapes agrees with pausing and resuming at their boundary. -/
theorem runConfigFromCoins_append {m : Type → Type*} [Monad m] [LawfulMonad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → m (List Symbol))
    (coins more : List Bool) (cfg : Config k Symbol State Oracle input) :
    runConfigFromCoins machine query (coins ++ more) cfg =
      (runConfigFromCoins machine query coins cfg >>= runConfigFromCoins machine query more) := by
  induction coins generalizing cfg with
  | nil => simp [runConfigFromCoins]
  | cons coin coins ih =>
    cases hstate : cfg.tapes.state with
    | none => simp [runConfigFromCoins, hstate, runConfigFromCoins_halted]
    | some state =>
      simp only [List.cons_append, runConfigFromCoins, hstate]
      split <;> simp [ih, bind_assoc]

end Turing.MultiTapePTM
