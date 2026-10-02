/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.ReplayInput
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RestoreWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeCall
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.UnaryRepeat
public import Cslib.Computability.Probabilistic.Iteration

/-!
# Checks for the shared probabilistic machine core

The reference evaluator below is the compact evaluator from before consolidation. Equality holds
for every machine, configuration and fuel bound, so it checks the whole interaction at cutoffs,
rather than only the output of a few terminating examples.

The concrete checks exercise an empty operation type, two communication channels sharing one
hidden oracle state, and typed game operations that share a lazy-sampling cache.
Deterministic replay checks include empty coins, clock exhaustion of a nonhalting source,
local query handling, virtual input reads, and early source halting.
Scratch-tape restoration checks cover negative positions, blank gaps, parallel cleanups
finishing at different times, repeated invocations, and an empty workspace and input.
Iteration checks include shrinking and empty replacement words, a computed zero count,
complete initialization from blank tapes, and a client proof using only word functions.
-/

@[expose] public section

namespace CslibTests.ComputationalCryptoMachines

open Cslib Turing

/-- The original bounded semantics, retained here as an independent reference. -/
noncomputable def referenceRunConfigFrom {k : ℕ} {State : Type} {input : List Bool}
    (machine : OracleTM k State) :
    ℕ → OracleTM.Config k State input →
      OracleComp (List Bool) (fun _ => List Bool) (OracleTM.Config k State input)
  | 0, cfg => pure cfg
  | fuel + 1, cfg => match cfg.tapes.state with
    | none => pure cfg
    | some state => do
      let coin ← OracleComp.uniform Bool
      match machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | .step action bit move =>
        referenceRunConfigFrom machine fuel (cfg.step action bit move)
      | .query next =>
        let answer ← OracleComp.query cfg.queryBuffer
        referenceRunConfigFrom machine fuel (cfg.receive next answer)

/-- Consolidation preserves the exact program at every fuel bound, not only its final output. -/
theorem runConfigFrom_reference {k : ℕ} {State : Type} {input : List Bool}
    (machine : OracleTM k State) (fuel : ℕ) (cfg : OracleTM.Config k State input) :
    machine.runConfigFrom fuel cfg = referenceRunConfigFrom machine fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp [referenceRunConfigFrom]
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [referenceRunConfigFrom, hs]
    | some state =>
      simp only [OracleTM.runConfigFrom_succ, referenceRunConfigFrom, hs]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin <;> simp only [ih]

/-- In particular, consolidation preserves the oracle's private state along with all tapes. -/
example {k : ℕ} {State OracleState : Type} {input : List Bool}
    (machine : OracleTM k State) (fuel : ℕ) (cfg : OracleTM.Config k State input)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (s : OracleState) :
    OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s =
      OracleComp.runState oracle (referenceRunConfigFrom machine fuel cfg) s := by
  rw [runConfigFrom_reference]

/-- A genuinely oracle-free fair-coin machine. There is no query constructor it can use. -/
def coinMachine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ coin := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := none }
    Empty.elim Empty.elim

example :
    ProbComp.eval (MultiTapePTM.run coinMachine (fun operation => operation.elim) 1 []) =
      (PMF.uniformOfFintype Bool).map (fun coin => [coin]) := by
  simp [MultiTapePTM.run, MultiTapePTM.runFrom, MultiTapePTM.runConfigFrom, coinMachine,
    MultiTapeMachine.initialConfig, MultiTapeMachine.Config.step, Cfg.init, Action.apply,
    OracleComp.uniform, PMF.map, Function.comp_def]

inductive Operation where
  | left
  | right
  deriving DecidableEq

instance : Fintype Operation :=
  ⟨{.left, .right}, fun operation => by cases operation <;> simp⟩

/-- Query each channel once, then check the two separately retained replies. -/
def twoChannelMachine : MultiTapePTM 0 Bool (Fin 3) Operation where
  initial := 0
  tr state _ _ answer _ :=
    if state = 0 then .query .left 1
    else if state = 1 then .query .right 2
    else .step
      { inputTape := 0
        workTapes := Fin.elim0
        output := some (answer .left == some false && answer .right == some true)
        state := none }
      (fun _ => none) (fun _ => 0)

/-- The two operations share this state; the second call observes the first call's update. -/
noncomputable def alternating (_ : Operation × List Bool) : StateT Bool PMF (List Bool) :=
  fun state => PMF.pure ([state], !state)

example :
    OracleComp.runState alternating
      (MultiTapePTM.run twoChannelMachine
        (fun operation word => OracleComp.query (operation, word)) 3 []) false =
      PMF.pure ([true], false) := by
  simp [MultiTapePTM.run, MultiTapePTM.runFrom, MultiTapePTM.runConfigFrom, twoChannelMachine,
    MultiTapeMachine.initialConfig, MultiTapeMachine.Config.step, MultiTapeMachine.Config.receive,
    MultiTapeMachine.Config.answerSymbols, MultiTapeMachine.Channel.answerSymbol, alternating,
    Cfg.init, Action.apply, OracleComp.uniform, PMF.map, Function.comp_def]

end CslibTests.ComputationalCryptoMachines

namespace CslibTests.ComputationalCryptoMachines.Replay
open Turing

/-- Alternate an input-dependent output with a query, forever. -/
def looping : OracleTM 0 Bool := OracleTM.mk false fun querying symbol _ _ coin =>
  if querying then .query false else .step
    { inputTape := 1, workTapes := Fin.elim0
      output := some (coin ^^ symbol.getD false), state := some true }
    (some coin) (-1)

/-- Even a nonhalting source stops before its first transition when no coins are supplied. -/
example :
    let final := looping.replayInput.runFrom
      (looping.replayInput.initCfg (MultiTapeTM.PrepareReplay.encode [] [])) 12
    final.state = none ∧ final.output = [] := by decide

/-- The middle coin pays for the query; the first and third coins produce the two outputs. -/
example :
    let final := looping.replayInput.runFrom
      (looping.replayInput.initCfg
        (MultiTapeTM.PrepareReplay.encode [true, false, false] [false, true])) 36
    final.state = none ∧ final.output = [true, true] := by decide

/-- A source which halts after one output leaves the remaining stored coins unused. -/
def halting : OracleTM 0 Unit := OracleTM.mk () fun _ _ _ _ coin => .step
  { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := none } none 0

example :
    let final := halting.replayInput.runFrom
      (halting.replayInput.initCfg
        (MultiTapeTM.PrepareReplay.encode [false, true, true] [true])) 33
    final.state = none ∧ final.output = [false] := by decide

end CslibTests.ComputationalCryptoMachines.Replay

namespace CslibTests.ComputationalCryptoMachines.Restore
open Turing MultiTapeTM

/-- Leave data on both sides of the origin, blank gaps, and two different final head positions.
The first output also checks that both scratch tapes were blank at entry. -/
def dirty : MultiTapeTM 2 Bool (Fin 5) where
  q₀ := 0
  tr state symbol work :=
    if state = 0 then
      { inputTape := 1,
        workTapes := fun i => (some (some (i = 0)), if i = 0 then -1 else 1),
        output := some (work 0 == none && work 1 == none), state := some 1 }
    else if state = 1 then
      { inputTape := 0, workTapes := fun i => (none, if i = 0 then -1 else 1),
        output := some false, state := some 2 }
    else if state = 2 then
      { inputTape := 1,
        workTapes := fun i => (some (some (i ≠ 0)), if i = 0 then 1 else 0),
        output := none, state := some 3 }
    else if state = 3 then
      { inputTape := 0, workTapes := fun i => (none, if i = 0 then 1 else -1),
        output := some (symbol.getD false), state := some 4 }
    else
      { inputTape := 0, workTapes := fun i => (none, if i = 0 then -1 else 1),
        output := none, state := none }

set_option maxRecDepth 8192 in
/-- Evaluate the compiled transitions directly, including clearing through blank gaps. -/
example :
    let final := dirty.restoreWork.runFrom (dirty.restoreWork.initCfg [true, false, true]) 47
    final.state = none ∧ final.inputPos = 1 ∧ final.output = [true, false, true] ∧
      ∀ i : Fin 4, final.workTapePos i = 0 ∧
        ([-3, -2, -1, 0, 1, 2, 3] : List ℤ).all (fun z => final.workTapes i z == none) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The second invocation sees fresh scratch tapes and the restored input head. -/
example :
    let routine := dirty.restoreWork.repeatUnary
    let initial := wordsCfg [true, false, true] (some routine.q₀)
      (Fin.lastCases [true, true] (fun _ => [])) [false]
    let final := routine.runFrom initial 102
    final.state = none ∧ final.inputPos = 1 ∧
      final.output = [false, true, false, true, true, false, true] ∧
      final.workTapePos (Fin.last 4) = 0 ∧
      final.workTapes (Fin.last 4) 0 = some true ∧
      final.workTapes (Fin.last 4) 1 = some true ∧
      ∀ i : Fin 4, final.workTapePos i.castSucc = 0 ∧
        ([-3, -2, -1, 0, 1, 2, 3] : List ℤ).all
          (fun z => final.workTapes i.castSucc z == none) = true := by
  decide +kernel

/-- Zero source tapes and an empty input still restore the native input boundary correctly. -/
def noScratch : MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputTape := -1, workTapes := Fin.elim0, output := some false, state := none }

example :
    let routine := noScratch.restoreWork
    let final := routine.runFrom (wordsCfg [] (some routine.q₀) (fun _ => []) [true]) 16
    final.state = none ∧ final.inputPos = 1 ∧ final.output = [true, false] := by
  decide

end CslibTests.ComputationalCryptoMachines.Restore

namespace CslibTests.ComputationalCryptoMachines.Loops
open Turing MultiTapeTM

/-- Flip a stored bit, taking one step on true and two steps on false. -/
def variableStop : MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr waiting _ work :=
    if waiting then
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
    else
      let bit := (work 0).getD false
      { inputTape := 0, workTapes := fun _ => (some (some !bit), 0),
        output := none, state := if bit then none else some true }

set_option maxRecDepth 8192 in
/-- Three changing word states, with different first halting times, fit the common body bound. -/
example :
    let routine := variableStop.repeatUnary
    let initial := wordsCfg [] (some routine.q₀)
      (Fin.lastCases [true, true, true] (fun _ => [true])) [false]
    let final := routine.runFrom initial 17
    final.state = none ∧ final.inputPos = 1 ∧ final.output = [false] ∧
      final.workTapes 0 0 = some false ∧
      (List.range 3).all (fun i => final.workTapes 1 i == some true) = true ∧
      ∀ i : Fin 2, final.workTapePos i = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The call reads its buffered argument, preserves ambient output, and clears its boundary flag. -/
example :
    let routine := Restore.dirty.restoreWork.tapeCall
    let initial := wordsCfg [false, false] (some routine.q₀)
      (TapeCall.words 4 [true, false, true] []) [false]
    let final := routine.runFrom initial 56
    final.state = none ∧ final.inputPos = 1 ∧ final.output = [false] ∧
      ([-1, 0, 1, 2, 3] : List ℤ).map (final.workTapes 4) =
        [none, some true, some false, some true, none] ∧
      ([-1, 0, 1, 2, 3] : List ℤ).map (final.workTapes 5) =
        [none, some true, some false, some true, none] ∧
      final.workTapes 6 (-1) = none ∧ final.workTapes 6 0 = none ∧
      (∀ i : Fin 7, final.workTapePos i = 0) ∧
      ∀ i : Fin 4, ([-3, -2, -1, 0, 1, 2, 3] : List ℤ).all
        (fun z => final.workTapes (i.castAdd 3) z == none) = true := by
  decide +kernel

/-- Emit the complement of the first input bit, leaving the input head displaced. -/
def negateFirst : MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ symbol _ :=
    { inputTape := 1, workTapes := Fin.elim0, output := some !(symbol.getD false), state := none }

set_option maxRecDepth 8192 in
/-- The argument shrinks from three bits to one; later iterations cannot retain its old tail. -/
example :
    let routine := negateFirst.restoreWork.tapeUpdate.repeatUnary
    let initial := wordsCfg [] (some routine.q₀)
      (Fin.lastCases [true, true, true] (TapeCall.words 0 [true, false, true] [])) [true, false]
    let final := routine.runFrom initial 125
    final.state = none ∧ final.inputPos = 1 ∧ final.output = [true, false] ∧
      final.workTapes 1 0 = some false ∧ final.workTapes 1 1 = none ∧
      final.workTapes 1 2 = none ∧
      ([-1, 0, 1] : List ℤ).all (fun z => final.workTapes 0 z == none) = true ∧
      final.workTapes 2 (-1) = none ∧ final.workTapes 2 0 = none ∧
      (List.range 3).all (fun i => final.workTapes 3 i == some true) = true ∧
      ∀ i : Fin 4, final.workTapePos i = 0 := by
  decide +kernel

/-- A finite controller writes the unary count three. -/
def three : MultiTapeTM 0 Bool (Fin 4) where
  q₀ := 0
  tr state _ _ :=
    if h : state.val < 3 then
      { inputTape := 0, workTapes := Fin.elim0, output := some true,
        state := some ⟨state.val + 1, by lia⟩ }
    else
      { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

set_option maxRecDepth 8192 in
/-- Execute the entire compiler from blank tapes, including both initializers and final output. -/
example :
    let routine := Iteration.machine copy.restoreWork three.restoreWork negateFirst.restoreWork
    let final := routine.runFrom (routine.initCfg [true, false, true]) 213
    final.state = none ∧ final.output = [false] := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- A computed zero count emits the initial word without calling the step function. -/
example :
    let routine := Iteration.machine copy.restoreWork (nop 0 Bool).restoreWork
      negateFirst.restoreWork
    let final := routine.runFrom (routine.initCfg [true, false]) 61
    final.state = none ∧ final.output = [true, false] := by
  decide +kernel

/-- Moving an empty word clears the entire old destination and restores every head. -/
example :
    let routine := TransferWord.machine true true
    let final := routine.runFrom (wordsCfg [false] (some routine.q₀) ![[], [true, false], []]
      [true]) 6
    final.state = none ∧ final.output = [true] ∧ final.inputPos = 1 ∧
      ∀ i : Fin 3, final.workTapePos i = 0 ∧
        ([-1, 0, 1, 2] : List ℤ).all (fun z => final.workTapes i z == none) = true := by
  decide +kernel

open Cslib Cslib.Probability in
/-- Clients can certify a length-nonincreasing loop without mentioning a machine or tape. -/
example {initial : Word → Word} {count : Word → ℕ} {step : Word → Word}
    (hi : IsPolyTime wordEncoding initial)
    (hc : IsPolyTime wordEncoding (fun word => List.replicate (count word) true))
    (hs : IsPolyTime wordEncoding step)
    (hlen : ∀ word, (step word).length ≤ word.length) :
    IsPolyTime wordEncoding (fun word => step^[count word] (initial word)) :=
  hi.iterate_of_length_le hc hs hlen

end CslibTests.ComputationalCryptoMachines.Loops



/- A single-bit lazy random oracle, shared between two typed game operations. -/
namespace CslibTests.ComputationalCryptoMachines.SharedRandomOracle
open Cslib

inductive Operation where
  | hash
  | hashPair
  deriving DecidableEq

instance : Fintype Operation :=
  ⟨{.hash, .hashPair}, fun operation => by cases operation <;> simp⟩

abbrev Request : Operation → Type
  | .hash => List Bool
  | .hashPair => List Bool × List Bool

abbrev Response : (operation : Operation) → Request operation → Type
  | .hash, _ => Bool
  | .hashPair, _ => Bool × Bool

abbrev Query := (operation : Operation) × Request operation
abbrev Game := OracleComp Query (fun query => Response query.1 query.2)
abbrev Cache := List Bool → Option Bool

def call (operation : Operation) (request : Request operation) :
    Game (Response operation request) :=
  OracleComp.query (Query := Query) (Response := fun query => Response query.1 query.2)
    ⟨operation, request⟩

noncomputable def hash (message : List Bool) : StateT Cache PMF Bool :=
  fun cache => match cache message with
  | some answer => PMF.pure (answer, cache)
  | none => (PMF.uniformOfFintype Bool).map
      (fun answer => (answer, Function.update cache message (some answer)))

noncomputable def handler (query : Query) : StateT Cache PMF (Response query.1 query.2) :=
  match query with
  | ⟨.hash, message⟩ => hash message
  | ⟨.hashPair, (left, right)⟩ => fun cache =>
      (hash left cache).bind fun (first, cache') =>
        (hash right cache').map fun (second, cache'') => ((first, second), cache'')

def experiment (message : List Bool) : Game Bool := do
  let first : Bool ← call .hash message
  let pair : Bool × Bool ← call .hashPair (message, message)
  pure (first == pair.1 && first == pair.2)

theorem shared_cache (message : List Bool) :
    OracleComp.runState handler (experiment message) (fun _ => none) =
      (PMF.uniformOfFintype Bool).map
        (fun answer => (true, Function.update (fun _ => none) message (some answer))) := by
  simp [experiment, call, OracleComp.runState_bind, OracleComp.runState_query,
    handler, hash, PMF.map, Function.comp_def]
end CslibTests.ComputationalCryptoMachines.SharedRandomOracle

namespace CslibTests.ComputationalCryptoMachines.Transducers

open Cslib.Automata Turing Turing.MultiTapeTM

/-- Skip false bits, expand true bits, and emit the parity as a final block. -/
private def sparse : DeterministicTransducer Bool Bool Bool where
  initial := false
  next := Bool.xor
  output _ bit := if bit then [true, false] else []
  finish state := [state]

/-- Variable-size blocks, including empty blocks, and the final output all reach the machine. -/
example :
    let routine := Transducer.machine sparse 2
    let final := routine.runFrom (routine.initCfg [true, false, true]) 12
    final.state = none ∧ final.output = [true, false, true, false, false] := by
  decide +kernel

/-- The final transition is charged even after the final block has been written. -/
example :
    let routine := Transducer.machine sparse 2
    (routine.runFrom (routine.initCfg [true, false, true]) 11).state ≠ none := by
  decide +kernel

/-- An empty input still emits the final block. -/
example :
    let routine := Transducer.machine sparse 2
    let final := routine.runFrom (routine.initCfg []) 3
    final.state = none ∧ final.output = [false] := by
  decide +kernel

/-- A width-zero transducer scans the input and halts without emitting any symbols. -/
example :
    let routine := Transducer.machine (DeterministicTransducer.flatMap (fun _ : Bool => [])) 0
    let final := routine.runFrom (routine.initCfg [true, false, true]) 4
    final.state = none ∧ final.output = [] := by
  decide +kernel

end CslibTests.ComputationalCryptoMachines.Transducers
