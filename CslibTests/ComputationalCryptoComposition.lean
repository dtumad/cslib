/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Probabilistic.Composition
import Cslib.Computability.Probabilistic.Input
import Cslib.Computability.Probabilistic.PolynomialTime
import Cslib.Computability.Probabilistic.Sampling

/-!
# Computational composition checks

These examples exercise data preparation, random stopping times, pending queries across shared
tape sequencing, and adaptive use of a sampled parameter through the high-level PPT interface.
-/

namespace CslibTests.ComputationalCryptoComposition

open Cslib Cslib.Probability Turing

/-- Leave a written tape, a displaced work head and the input head at the left boundary. -/
private def leaveData : MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr _ symbol _ := ⟨-1, fun _ => (some (some true), 1), symbol, none⟩

/-- This continuation accepts its input symbol only if its own work tape is still blank. -/
private def freshEcho : MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr _ symbol work :=
    ⟨0, fun _ => (none, 0), if work 0 = none then symbol else some false, none⟩

/-- A one-step emitter for checking handoffs with no work tapes. -/
private def emitBit (bit : Bool) : MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨0, Fin.elim0, some bit, none⟩

/-- Concatenation restores the input, preserves the first output and gives the continuation
fresh tapes, while leaving the first machine's written tape and displaced head intact. -/
example :
    let machine := leaveData.concat freshEcho
    let final := machine.runFrom (machine.initCfg [true, false]) 6
    final.state = none ∧ final.output = [true, true] ∧ final.inputPos = 1 ∧
      final.workTapes 0 0 = some true ∧ final.workTapePos 0 = 1 ∧
      final.workTapes 1 0 = none ∧ final.workTapePos 1 = 0 := by
  decide

/-- Empty input and zero work tapes still preserve both outputs across the rewind. -/
example :
    let machine := (emitBit true).concat (emitBit false)
    let final := machine.runFrom (machine.initCfg []) 4
    final.state = none ∧ final.output = [true, false] := by
  decide

set_option maxRecDepth 4096 in

/-- Buffer preparation preserves source data and heads, including a displaced outer input head. -/
example :
    let cfg : Cfg 1 Bool Bool [false, true] :=
      { wordsCfg [false, true] (some true) (fun _ => [true]) [false, true, false] with
        inputPos := 2
        workTapePos := fun _ => 3 }
    let machine := MultiTapeTM.prepareInput 1
    let final := machine.runFrom
      ((MultiTapeTM.PrepareInput.before cfg).withState (some machine.q₀)) 7
    final.state = none ∧ final.output = [] ∧ final.inputPos = 2 ∧
      final.workTapePos 0 = 3 ∧ final.workTapes 0 0 = some true ∧
      final.workTapePos 1 = 0 ∧ final.workTapes 1 0 = some false ∧
      final.workTapes 1 2 = some false ∧ final.workTapes 1 3 = none ∧
      final.workTapePos 2 = 0 ∧ final.workTapes 2 (-1) = some true := by
  decide

/-- Empty output is still a valid input, with two distinct boundary positions. -/
example :
    let cfg : Cfg 0 Bool Bool [] := wordsCfg [] none Fin.elim0 []
    let machine := MultiTapeTM.prepareInput 0
    let final := machine.runFrom
      ((MultiTapeTM.PrepareInput.before cfg).withState (some machine.q₀)) 4
    final.state = none ∧ final.workTapePos 0 = 0 ∧ final.workTapes 0 0 = none ∧
      final.workTapePos 1 = 0 ∧ final.workTapes 1 (-1) = some true := by
  decide

noncomputable section

/-- A stateful oracle records the submitted query verbatim. -/
def recordingOracle (query : Word) : StateT (List Word) PMF Word :=
  fun transcript => PMF.pure ([true], transcript ++ [query])

/-- Stop after either one or two steps, leaving a correspondingly different pending query. -/
def randomStop : OracleTM 0 Bool :=
  Turing.OracleTM.mk (false) fun later _ _ _ coin => .step
    { inputTape := 0, workTapes := Fin.elim0, output := none,
      state := if later || coin then none else some true }
    (some (later || coin)) 0

/-- Submit the inherited buffer, then return the oracle's first answer bit. -/
def submit : OracleTM 0 Bool :=
  Turing.OracleTM.mk (false) fun write _ _ answer _ =>
    if write then .step
      { inputTape := 0, workTapes := Fin.elim0, output := some (answer.getD false),
        state := none } none 0
    else .query true

/-- Directly evaluate shared-tape sequencing across both stopping times. No query is repeated
when the first phase halts early, and the pending query is preserved until submission. -/
example : OracleComp.runState recordingOracle ((randomStop.seq submit).run 4 []) [] =
    (PMF.uniformOfFintype Bool).map
      (fun early => ([true], [if early then [true] else [false, true]])) := by
  simp only [OracleTM.run, OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk,
    Cfg.init,
    OracleTM.seq_initial, OracleTM.seq_transition, randomStop, Bool.false_or,
    OracleComp.uniform, OracleComp.runState_sample_bind, PMF.map]
  congr 1
  funext coin
  cases coin <;>
    simp [submit, recordingOracle,
      OracleTM.Config.step, OracleTM.Config.receive, OracleTM.Config.answerSymbol,
      Action.apply, PMF.map, Function.comp_def]

/-- Write an encoded parameter of zero or one, each with probability one half, in two steps. -/
def chooseParameterMachine : OracleTM 0 Bool :=
  Turing.OracleTM.mk (false) fun delimiter _ _ _ coin => .step
    { inputTape := 0
      workTapes := Fin.elim0
      output := if delimiter then some false else if coin then some true else none
      state := if delimiter then none else some true } none 0

def chooseArguments (_ : ℕ) (_ : Word) : ProbComp (ℕ × Word) := do
  let bit ← OracleComp.uniform Bool
  pure (if bit then 1 else 0, [])

theorem chooseArguments_isPPT : IsPPT parameterEncoding chooseArguments := by
  apply isPPT_of_finite_machine chooseParameterMachine 2 0
  intro n input
  simp only [chooseArguments, ProbComp.eval_bind, OracleComp.uniform, ProbComp.eval_sample,
    ProbComp.eval_pure, PMF.map_bind, PMF.pure_map, pow_zero, Nat.mul_one,
    OracleTM.run, OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk, Cfg.init,
    chooseParameterMachine, Bool.false_eq_true, ↓reduceIte, OracleComp.eval_bind,
    OracleComp.eval_sample]
  congr 1
  funext coin
  cases coin <;>
    simp [OracleTM.Config.step, Action.apply, parameterEncoding, parameterInput, PMF.map,
      Function.comp_def]

/-- The first program's sampled parameter determines the size of the second sample. -/
def adaptiveSample (n : ℕ) (input : Word) : ProbComp Word := do
  let (length, _) ← chooseArguments n input
  OracleComp.sampleBits length

theorem adaptiveSample_isPPT : IsPPT wordEncoding adaptiveSample :=
  chooseArguments_isPPT.bind_parameter isPPT_sampleBits

/-- This is an adaptive distribution: empty with probability one half, one fair bit otherwise. -/
example (n : ℕ) (input : Word) :
    ProbComp.eval (adaptiveSample n input) =
      (PMF.uniformOfFintype Bool).bind (fun bit => uniformBits (if bit then 1 else 0)) := by
  simp [adaptiveSample, chooseArguments, OracleComp.uniform, ProbComp.eval]

/-- A closed query writes its empty answer's default bit, contaminating only its own work tape. -/
def queryAndWrite : OracleTM 1 Bool :=
  Turing.OracleTM.mk (false) fun write _ _ answer _ =>
    if write then .step
      { inputTape := 1, workTapes := fun _ => (some (some true), 1),
        output := some (answer.getD false), state := none } none 0
    else .query true

/-- Read the buffered first bit only if both of the continuation's own work tapes are blank. -/
def inspectFresh : OracleTM 2 Unit :=
  Turing.OracleTM.mk (()) fun _ symbol work _ _ => .step
    { inputTape := 0, workTapes := fun _ => (none, 0),
      output := some (if (work 0).isNone && (work 1).isNone then symbol.getD true else true),
      state := none } none 0

theorem queryAndWrite_halts (input : Word) : queryAndWrite.HaltsWithin 2 input := by
  intro OracleState oracle s final s' hfinal
  simp only [OracleTM.runConfigFrom_zero, OracleTM.runConfigFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk,
    Cfg.init, queryAndWrite,
    Bool.false_eq_true, ↓reduceIte, OracleComp.uniform,
    OracleComp.runState_bind, OracleComp.runState_query, PMF.mem_support_bind_iff,
    OracleTM.Config.receive, OracleTM.Config.step, Action.apply, OracleComp.runState_pure,
    PMF.mem_support_pure_iff] at hfinal
  obtain ⟨coin, _, ⟨answer, state⟩, _, coin', _, heq⟩ := hfinal
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  exact hstate

theorem inspectFresh_halts (input : Word) : inspectFresh.HaltsWithin 1 input := by
  intro OracleState oracle s final s' hfinal
  simp only [OracleTM.runConfigFrom_zero, OracleTM.runConfigFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk,
    Cfg.init, inspectFresh,
    OracleComp.uniform, OracleComp.runState_sample_bind, PMF.mem_support_bind_iff,
    OracleTM.Config.step, Action.apply, OracleComp.runState_pure,
    PMF.mem_support_pure_iff] at hfinal
  obtain ⟨coin, _, heq⟩ := hfinal
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  exact hstate

/-- Different work-tape counts compose, the second input is the first output, and the external
oracle is never called. Reading the real input or a source work tape would return the wrong bit. -/
example : OracleComp.runState recordingOracle
    ((queryAndWrite.comp inspectFresh).run 9 [true, true]) [] = PMF.pure ([false], []) := by
  rw [show 9 = 2 + (2 + 4 + 1) by decide,
    OracleTM.runState_comp queryAndWrite inspectFresh [true, true] 2 1 recordingOracle []
      (queryAndWrite_halts _) (fun word _ => inspectFresh_halts word)]
  simp [OracleTM.run, OracleTM.runFrom_succ, OracleTM.initialConfig, OracleTM.initial_mk,
    OracleTM.transition_mk,
    queryAndWrite, inspectFresh,
    OracleTM.Config.step, OracleTM.Config.receive, OracleTM.Config.answerSymbol, Action.apply,
    OracleComp.uniform, PMF.map, Function.comp_def, Cfg.workTapeSymbols, Cfg.inputSymbol]

end

end CslibTests.ComputationalCryptoComposition
