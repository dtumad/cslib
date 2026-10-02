/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Probabilistic.Clock

/-!
# Internal clock checks

The deterministic constructor and complete tape preparation are evaluated from blank tapes.
The oracle controller and complete compiler are checked on nonhalting sources, zero budgets,
and cutoff immediately after a stateful oracle query.
-/

namespace CslibTests.ComputationalCryptoClock

open Cslib Cslib.Probability Turing

set_option maxRecDepth 4096 in

/-- Evaluate the nested loop constructor itself, independently of its correctness theorem. -/
example :
    let machine := MultiTapeTM.polynomialClock 3 2
    let final := machine.runFrom (machine.initCfg [true, false]) 86
    final.output = List.replicate 27 true ∧ final.state = none ∧ final.inputPos = 1 ∧
      ∀ i, final.workTapePos i = 0 ∧ final.workTapeSymbols i = some true := by
  decide

/-- Empty input still gives base one, so a positive monomial retains its coefficient. -/
example :
    let machine := MultiTapeTM.polynomialClock 2 2
    let final := machine.runFrom (machine.initCfg []) 15
    final.output = [true, true] ∧ final.state = none := by
  decide

/-- Degree zero and coefficient zero need no hidden positive-input assumption. -/
example :
    let machine := MultiTapeTM.polynomialClock 0 0
    let final := machine.runFrom (machine.initCfg []) 3
    final.output = [] ∧ final.state = none := by
  decide

set_option maxRecDepth 4096 in

/-- Evaluate routing, output redirection and rewind, independently of their correctness proofs. -/
example :
    let machine := MultiTapeTM.PolynomialClock.prepare 1 2 1
    let final := machine.runFrom (machine.initCfg [false]) 86
    final.state = none ∧ final.output = [] ∧ final.inputPos = 1 ∧
      (∀ i, final.workTapePos i = 0) ∧ final.workTapeSymbols 0 = none ∧
      final.workTapes 1 1 = some true ∧ final.workTapes 1 2 = none ∧
      final.workTapes 2 3 = some true ∧ final.workTapes 2 4 = none := by
  decide

/-- Rewinding an empty word preserves data and restores its head. -/
example :
    let machine := MultiTapeTM.rewindLast 0
    let final := machine.runFrom (machine.initCfg []) 2
    final.state = none ∧ final.workTapePos 0 = 0 ∧ final.output = [] := by
  decide

/-- The generated budget has a uniform PPT certificate with the specified monomial output size. -/
example (coefficient degree : ℕ) : IsPPT wordEncoding
    (fun n input =>
      pure (List.replicate (coefficient * (n + input.length + 2) ^ degree) true)) := by
  let generator := MultiTapeTM.polynomialClock coefficient degree
  apply isPPT_of_finite_machine (OracleTM.ofDeterministic generator)
    (6 ^ degree * (coefficient + 1) + 2) (degree + 1)
  intro n input
  rw [OracleTM.run, OracleTM.eval_ofDeterministic]
  change (PMF.pure _).map wordEncoding = PMF.pure
    (generator.runFrom (Cfg.init generator.q₀ (parameterInput n input)) _).output
  rw [Cfg.init_eq_wordsCfg, MultiTapeTM.runFrom_polynomialClock_bound]
  simp [wordEncoding, PMF.pure_map, wordsCfg, Nat.add_assoc]

noncomputable section

/-- A private oracle records the exact sequence of queries. -/
def recordingOracle (query : Word) : StateT (List Word) PMF Word :=
  fun transcript => PMF.pure ([true], transcript ++ [query])

/-- The first step queries; the second writes its answer and halts. -/
def queryThenWrite : OracleTM 0 Bool :=
  Turing.OracleTM.mk (false) fun state _ _ answer _ =>
    if state then .step
      { inputTape := 0, workTapes := Fin.elim0, output := some (answer.getD false),
        state := none } none 0
    else .query true

/-- This source has no halting transition. -/
def writeForever : OracleTM 0 Unit :=
  Turing.OracleTM.mk (()) fun _ _ _ _ _ => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some true, state := some () } none 0

/-- The internal budget stops an otherwise infinite source after the requested number of bits. -/
example : OracleComp.runState recordingOracle
    (writeForever.withClock.runFrom 10
      (OracleTM.Clock.config (writeForever.initialConfig [])
        (tapeOfList (List.replicate 3 true)) 0 false)) [] =
      PMF.pure ([true, true, true], []) := by
  rw [show 10 = 2 * 3 + 1 + 3 by decide,
    OracleTM.runState_runFrom_withClock writeForever recordingOracle _ _ _ 3 3 []
      (by
        intro i hi
        simp only [zero_add, tapeOfList_ofNat, List.getElem?_replicate, ite_eq_left hi])
      (by decide)]
  simp [OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk, writeForever,
    OracleTM.Config.step,
    Action.apply, OracleComp.uniform, PMF.map, Function.comp_def]

/-- An empty budget prevents even the first oracle query. -/
example : OracleComp.runState recordingOracle
    (queryThenWrite.withClock.runFrom 9
      (OracleTM.Clock.config (queryThenWrite.initialConfig []) (tapeOfList []) 0 false)) [] =
      PMF.pure ([], []) := by
  simpa [OracleTM.initialConfig] using OracleTM.runState_runFrom_withClock
    queryThenWrite recordingOracle
    (queryThenWrite.initialConfig []) (tapeOfList []) 0 0 8 [] (by simp) (by simp)

/-- Cutoff immediately after the query keeps the oracle effect but prevents the next output step.
Giving the compiled machine extra time cannot resume that discarded source computation. -/
example : OracleComp.runState recordingOracle
    (queryThenWrite.withClock.runFrom 13
      (OracleTM.Clock.config (queryThenWrite.initialConfig []) (tapeOfList [true]) 0 false)) [] =
      PMF.pure ([], [[]]) := by
  rw [show 13 = 2 * 1 + 1 + 10 by decide,
    OracleTM.runState_runFrom_withClock queryThenWrite recordingOracle _ _ _ 1 10 []
      (by
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        rfl)
      (by decide)]
  simp [OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk, queryThenWrite,
    recordingOracle,
    OracleTM.Config.receive, OracleComp.uniform, PMF.map, Function.comp_def]

/-- Padding after the source halts never repeats its query or emits another answer. -/
example : OracleComp.runState recordingOracle
    (queryThenWrite.withClock.runFrom 18
      (OracleTM.Clock.config (queryThenWrite.initialConfig [])
        (tapeOfList (List.replicate 5 true)) 0 false)) [] = PMF.pure ([true], [[]]) := by
  rw [show 18 = 2 * 5 + 1 + 7 by decide,
    OracleTM.runState_runFrom_withClock queryThenWrite recordingOracle _ _ _ 5 7 []
      (by
        intro i hi
        simp only [zero_add, tapeOfList_ofNat, List.getElem?_replicate, ite_eq_left hi])
      (by decide)]
  simp [OracleTM.runFrom_succ, OracleTM.initialConfig, OracleTM.initial_mk,
    OracleTM.transition_mk, queryThenWrite,
    recordingOracle,
    OracleTM.Config.receive, OracleTM.Config.step, OracleTM.Config.answerSymbol,
    Action.apply, OracleComp.uniform, PMF.map, Function.comp_def]

/-- The complete compiler constructs its own constant budget and stops a nonhalting source. -/
example : OracleComp.runState recordingOracle
    ((writeForever.withPolynomialClock 3 0).run 50 []) [] =
      PMF.pure ([true, true, true], []) := by
  rw [OracleTM.runState_withPolynomialClock writeForever 3 0 [] recordingOracle 50 [] (by decide)]
  simp [OracleTM.run, OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk,
    writeForever, OracleTM.Config.step,
    Action.apply, OracleComp.uniform, PMF.map, Function.comp_def]

/-- A zero compiled budget makes no queries, even with positive degree and substantial padding. -/
example : OracleComp.runState recordingOracle
    ((queryThenWrite.withPolynomialClock 0 2).run 100 []) [] = PMF.pure ([], []) := by
  rw [OracleTM.runState_withPolynomialClock queryThenWrite 0 2 [] recordingOracle 100 []
    (by decide)]
  simp [OracleTM.run, OracleTM.initialConfig]

/-- Initialization and padding preserve the exact transcript at a query cutoff. -/
example : OracleComp.runState recordingOracle
    ((queryThenWrite.withPolynomialClock 1 1).run 50 []) [] = PMF.pure ([], [[]]) := by
  rw [OracleTM.runState_withPolynomialClock queryThenWrite 1 1 [] recordingOracle 50 [] (by decide)]
  simp [OracleTM.run, OracleTM.runFrom_zero, OracleTM.runFrom_succ, OracleTM.initialConfig,
    OracleTM.initial_mk, OracleTM.transition_mk,
    queryThenWrite, recordingOracle,
    OracleTM.Config.receive, OracleComp.uniform, PMF.map, Function.comp_def]

/-- Actual halting is checked separately from agreement of output distributions. -/
example : (writeForever.withPolynomialClock 3 0).HaltsWithin 50 [] :=
  writeForever.withPolynomialClock_haltsWithin 3 0 [] 50 (by decide)

end

end CslibTests.ComputationalCryptoClock
