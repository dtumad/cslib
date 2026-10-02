/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Computational.OneWay
import Cslib.Crypto.Computational.PseudorandomGenerator
import Cslib.Crypto.Computational.PseudorandomFunction
import Cslib.Crypto.Computational.Hybrid
import Cslib.Computability.Probabilistic.Output

/-!
# Computational cryptography examples

These examples exercise actual PPT certificates, adaptive and stateful oracles, and security-game
semantics. In particular, the repeated-query test distinguishes a fixed random function from an
oracle which resamples on every call.
-/

namespace CslibTests.ComputationalCrypto

open Cslib Cslib.Probability Cslib.Crypto

noncomputable section

/-- A machine writes its fresh random bit and halts. -/
def coinMachine : Turing.OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ _ _ _ coin => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := none } none 0

example : IsPPT boolEncoding (fun _ _ => OracleComp.uniform Bool) := by
  refine ⟨0, 1, coinMachine, 1, 0, ?_⟩
  intro pair
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    coinMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    boolEncoding, PMF.map, Function.comp_def]

/-- Query the empty word, then copy the first answer bit (or false for an empty answer). -/
def firstAnswerMachine : Turing.OracleTM 0 (Fin 2) :=
  Turing.OracleTM.mk (0) fun state _ _ answer _ =>
    if state = 0 then .query 1
    else .step
      { inputTape := 0, workTapes := Fin.elim0, output := some (answer.getD false), state := none }
      none 0

/-- A high-level oracle program with a concrete two-transition realization. The certificate
quantifies over all stateful oracles and preserves the final oracle state. -/
example : IsOraclePPT boolEncoding
    (fun _ _ => do return (← OracleComp.query []).headD false) := by
  refine ⟨0, 2, firstAnswerMachine, 2, 0, ?_⟩
  intro n x State oracle s
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine, Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    boolEncoding, PMF.map, Function.comp_def, List.headD_eq_head?_getD, List.head?_eq_getElem?]

/-- The second query is the answer to the first. -/
def adaptive (input : Word) : OracleComp Word (fun _ => Word) Word := do
  let answer ← OracleComp.query input
  OracleComp.query answer

example (f : Word → Word) (input : Word) :
    OracleComp.eval (fun query => PMF.pure (f query)) (adaptive input) =
      PMF.pure (f (f input)) := by
  simp [adaptive]

/-- A private Boolean state alternates the returned bit. -/
def alternatingOracle (_ : Word) : StateT Bool PMF Word :=
  fun state => PMF.pure ([state], !state)

/-- This machine never halts: only its external clock stops the coin stream. -/
def streamingCoinMachine : Turing.OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ _ _ _ coin => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := some 0 } none 0

/-- Unequal codeword lengths, including erasure, are allowed. -/
def unevenCode (bit : Bool) : Word := if bit then [true, false] else []

/-- After exactly two source steps, exactly one true coin has probability one half.
The expanded machine flushes the complete codeword even though the source never halts. -/
example : OracleComp.eval (fun _ => PMF.pure [])
    ((streamingCoinMachine.expandOutput unevenCode).run 8 []) [true, false] = 1 / 2 := by
  change OracleComp.eval (fun _ => PMF.pure [])
    ((streamingCoinMachine.expandOutput unevenCode).run
      ((Turing.OracleTM.OutputExpansion.width unevenCode + 2) * 2) []) _ = _
  rw [Turing.OracleTM.eval_run_expandOutput]
  norm_num [Turing.OracleTM.run, Turing.OracleTM.runFrom_zero, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    streamingCoinMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    unevenCode, PMF.map, Function.comp_def, PMF.bind_apply, PMF.uniformOfFintype_apply,
    tsum_fintype]
  rw [← add_mul, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

/-- Erasing the output still performs the query and preserves its effect on private state. -/
example : OracleComp.runState alternatingOracle
    ((firstAnswerMachine.expandOutput (fun _ => [])).run 4 []) false =
      PMF.pure ([], true) := by
  change OracleComp.runState alternatingOracle
    ((firstAnswerMachine.expandOutput (fun _ => [])).run
      ((Turing.OracleTM.OutputExpansion.width (fun _ => []) + 2) * 2) []) false = _
  rw [Turing.OracleTM.runState_run_expandOutput]
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine, Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    alternatingOracle, PMF.map, Function.comp_def]

/-- A bit emitted on the halting transition is expanded completely. -/
example : OracleComp.eval (fun _ => PMF.pure [])
    (((returnBitMachine true).expandOutput unevenCode).run 4 []) =
      PMF.pure [true, false] := by
  change OracleComp.eval (fun _ => PMF.pure [])
    (((returnBitMachine true).expandOutput unevenCode).run
      ((Turing.OracleTM.OutputExpansion.width unevenCode + 2) * 1) []) = _
  rw [Turing.OracleTM.eval_run_expandOutput]
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    returnBitMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    unevenCode, PMF.map, Function.comp_def]

/-- Pause just after the query, then resume with the saved answer and oracle state. -/
example :
    OracleComp.runState alternatingOracle
      (do
        let cfg ← firstAnswerMachine.runConfigFrom 1 (firstAnswerMachine.initialConfig [])
        firstAnswerMachine.runFrom 1 cfg) false = PMF.pure ([false], true) := by
  rw [← Turing.OracleTM.runFrom_add]
  simp [Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine,
    Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    alternatingOracle, PMF.map, Function.comp_def]

example :
    OracleComp.runState alternatingOracle
      (do
        let first ← OracleComp.query []
        let second ← OracleComp.query []
        return first != second) false = PMF.pure (true, false) := by
  simp [alternatingOracle, PMF.pure_map]
  rfl

/-- Query the same valid input twice and check equality of the responses. -/
def repeatQuery : OracleDistinguisher := fun n _ => do
  let input := List.replicate n false
  let first ← OracleComp.query input
  let second ← OracleComp.query input
  return first == second

example (family : Word → Word → Word) (n : ℕ) :
    ProbComp.eval (prfRealGame family repeatQuery n) = PMF.pure true := by
  simp [prfRealGame, repeatQuery, ProbComp.eval, PMF.map,
    Function.comp_def]

example (n : ℕ) : ProbComp.eval (prfIdealGame repeatQuery n) = PMF.pure true := by
  simp [prfIdealGame, repeatQuery, ProbComp.eval, OracleComp.uniform,
    PMF.map, Function.comp_def]

/-- Fresh independent answers pass the repeated-query test with probability one half. -/
example :
    OracleComp.eval (fun _ : Word => (PMF.uniformOfFintype Bool).map (fun bit => [bit]))
      (repeatQuery 1 []) true = 1 / 2 := by
  norm_num [repeatQuery, PMF.map, Function.comp_def, PMF.bind_apply,
    PMF.uniformOfFintype_apply, tsum_fintype]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

example (word : Word) : ¬ OneWay (fun _ => word) := not_oneWay_const word

/-- A different preimage is accepted, even when it has a different length from the sampled input. -/
example (n : ℕ) :
    ProbComp.eval (inversionGame (fun _ => [true]) (fun _ _ => pure []) n) = PMF.pure true :=
  eval_inversionGame_of_rightInverse _ (fun _ => []) (fun _ => rfl) n

example (X Y Z : ℕ → PMF Word) (hXY : ComputationallyIndistinguishable X Y)
    (hYZ : ComputationallyIndistinguishable Y Z) : ComputationallyIndistinguishable X Z :=
  hXY.trans hYZ

/-- A negligible bound for each fixed hop is insufficient for a growing hybrid sequence. -/
def isolatedAdvantage (i n : ℕ) : ℝ := if n = i then 1 else 0

example (i : ℕ) : Negligible (isolatedAdvantage i) := by
  apply negligible_zero.congr'
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  simp [isolatedAdvantage, Nat.ne_of_gt hn]

example : ¬ Negligible (fun n => isolatedAdvantage n n) := by
  simpa [isolatedAdvantage] using (not_negligible_const (c := 1) one_ne_zero)

end

end CslibTests.ComputationalCrypto
