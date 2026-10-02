/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Composition
public import Cslib.Languages.Probabilistic.BitString

/-!
# Uniform binary sampling is PPT

A single one-state machine scans the unary security parameter, writing a fresh fair bit for every
`true` and halting at the delimiter. It uses `n + 1` transitions and no work tapes. The proof holds
for every stateful oracle and leaves its state unchanged.

Typed sampling rules reuse this machine after an efficiently computed unary length. They support
runtime-dependent sample sizes and a uniform Boolean draw through the public composition API.
-/

@[expose] public section

namespace Cslib.Probability

open Turing

/-- A fixed machine samples one bit per unary parameter symbol and halts at the delimiter. -/
@[simps! initial] def uniformBitsMachine : OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ symbol _ _ coin => .step
    { inputTape := if symbol = some true then 1 else 0
      workTapes := Fin.elim0
      output := if symbol = some true then some coin else none
      state := if symbol = some true then some 0 else none } none 0

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem uniformBitsMachine_transition :
    (uniformBitsMachine).transition =
  fun _ symbol _ _ coin => .step
    { inputTape := if symbol = some true then 1 else 0
      workTapes := Fin.elim0
      output := if symbol = some true then some coin else none
      state := if symbol = some true then some 0 else none } none 0 := by
  funext state symbol work answer coin
  simp only [uniformBitsMachine, Turing.OracleTM.transition_mk]

namespace UniformBitsMachine

/-- After `index` bits, the input head points to the next unary symbol or the delimiter. -/
def config (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    OracleTM.Config 0 (Fin 1) (parameterInput n input) where
  tapes :=
    { state := some 0
      inputPos := ⟨index + 1, by simp only [length_parameterInput]; omega⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := output }

@[simp] theorem config_state (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    (config n input output index h).tapes.state = some 0 := rfl

theorem inputSymbol (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    (config n input output index h).tapes.inputSymbol =
      if index < n then some true else some false := by
  rw [inputSymbolInner index (by simp [config, Nat.add_comm])
    (by simp only [length_parameterInput]; omega)]
  by_cases hi : index < n
  · simp [parameterInput, hi]
  · have : index = n := by omega
    subst index
    simp [parameterInput]

theorem step (n : ℕ) (input output : Word) (index : ℕ) (h : index < n) (coin : Bool) :
    (config n input output index (by omega)).step
      { inputTape := 1, workTapes := Fin.elim0, output := some coin, state := some 0 } none 0 =
      config n input (output ++ [coin]) (index + 1) h := by
  refine OracleTM.Config.ext ?_ rfl rfl (by simp [OracleTM.Config.step, config])
  refine Cfg.ext_zero_tapes ?_ ?_ ?_
  · rfl
  · apply Fin.ext
    change (moveInputPos (config n input output index (by omega)).tapes.inputPos .pos).val =
      index + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp [config]; omega)]
    rfl
  · rfl

/-- The remaining unary symbols produce independent fair bits, regardless of the oracle. -/
theorem runState_config {State : Type} (oracle : Word → StateT State PMF Word)
    (n : ℕ) (input : Word) (remaining : ℕ) (s : State) :
    ∀ (index fuel : ℕ) (output : Word) (h : index + remaining = n), remaining < fuel →
      OracleComp.runState oracle
        (uniformBitsMachine.runFrom fuel (config n input output index (by omega))) s =
        (uniformBits remaining).map (fun tail => (output ++ tail, s)) := by
  induction remaining with
  | zero =>
    intro index fuel output h hf
    have : index = n := by omega
    subst index
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [OracleTM.runFrom_succ, config_state,
        uniformBitsMachine_transition, inputSymbol,
        lt_self_iff_false, ↓reduceIte]
      simp [OracleComp.uniform, OracleTM.Config.step, config, Action.apply, PMF.map,
        Function.comp_def]
  | succ remaining ih =>
    intro index fuel output h hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hi : index < n := by omega
      simp only [OracleTM.runFrom_succ, config_state,
        uniformBitsMachine_transition, inputSymbol,
        ite_eq_left hi, ↓reduceIte, step n input output index hi, OracleComp.uniform,
        OracleComp.runState_sample_bind]
      have hnext : index + 1 + remaining = n := by omega
      simp only [ih (index + 1) fuel _ hnext (by omega), uniformBits_succ, PMF.map_bind,
        PMF.map_comp, Function.comp_def, List.append_assoc, List.singleton_append]

end UniformBitsMachine

/-- The sampler writes exactly `n` uniformly distributed bits and leaves the oracle untouched. -/
theorem runState_uniformBitsMachine {State : Type} (oracle : Word → StateT State PMF Word)
    (n : ℕ) (input : Word) (fuel : ℕ) (hf : n < fuel) (s : State) :
    OracleComp.runState oracle (uniformBitsMachine.run fuel (parameterInput n input)) s =
      (uniformBits n).map (fun word => (word, s)) := by
  have hcfg : uniformBitsMachine.initialConfig (parameterInput n input) =
      UniformBitsMachine.config n input [] 0 (Nat.zero_le n) := by
    refine OracleTM.Config.ext ?_ rfl rfl rfl
    refine Cfg.ext_zero_tapes rfl ?_ rfl
    apply Fin.ext
    simp [OracleTM.initialConfig, Cfg.init, UniformBitsMachine.config]
  rw [OracleTM.run, hcfg]
  simpa using UniformBitsMachine.runState_config oracle n input n s 0 fuel [] (by omega) hf

/-- Uniform sampling has a single finite-control oracle PPT implementation for all lengths. -/
theorem isOraclePPT_sampleBits :
    IsOraclePPT wordEncoding (fun n _ => OracleComp.sampleBits n) := by
  refine ⟨0, 1, uniformBitsMachine, 1, 1, ?_⟩
  intro n input State oracle s
  change OracleComp.runState oracle (id <$> OracleComp.sampleBits n) s = _
  rw [id_map, OracleComp.runState_sampleBits, runState_uniformBitsMachine]
  simp only [pow_one, one_mul, length_parameterInput]
  omega

/-- Sampling a uniform binary string is PPT under the fair-coin machine definition. -/
theorem isPPT_sampleBits : IsPPT wordEncoding (fun n _ => OracleComp.sampleBits n) := by
  refine ⟨0, 1, uniformBitsMachine, 1, 1, ?_⟩
  rintro ⟨n, input⟩
  have h := congrArg (PMF.map Prod.fst) (runState_uniformBitsMachine
    (fun _ (s : Unit) => (PMF.pure ([] : Word)).map (fun a => (a, s))) n input
      (1 * ((parameterInput n input).length + 1) ^ 1) (by simp; lia) ())
  rw [OracleComp.runState_stateless] at h
  simpa [ProbComp.eval, OracleComp.eval_sampleBits, wordEncoding, parameterEncoding, PMF.map,
    Function.comp_def] using h.symm

/-- An abstract uniform sample has the same PPT realization as the fair-bit program. -/
theorem isPPT_uniformBits :
    IsPPT wordEncoding (fun n _ => OracleComp.sample (uniformBits n)) :=
  isPPT_sampleBits.congr (fun _ _ => by simp [ProbComp.eval])

/-- Sample an efficiently computed number of fair bits, charging the numerical length in unary. -/
theorem IsPolyTime.sampleBits {α : Type} {input : α → Word} {count : α → ℕ}
    (hcount : IsPolyTime input (fun a => List.replicate (count a) true)) :
    IsPPTOn input wordEncoding (fun a => OracleComp.sampleBits (count a)) :=
  isPPT_sampleBits.on.preprocess (prepare := fun a => (count a, []))
    (hcount.parameterInput (isPolyTime_const input []))

/-- An explicit uniform word sample has the same certificate as its fair-bit implementation. -/
theorem IsPolyTime.uniformBits {α : Type} {input : α → Word} {count : α → ℕ}
    (hcount : IsPolyTime input (fun a => List.replicate (count a) true)) :
    IsPPTOn input wordEncoding (fun a => OracleComp.sample (uniformBits (count a))) :=
  hcount.sampleBits.congr (fun _ => by simp [ProbComp.eval])

/-- One fair coin is available at any input encoding. -/
theorem isPPTOn_uniformBool {α : Type} (input : α → Word) :
    IsPPTOn input boolEncoding (fun _ => OracleComp.uniform Bool) := by
  have hbits := (isPolyTime_const input [true]).sampleBits (count := fun _ => 1)
  have hbit := hbits.map (output := boolEncoding) (f := fun word => word.headD false)
    (isPolyTime_headD wordEncoding false)
  apply hbit.congr
  intro a
  simp [ProbComp.eval, OracleComp.eval_sampleBits, uniformBits_succ, PMF.map_bind,
    OracleComp.uniform, PMF.pure_map]

end Cslib.Probability
