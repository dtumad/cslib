/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Computability.PolynomialTime.Defs
public import Init.Data.List.Monadic

/-!
# A uniform machine for sampling binary words

One fixed state and no work tapes suffice to sample one bit for each symbol of the unary
parameter. The delimiter takes a final transition, whose coin is discarded. The structural
execution theorem retains that coin, so it holds independently of any probability semantics.
There are no oracle calls and the communication channels remain unchanged.

Adapted from Samuel Schlesinger's sampling machine.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine MultiTapeTM PFunctor

variable {Oracle : Type}

/-- Scan the unary parameter, emitting one coin per `true`, and halt at the delimiter. -/
def uniformBitsMachine : MultiTapePTM 0 Bool (Fin 1) Oracle where
  initial := 0
  tr _ symbol _ _ bit := .step
    { inputTape := if symbol = some true then 1 else 0
      workTapes := Fin.elim0
      output := if symbol = some true then some bit else none
      state := if symbol = some true then some 0 else none }
    (fun _ => none) (fun _ => 0)

namespace UniformBitsMachine

/-- The configuration after scanning `index` parameter symbols. -/
def config (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    Config 0 Bool (Fin 1) Oracle (parameterInput n input) where
  tapes :=
    { state := some 0
      inputPos := ⟨index + 1, by simp only [length_parameterInput]; omega⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := output }

@[simp] theorem config_state (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    (config (Oracle := Oracle) n input output index h).tapes.state = some 0 := rfl

/-- Halt at the parameter delimiter with the completed output. -/
def finalConfig (n : ℕ) (input output : Word) :
    Config 0 Bool (Fin 1) Oracle (parameterInput n input) :=
  { config n input output n le_rfl with tapes.state := none }

theorem inputSymbol (n : ℕ) (input output : Word) (index : ℕ) (h : index ≤ n) :
    (config (Oracle := Oracle) n input output index h).tapes.inputSymbol =
      if index < n then some true else some false := by
  rw [inputSymbolInner index (by simp [config, Nat.add_comm])
    (by simp only [length_parameterInput]; omega)]
  by_cases hi : index < n
  · simp [parameterInput, hi]
  · have : index = n := by omega
    subst index
    simp [parameterInput]

theorem step (n : ℕ) (input output : Word) (index : ℕ) (h : index < n) (bit : Bool) :
    (config (Oracle := Oracle) n input output index (by omega)).step
      { inputTape := 1, workTapes := Fin.elim0, output := some bit, state := some 0 }
      (fun _ => none) (fun _ => 0) =
      config n input (output ++ [bit]) (index + 1) h := by
  apply Config.ext
  · refine Cfg.ext_zero_tapes rfl ?_ rfl
    apply Fin.ext
    change (moveInputPos (config n input output index (by omega)).tapes.inputPos .pos).val =
      index + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp [config]; omega)]
    rfl
  · funext oracle
    simp [Config.step, config]

theorem step_final (n : ℕ) (input output : Word) :
    (config (Oracle := Oracle) n input output n le_rfl).step
      { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
      (fun _ => none) (fun _ => 0) = finalConfig n input output := by
  apply Config.ext
  · refine Cfg.ext_zero_tapes rfl ?_ ?_
    · simp [Config.step, Action.apply, finalConfig]
    · simp [Config.step, Action.apply, finalConfig]
  · funext oracle
    simp [Config.step, config, finalConfig]

variable [DecidableEq Oracle]

/-- The full reached configuration, including the final unused coin and all oracle channels. -/
theorem runConfigFrom_config (n : ℕ) (input : Word) (remaining : ℕ) :
    ∀ (index : ℕ) (output : Word) (h : index + remaining = n),
      uniformBitsMachine.runConfigFrom (remaining + 1)
        (config (Oracle := Oracle) n input output index (by omega)) = (do
          let tail ← (List.replicate remaining ()).mapM (fun _ => coin)
          let _ ← coin
          pure (finalConfig n input (output ++ tail))) := by
  induction remaining with
  | zero =>
    intro index output h
    have : index = n := by omega
    subst index
    simp [runConfigFrom, MultiTapePTM.step, uniformBitsMachine, inputSymbol, step_final]
  | succ remaining ih =>
    intro index output h
    have hi : index < n := by omega
    have hnext : index + 1 + remaining = n := by omega
    rw [runConfigFrom_succ]
    simp only [MultiTapePTM.step, show (config (Oracle := Oracle) n input output index
      (by omega)).tapes.state = some 0 from rfl, uniformBitsMachine,
      inputSymbol, ite_eq_left hi, ↓reduceIte, pure_bind, bind_assoc,
      List.replicate_succ, List.mapM_cons]
    apply bind_congr
    intro bit
    rw [step n input output index hi bit]
    simpa only [uniformBitsMachine, List.append_assoc, List.singleton_append] using
      ih (index + 1) (output ++ [bit]) hnext

omit [DecidableEq Oracle] in
theorem initialConfig (n : ℕ) (input : Word) :
    (uniformBitsMachine (Oracle := Oracle)).initialConfig (parameterInput n input) =
      config n input [] 0 (Nat.zero_le n) := by
  apply Config.ext
  · refine Cfg.ext_zero_tapes rfl ?_ rfl
    apply Fin.ext
    simp [MultiTapeMachine.initialConfig, Cfg.init, config]
  · rfl

end UniformBitsMachine

variable [DecidableEq Oracle]

/-- The sampler halts in `n + 1` transitions for every coin path. -/
theorem haltsWithin_uniformBitsMachine (n : ℕ) (input : Word) :
    uniformBitsMachine.HaltsWithin (n + 1)
      ((uniformBitsMachine (Oracle := Oracle)).initialConfig (parameterInput n input)) := by
  intro final h
  rw [UniformBitsMachine.initialConfig,
    UniformBitsMachine.runConfigFrom_config n input n 0 [] (by omega)] at h
  obtain ⟨tail, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  obtain ⟨_, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  have heq : final = UniformBitsMachine.finalConfig n input ([] ++ tail) := h
  rw [heq]
  rfl

/-- Structural output law; interpreting the final unused coin removes it. -/
theorem run_uniformBitsMachine (n : ℕ) (input : Word) :
    (uniformBitsMachine (Oracle := Oracle)).run (n + 1) (parameterInput n input) = (do
      let word ← (List.replicate n ()).mapM (fun _ => coin)
      let _ ← coin
      pure (some word)) := by
  rw [run, runFrom, UniformBitsMachine.initialConfig,
    UniformBitsMachine.runConfigFrom_config n input n 0 [] (by omega)]
  simp [map_bind, output?, UniformBitsMachine.finalConfig, UniformBitsMachine.config]

end Turing.MultiTapePTM
