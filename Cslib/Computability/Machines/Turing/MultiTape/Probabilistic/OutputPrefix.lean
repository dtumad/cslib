/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Simulation

/-!
# Retaining an already written output prefix

Output is write-only, so a prefix leaves all subsequent execution and oracle interaction unchanged.
Writing that prefix is separate, charged machine work. Timeout remains distinct from every word.
-/

@[expose] public section

namespace Turing.MultiTapePTM
open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} {input : List Bool}

namespace OutputPrefix

/-- Change only the already written output, inserting a fixed prefix. -/
def config (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    Config k Bool State Oracle input := { cfg with tapes := cfg.tapes.prependOutput pre }

@[simp] theorem config_state (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).tapes.state = cfg.tapes.state := rfl
@[simp] theorem config_inputSymbol (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl
@[simp] theorem config_workTapeSymbols (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl
@[simp] theorem config_answerSymbols (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).answerSymbols = cfg.answerSymbols := rfl
@[simp] theorem config_channels (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).channels = cfg.channels := rfl
@[simp] theorem config_output (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    (config cfg pre).tapes.output = pre ++ cfg.tapes.output := rfl

theorem step_config (cfg : Config k Bool State Oracle input) (pre : List Bool)
    (action : Turing.Action k Bool State) (symbol : Oracle → Option Bool)
    (move : Oracle → SignType) :
    (config cfg pre).step action symbol move = config (cfg.step action symbol move) pre := by
  simp only [config, Config.step, Turing.Action.apply_prependOutput]

theorem receive_config [DecidableEq Oracle] (cfg : Config k Bool State Oracle input)
    (pre : List Bool) (oracle : Oracle) (next : State) (answer : List Bool) :
    (config cfg pre).receive oracle next answer = config (cfg.receive oracle next answer) pre := rfl

@[simp] theorem output?_config (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    output? (config cfg pre) = (output? cfg).map (pre ++ ·) := by
  simp [output?, apply_ite]

end OutputPrefix

variable [DecidableEq Oracle]
/-- Prepending unreadable output preserves every coin and oracle interaction. -/
theorem runConfigFrom_prefixOutput (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    machine.runConfigFrom fuel (OutputPrefix.config cfg pre) =
      (fun final => OutputPrefix.config final pre) <$> machine.runConfigFrom fuel cfg := by
  refine runConfigFrom_simulation machine machine
    (fun cfg => OutputPrefix.config cfg pre) ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, OutputPrefix.config_state, hs, OutputPrefix.config_inputSymbol,
      OutputPrefix.config_workTapeSymbols, OutputPrefix.config_answerSymbols, map_bind]
    apply bind_congr
    intro bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [OutputPrefix.step_config, OutputPrefix.receive_config]

/-- A completed output retains the prefix; exhaustion remains `none`. -/
theorem runFrom_prefixOutput (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) (pre : List Bool) :
    machine.runFrom fuel (OutputPrefix.config cfg pre) =
      (fun result => result.map (pre ++ ·)) <$> machine.runFrom fuel cfg := by
  simp only [runFrom, runConfigFrom_prefixOutput, ← comp_map]
  congr 1
  funext final
  exact OutputPrefix.output?_config final pre

/-- A fixed output prefix leaves the pathwise termination bound unchanged. -/
theorem HaltsWithin.prefixOutput {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg) (pre : List Bool) :
    machine.HaltsWithin fuel (OutputPrefix.config cfg pre) := by
  intro final hfinal
  rw [runConfigFrom_prefixOutput] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  exact h original horiginal

end Turing.MultiTapePTM
