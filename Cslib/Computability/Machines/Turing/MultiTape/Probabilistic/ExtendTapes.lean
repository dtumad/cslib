/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Simulation
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# Reserving scratch tapes for oracle-machine compilers

Reindexing the source tapes leaves all additional tapes and heads unchanged. The construction
reuses the deterministic model's tape embedding and preserves the complete oracle program.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k k' : ℕ} {State Oracle : Type} {input : List Bool}

/-- Reindex a local action, leaving every extra tape untouched. -/
def extendAction (action : Turing.Action k Bool State) (e : Fin k ↪ Fin k') :
    Turing.Action k' Bool State where
  inputTape := action.inputTape
  workTapes := fun i => match MultiTapeTM.partialInv e i with
    | some j => action.workTapes j
    | none => (none, 0)
  output := action.output
  state := action.state

/-- Run on the tapes selected by `e`, preserving all other tapes and every oracle interaction. -/
@[simps! initial] def extendTapes (machine :
    MultiTapePTM k Bool State Oracle) (e : Fin k ↪ Fin k') :
    MultiTapePTM k' Bool State Oracle :=
  { initial := machine.initial
    tr := fun state symbol work answer coin =>
    match machine.tr state symbol (fun i => work (e i)) answer coin with
    | .step action bit move => .step (extendAction action e) bit move
    | .query oracle next => .query oracle next }

/-- A source configuration together with arbitrary contents and head positions on extra tapes. -/
def ExtendTapes.config (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    Config k' Bool State Oracle input :=
  { cfg with tapes := MultiTapeTM.embed e cfg.tapes extraTapes extraPos }

@[simp] theorem ExtendTapes.config_state (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (ExtendTapes.config cfg e extraTapes extraPos).tapes.state = cfg.tapes.state := rfl

@[simp] theorem ExtendTapes.config_inputSymbol (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (ExtendTapes.config cfg e extraTapes extraPos).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem ExtendTapes.config_workTapeSymbols (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ)
    (i : Fin k) :
    (ExtendTapes.config cfg e extraTapes extraPos).tapes.workTapeSymbols (e i) =
      cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.embed_workTapeSymbols_embed e cfg.tapes extraTapes extraPos i

@[simp] theorem ExtendTapes.config_answerSymbols (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (ExtendTapes.config cfg e extraTapes extraPos).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem ExtendTapes.config_channels (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (ExtendTapes.config cfg e extraTapes extraPos).channels = cfg.channels := rfl

@[simp] theorem ExtendTapes.config_output (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (ExtendTapes.config cfg e extraTapes extraPos).tapes.output = cfg.tapes.output := rfl

theorem ExtendTapes.step_config (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ)
    (action : Turing.Action k Bool State) (bit : Oracle → Option Bool) (move : Oracle → SignType) :
    (ExtendTapes.config cfg e extraTapes extraPos).step (extendAction action e) bit move =
      ExtendTapes.config (cfg.step action bit move) e extraTapes extraPos := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [Config.step, ExtendTapes.config, extendAction, Action.apply, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> simp

variable [DecidableEq Oracle]

theorem ExtendTapes.receive_config (cfg : Config k Bool State Oracle input)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ)
    (oracle : Oracle) (next : State)
    (answer : List Bool) :
    (ExtendTapes.config cfg e extraTapes extraPos).receive oracle next answer =
      ExtendTapes.config (cfg.receive oracle next answer) e extraTapes extraPos := rfl

/-- Reindexing preserves the entire clocked program, retaining all scratch-tape contents. -/
theorem runConfigFrom_embed (machine : MultiTapePTM k Bool State Oracle) (e : Fin k ↪ Fin k')
    (cfg : Config k Bool State Oracle input) (extraTapes : Fin k' → ℤ → Option Bool)
    (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runConfigFrom fuel (ExtendTapes.config cfg e extraTapes extraPos) =
      (fun final => ExtendTapes.config final e extraTapes extraPos) <$>
        machine.runConfigFrom fuel cfg := by
  refine runConfigFrom_simulation machine (machine.extendTapes e)
    (fun cfg => ExtendTapes.config cfg e extraTapes extraPos) ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, ExtendTapes.config_state, hs, ExtendTapes.config_inputSymbol,
      ExtendTapes.config_workTapeSymbols, ExtendTapes.config_answerSymbols, extendTapes, map_bind]
    apply bind_congr
    intro bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [ExtendTapes.step_config, ExtendTapes.receive_config]

/-- The additional work tapes are invisible in the source's output program. -/
theorem runFrom_embed (machine : MultiTapePTM k Bool State Oracle) (e : Fin k ↪ Fin k')
    (cfg : Config k Bool State Oracle input) (extraTapes : Fin k' → ℤ → Option Bool)
    (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runFrom fuel (ExtendTapes.config cfg e extraTapes extraPos) =
      machine.runFrom fuel cfg := by
  simp only [runFrom, runConfigFrom_embed, ← comp_map]
  rfl

omit [DecidableEq Oracle] in
/-- Reserving extra tapes starts them blank, with every work head at zero. -/
theorem initialConfig_extendTapes (machine : MultiTapePTM k Bool State Oracle) (e : Fin k ↪ Fin k')
    (input : List Bool) :
    (machine.extendTapes e).initialConfig input =
      ExtendTapes.config (machine.initialConfig input) e (fun _ _ => none) (fun _ => 0) := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [initialConfig, Cfg.init, ExtendTapes.config, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> rfl

/-- Reserving blank scratch tapes does not change the machine's observable program. -/
@[simp] theorem run_extendTapes (machine : MultiTapePTM k Bool State Oracle) (e : Fin k ↪ Fin k')
    (fuel : ℕ) (input : List Bool) :
    (machine.extendTapes e).run fuel input = machine.run fuel input := by
  rw [run, initialConfig_extendTapes, runFrom_embed]
  rfl

/-- Reserving additional tapes preserves every pathwise halting bound. -/
theorem HaltsWithin.extendTapes {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Bool)
    (extraPos : Fin k' → ℤ) :
    (machine.extendTapes e).HaltsWithin fuel (ExtendTapes.config cfg e extraTapes extraPos) := by
  intro final hfinal
  rw [runConfigFrom_embed] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  exact h original horiginal

end Turing.MultiTapePTM
