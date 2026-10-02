/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Halting
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# Reserving scratch tapes for oracle-machine compilers

Reindexing the source tapes leaves all additional tapes and heads unchanged. The construction
reuses the deterministic model's tape embedding and preserves the complete oracle program.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k k' : ℕ} {State : Type} {input : List Bool}

/-- Reindex a local action, leaving every extra tape untouched. -/
def extendAction (action : Action k Bool State) (e : Fin k ↪ Fin k') : Action k' Bool State where
  inputTape := action.inputTape
  workTapes := fun i => match MultiTapeTM.partialInv e i with
    | some j => action.workTapes j
    | none => (none, 0)
  output := action.output
  state := action.state

/-- Run on the tapes selected by `e`, preserving all other tapes and every oracle interaction. -/
@[simps! initial] def extendTapes (machine :
    OracleTM k State) (e : Fin k ↪ Fin k') :
    OracleTM k' State :=
  Turing.OracleTM.mk (machine.initial) fun state symbol work answer coin =>
    match machine.transition state symbol (fun i => work (e i)) answer coin with
    | .step action bit move => .step (extendAction action e) bit move
    | .query next => .query next

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem extendTapes_transition (machine : OracleTM k State) (e : Fin k ↪ Fin k') :
    (extendTapes machine e).transition =
  fun state symbol work answer coin =>
    match machine.transition state symbol (fun i => work (e i)) answer coin with
    | .step action bit move => .step (extendAction action e) bit move
    | .query next => .query next := by
  funext state symbol work answer coin
  simp only [extendTapes, Turing.OracleTM.transition_mk]

/-- A source configuration together with arbitrary contents and head positions on extra tapes. -/
def Config.embed (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) : Config k' State input :=
  { cfg with tapes := MultiTapeTM.embed e cfg.tapes extraTapes extraPos }

@[simp] theorem Config.embed_state (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.state = cfg.tapes.state := rfl

@[simp] theorem Config.embed_inputSymbol (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem Config.embed_workTapeSymbols (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) (i : Fin k) :
    (cfg.embed e extraTapes extraPos).tapes.workTapeSymbols (e i) =
      cfg.tapes.workTapeSymbols i := by
  exact MultiTapeTM.embed_workTapeSymbols_embed e cfg.tapes extraTapes extraPos i

@[simp] theorem Config.embed_answerSymbol (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem Config.embed_queryBuffer (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem Config.embed_output (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) :
    (cfg.embed e extraTapes extraPos).tapes.output = cfg.tapes.output := rfl

theorem Config.step_embed (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (cfg.embed e extraTapes extraPos).step (extendAction action e) bit move =
      (cfg.step action bit move).embed e extraTapes extraPos := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [Config.step, Config.embed, extendAction, Action.apply, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> simp

theorem Config.receive_embed (cfg : Config k State input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Bool) (extraPos : Fin k' → ℤ) (next : State)
    (answer : List Bool) :
    (cfg.embed e extraTapes extraPos).receive next answer =
      (cfg.receive next answer).embed e extraTapes extraPos := rfl

/-- Reindexing preserves the entire clocked program, retaining all scratch-tape contents. -/
theorem runConfigFrom_embed (machine : OracleTM k State) (e : Fin k ↪ Fin k')
    (cfg : Config k State input) (extraTapes : Fin k' → ℤ → Option Bool)
    (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runConfigFrom fuel (cfg.embed e extraTapes extraPos) =
      (fun final => final.embed e extraTapes extraPos) <$> machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, Config.embed_state, hs, Config.embed_inputSymbol,
        Config.embed_workTapeSymbols, Config.embed_answerSymbol, extendTapes_transition, map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin <;> simp [Config.step_embed, Config.receive_embed, ih, map_bind]

/-- The additional work tapes are invisible in the source's output program. -/
theorem runFrom_embed (machine : OracleTM k State) (e : Fin k ↪ Fin k')
    (cfg : Config k State input) (extraTapes : Fin k' → ℤ → Option Bool)
    (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runFrom fuel (cfg.embed e extraTapes extraPos) =
      machine.runFrom fuel cfg := by
  rw [runFrom_eq_map_runConfigFrom, runConfigFrom_embed, ← comp_map]
  exact (runFrom_eq_map_runConfigFrom machine fuel cfg).symm

/-- Reserving extra tapes starts them blank, with every work head at zero. -/
theorem initialConfig_extendTapes (machine : OracleTM k State) (e : Fin k ↪ Fin k')
    (input : List Bool) :
    (machine.extendTapes e).initialConfig input =
      (machine.initialConfig input).embed e (fun _ _ => none) (fun _ => 0) := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    simp only [initialConfig, Cfg.init, Config.embed, MultiTapeTM.embed] <;>
    cases MultiTapeTM.partialInv e i <;> rfl

/-- Reserving blank scratch tapes does not change the machine's observable program. -/
@[simp] theorem run_extendTapes (machine : OracleTM k State) (e : Fin k ↪ Fin k')
    (fuel : ℕ) (input : List Bool) :
    (machine.extendTapes e).run fuel input = machine.run fuel input := by
  rw [run, initialConfig_extendTapes, runFrom_embed]
  rfl

/-- Reserving additional tapes preserves a uniform halting bound. -/
theorem HaltsWithin.extendTapes {machine : OracleTM k State} {fuel : ℕ} {input : List Bool}
    (h : machine.HaltsWithin fuel input) (e : Fin k ↪ Fin k') :
    (machine.extendTapes e).HaltsWithin fuel input := by
  intro OracleState oracle s final s' hfinal
  rw [initialConfig_extendTapes, runConfigFrom_embed, OracleComp.runState_map] at hfinal
  obtain ⟨⟨cfg, state⟩, hcfg, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact (congrArg (fun result => result.1.tapes.state) heq).symm.trans
    (h OracleState oracle s cfg state hcfg)

end Turing.OracleTM
