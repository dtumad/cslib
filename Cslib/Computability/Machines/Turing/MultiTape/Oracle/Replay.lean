/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Closed
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Deterministic replay of a closed probabilistic machine

`replay machine` reads the source's coins from a fresh last work tape. It uses the source's
ordinary tapes, handles empty-answer queries locally, and takes one transition per stored coin.
A halted source leaves its tapes unchanged while the controller finishes scanning the coins.
The first blank coin cell halts the controller, so a tape of `t` coins takes `t + 1` steps.

`runFrom_replay` proves exact agreement with the shared machine's fixed-coin semantics.
The coin tape is read-only. Initializing it and preparing any encoded input pair are separate
machine computations; this module does not give those preloaded tapes for free.
-/

@[expose] public section

namespace Turing.OracleTM
open Cslib
variable {k : ℕ} {State : Type} {input : List Bool}

namespace Replay

/-- The shared fixed-coin evaluator, viewed through the compact configuration interface. -/
def result (machine : OracleTM k State) (coins : List Bool) (cfg : Config k State input) :
    Config k State input :=
  Config.ofCore (MultiTapePTM.runConfigFromCoins (m := Id) machine (fun _ _ => []) coins cfg.toCore)

/-- An empty random tape takes no source transitions. -/
@[simp] theorem result_nil (machine : OracleTM k State) (cfg : Config k State input) :
    result machine [] cfg = cfg := rfl

/-- One stored coin supplies exactly the next source transition. -/
theorem result_cons (machine : OracleTM k State) (coin : Bool) (coins : List Bool)
    (cfg : Config k State input) :
    result machine (coin :: coins) cfg =
      match cfg.tapes.state with
      | none => cfg
      | some state =>
        match machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbol coin with
        | .step action bit move => result machine coins (cfg.step action bit move)
        | .query next => result machine coins (cfg.receive next []) := by
  cases hstate : cfg.tapes.state with
  | none =>
    simp [result, MultiTapePTM.runConfigFromCoins, hstate, Config.toCore, Config.ofCore]
    rfl
  | some state =>
    simp only [result, MultiTapePTM.runConfigFromCoins, Config.toCore_tapes, hstate,
      Config.toCore_answerSymbols, tr_eq]
    cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin with
    | step action bit move => rfl
    | query next => simp only [OracleAction.coreEquiv, Equiv.coe_fn_symm_mk,
        ← Config.toCore_receive]; rfl

/-- Add a read-only coin tape and retain the source's possibly halted state in the control. -/
def config (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (Option State) input where
  state := some cfg.tapes.state
  inputPos := cfg.tapes.inputPos
  workTapes := Fin.lastCases tape cfg.tapes.workTapes
  workTapePos := Fin.lastCases position cfg.tapes.workTapePos
  output := cfg.tapes.output

/-- Move only the coin head and update the controller. -/
def idle (next : Option (Option State)) (move : SignType) :
    Action (k + 1) Bool (Option State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, move) (fun _ => (none, 0))
  output := none
  state := next

/-- Simulate an ordinary source action while advancing the coin head. -/
def liftAction (action : Action k Bool State) : Action (k + 1) Bool (Option State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 1) action.workTapes
  output := action.output
  state := some action.state

/-- The controller's final configuration after scanning the complete coin tape. -/
def stopped (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (Option State) input :=
  (config cfg tape position).withState none

/-- A lifted action updates the source tapes and consumes one coin. -/
theorem apply_liftAction (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (liftAction action).apply (config cfg tape position) =
      config (cfg.step action bit move) tape (position + 1) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [config, liftAction, Config.step, Action.apply]

/-- An empty-answer query changes the source state and consumes one coin. -/
theorem apply_query (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ)
    (next : State) :
    (idle (some (some next)) 1).apply (config cfg tape position) =
      config (cfg.receive next []) tape (position + 1) := by
  refine Cfg.ext rfl (by simp [idle, config, Config.receive, Action.apply]) ?_ ?_
    (by simp [idle, config, Config.receive, Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [idle, config, Config.receive, Action.apply]

/-- A halted source stays fixed while the remaining coins are consumed. -/
theorem apply_tick (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    (idle (some cfg.tapes.state) 1).apply (config cfg tape position) =
      config cfg tape (position + 1) := by
  refine Cfg.ext rfl (by simp [idle, config, Action.apply]) ?_ ?_
    (by simp [idle, config, Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [idle, config, Action.apply]

/-- Halting preserves every tape and head position. -/
theorem apply_stop (cfg : Config k State input) (tape : ℤ → Option Bool) (position : ℤ) :
    (idle none 0).apply (config cfg tape position) = stopped cfg tape position := by
  refine Cfg.ext rfl (by simp [idle, config, stopped, Action.apply, Cfg.withState]) ?_ ?_
    (by simp [idle, config, stopped, Action.apply, Cfg.withState]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [idle, config, stopped, Action.apply, Cfg.withState]

/-- The controller sees the original input cell. -/
@[simp] theorem config_inputSymbol (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position).inputSymbol = cfg.tapes.inputSymbol := rfl

/-- The source work heads are preserved. -/
@[simp] theorem config_workTapeSymbols_castSucc (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (i : Fin k) :
    (config cfg tape position).workTapeSymbols i.castSucc = cfg.tapes.workTapeSymbols i := by
  simp [config, Cfg.workTapeSymbols]

/-- The last work head reads the next stored coin. -/
@[simp] theorem config_workTapeSymbols_last (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position).workTapeSymbols (Fin.last k) = tape position := by
  simp [config, Cfg.workTapeSymbols]

end Replay

/-- A deterministic machine replays a closed fair-coin machine from a supplied coin tape.
Its control is finite whenever the source control is finite. -/
def replay (machine : OracleTM k State) : MultiTapeTM (k + 1) Bool (Option State) where
  q₀ := some machine.initial
  tr state symbol work :=
    match work (Fin.last k) with
    | none => Replay.idle none 0
    | some coin =>
      match state with
      | none => Replay.idle (some none) 1
      | some state =>
        match machine.transition state symbol (fun i => work i.castSucc) none coin with
        | .step action _ _ => Replay.liftAction action
        | .query next => Replay.idle (some (some next)) 1

namespace Replay

/-- An available coin produces the same source transition as fixed-coin execution. -/
theorem step_some (machine : OracleTM k State) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (coin : Bool)
    (hcell : tape position = some coin) (hanswer : cfg.answer = []) :
    machine.replay.step (config cfg tape position) =
      match cfg.tapes.state with
      | none => config cfg tape (position + 1)
      | some state =>
        match machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbol coin with
        | .step action bit move => config (cfg.step action bit move) tape (position + 1)
        | .query next => config (cfg.receive next []) tape (position + 1) := by
  rw [MultiTapeTM.step_apply_of_state rfl]
  have hs : cfg.answerSymbol = none := Closed.answerSymbol_eq_none cfg hanswer
  simp only [replay, config_inputSymbol, config_workTapeSymbols_last, hcell,
    config_workTapeSymbols_castSucc, hs]
  cases hstate : cfg.tapes.state with
  | none => simp only [← hstate, apply_tick]
  | some state =>
    simp only
    cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols none coin with
    | step action bit move => exact apply_liftAction cfg tape position action bit move
    | query next => exact apply_query cfg tape position next

/-- The first blank coin cell halts the deterministic controller. -/
theorem step_none (machine : OracleTM k State) (cfg : Config k State input)
    (tape : ℤ → Option Bool) (position : ℤ) (hcell : tape position = none) :
    machine.replay.step (config cfg tape position) = stopped cfg tape position := by
  rw [MultiTapeTM.step_apply_of_state rfl]
  simpa only [replay, config_workTapeSymbols_last, hcell] using apply_stop cfg tape position


/-- Fixed-coin source execution ignores coins once halted. -/
theorem result_halted (machine : OracleTM k State) (coins : List Bool)
    (cfg : Config k State input) (h : cfg.tapes.state = none) :
    result machine coins cfg = cfg := by
  unfold result
  rw [MultiTapePTM.runConfigFromCoins_halted _ _ _ _ h]
  rfl

/-- Replay a given coin sequence from any location on the coin tape. The source may halt early;
the controller still reaches the end of the sequence in the stated time. -/
theorem runFrom_coins (machine : OracleTM k State) (cfg : Config k State input)
    (coins : List Bool) (tape : ℤ → Option Bool) (position : ℤ)
    (hcoins : ∀ i : ℕ, i < coins.length → tape (position + i) = coins[i]?)
    (hstop : tape (position + coins.length) = none) (hanswer : cfg.answer = []) :
    machine.replay.runFrom (config cfg tape position) (coins.length + 1) =
      stopped (result machine coins cfg) tape (position + coins.length) := by
  induction coins generalizing cfg position with
  | nil =>
    simpa [MultiTapeTM.runFrom_one] using step_none machine cfg tape position (by simpa using hstop)
  | cons coin coins ih =>
    have hcell : tape position = some coin := by simpa using hcoins 0 (by simp)
    have htail (i : ℕ) (hi : i < coins.length) :
        tape (position + 1 + i) = coins[i]? := by
      have h := hcoins (i + 1) (by simp; omega)
      simpa [Int.natCast_add, add_assoc, add_comm, add_left_comm] using h
    have hend : tape (position + 1 + coins.length) = none := by
      simpa [add_assoc, add_comm, add_left_comm] using hstop
    rw [List.length_cons, show coins.length + 1 + 1 = 1 + (coins.length + 1) by omega,
      MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one,
      step_some machine cfg tape position coin hcell hanswer, result_cons]
    cases hstate : cfg.tapes.state with
    | none =>
      simp only
      rw [ih cfg (position + 1) htail hend hanswer, result_halted machine coins cfg hstate]
      congr 1; omega
    | some state =>
      simp only
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | step action bit move =>
        rw [ih (cfg.step action bit move) (position + 1) htail hend hanswer]
        congr 1; omega
      | query next =>
        rw [ih (cfg.receive next []) (position + 1) htail hend rfl]
        congr 1; omega

end Replay

/-- From a correctly initialized coin tape, deterministic replay matches the original source
and has halted after the supplied number of coins plus one transitions. -/
theorem runFrom_replay (machine : OracleTM k State) (coins input : List Bool) :
    machine.replay.runFrom
        (Replay.config (machine.initialConfig input) (tapeOfList coins) 0) (coins.length + 1) =
      Replay.stopped (Replay.result machine coins (machine.initialConfig input))
        (tapeOfList coins) coins.length := by
  simpa using Replay.runFrom_coins machine (machine.initialConfig input) coins
    (tapeOfList coins) 0 (by intros; simp) (by simp) rfl

end Turing.OracleTM
