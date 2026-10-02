/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Deterministic preparation before an oracle computation

`machine.prepend preparation` runs a deterministic tape routine, then transfers control to the
oracle machine. The preparation makes no queries. The continuation retains its complete oracle
interaction, and the handoff theorem accounts for the preparation's actual halting time.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {Preparation State OracleState : Type} {input : List Bool}

/-- Execute deterministic preparation, then an oracle machine on the resulting tapes. -/
@[simps! initial] def prepend (machine : OracleTM k State)
    (preparation : MultiTapeTM k Bool Preparation) : OracleTM k (Preparation ⊕ State) :=
  Turing.OracleTM.mk (.inl preparation.q₀) fun state symbol work answer coin =>
    match state with
    | .inl state =>
      let action := preparation.tr state symbol work
      .step { action with state := some (action.state.elim (.inr machine.initial) .inl) } none 0
    | .inr state =>
      match machine.transition state symbol work answer coin with
      | .step action bit move => .step { action with state := action.state.map .inr } bit move
      | .query next => .query (.inr next)

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem prepend_transition (machine : OracleTM k State)
    (preparation : MultiTapeTM k Bool Preparation) :
    (prepend machine preparation).transition =
  fun state symbol work answer coin =>
    match state with
    | .inl state =>
      let action := preparation.tr state symbol work
      .step { action with state := some (action.state.elim (.inr machine.initial) .inl) } none 0
    | .inr state =>
      match machine.transition state symbol work answer coin with
      | .step action bit move => .step { action with state := action.state.map .inr } bit move
      | .query next => .query (.inr next) := by
  funext state symbol work answer coin
  simp only [prepend, Turing.OracleTM.transition_mk]

namespace Prepend

/-- Preparation uses the left states; its halt dispatches to the continuation. -/
def left (machine : OracleTM k State) (cfg : Cfg k Bool Preparation input) :
    Config k (Preparation ⊕ State) input where
  tapes := cfg.mapState (fun state => some (state.elim (.inr machine.initial) .inl))

/-- Embed a running or halted continuation, retaining its communication tapes. -/
def right (cfg : Config k State input) : Config k (Preparation ⊕ State) input :=
  { cfg with tapes := cfg.tapes.mapState (Option.map .inr) }

@[simp] theorem left_state (machine : OracleTM k State) (cfg : Cfg k Bool Preparation input) :
    (left machine cfg).tapes.state = some (cfg.state.elim (.inr machine.initial) .inl) := rfl

@[simp] theorem left_inputSymbol (machine : OracleTM k State)
    (cfg : Cfg k Bool Preparation input) :
    (left machine cfg).tapes.inputSymbol = cfg.inputSymbol := rfl

@[simp] theorem left_workTapeSymbols (machine : OracleTM k State)
    (cfg : Cfg k Bool Preparation input) :
    (left machine cfg).tapes.workTapeSymbols = cfg.workTapeSymbols := rfl

@[simp] theorem right_state (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).tapes.state = cfg.tapes.state.map .inr := rfl

@[simp] theorem right_inputSymbol (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem right_workTapeSymbols (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).tapes.workTapeSymbols =
      cfg.tapes.workTapeSymbols := rfl

@[simp] theorem right_answerSymbol (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem right_queryBuffer (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem right_output (cfg : Config k State input) :
    (right (Preparation := Preparation) cfg).tapes.output = cfg.tapes.output := rfl

theorem step_right (cfg : Config k State input) (action : Action k Bool State)
    (bit : Option Bool) (move : SignType) :
    (right (Preparation := Preparation) cfg).step
        { action with state := action.state.map .inr } bit move =
      right (cfg.step action bit move) := rfl

theorem receive_right (cfg : Config k State input) (next : State) (answer : List Bool) :
    (right (Preparation := Preparation) cfg).receive (.inr next) answer =
      right (cfg.receive next answer) := rfl

/-- Once preparation is finished, the continuation executes its original program. -/
theorem runConfigFrom_right (machine : OracleTM k State)
    (preparation : MultiTapeTM k Bool Preparation) (fuel : ℕ) (cfg : Config k State input) :
    (machine.prepend preparation).runConfigFrom fuel (right cfg) =
      right <$> machine.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, right_state, hs, Option.map_some, right_inputSymbol,
        right_workTapeSymbols, right_answerSymbol, prepend_transition, map_bind]
      congr 1
      funext coin
      cases machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | step action bit move => simp [step_right, ih]
      | query next => simp [receive_right, ih, map_bind]

/-- During preparation the only sampled bits are ignored, and the oracle state is untouched. -/
theorem runState_left (machine : OracleTM k State)
    (preparation : MultiTapeTM k Bool Preparation)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Cfg k Bool Preparation input) (s : OracleState)
    (hlive : ∀ time < fuel, (preparation.runFrom cfg time).state ≠ none) :
    OracleComp.runState oracle
      ((machine.prepend preparation).runConfigFrom fuel (left machine cfg)) s =
      PMF.pure (left machine (preparation.runFrom cfg fuel), s) := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp (hlive 0 (by omega))
    have hstate : cfg.state = some state := hs
    have hstep : (left machine cfg).step
        { preparation.tr state cfg.inputSymbol cfg.workTapeSymbols with
          state := some ((preparation.tr state cfg.inputSymbol cfg.workTapeSymbols).state.elim
            (.inr machine.initial) .inl) } none 0 = left machine (preparation.step cfg) := by
      rw [MultiTapeTM.step_apply_of_state hstate]
      simp [left, Config.step, Action.apply, Cfg.mapState]
    have htail : ∀ time < fuel, (preparation.runFrom (preparation.step cfg) time).state ≠ none := by
      intro time htime
      simpa only [MultiTapeTM.runFrom, Function.iterate_succ_apply] using
        hlive (time + 1) (by omega)
    conv_lhs => rw [runConfigFrom_succ]
    simp only [left_state, hstate, Option.elim_some, left_inputSymbol, left_workTapeSymbols,
      prepend_transition]
    change OracleComp.runState oracle
      (OracleComp.uniform Bool >>= fun _ =>
        (machine.prepend preparation).runConfigFrom fuel _) s = _
    rw [hstep]
    simp only [OracleComp.uniform, OracleComp.runState_sample_bind, ih _ htail, PMF.bind_const]
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply]

end Prepend

/-- At the first halting time of preparation, transfer to the oracle continuation without
introducing any oracle calls or losing its private state. -/
theorem runState_runConfigFrom_prepend (machine : OracleTM k State)
    (preparation : MultiTapeTM k Bool Preparation)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (cfg : Cfg k Bool Preparation input) (time fuel : ℕ) (s : OracleState)
    (hlive : ∀ t < time, (preparation.runFrom cfg t).state ≠ none)
    (hhalt : (preparation.runFrom cfg time).state = none) :
    OracleComp.runState oracle
      ((machine.prepend preparation).runConfigFrom (time + fuel) (Prepend.left machine cfg)) s =
      (OracleComp.runState oracle
        (machine.runConfigFrom fuel
          { tapes := (preparation.runFrom cfg time).withState (some machine.initial) }) s).map
        (fun (final, s') => (Prepend.right final, s')) := by
  have hhandoff : Prepend.left machine (preparation.runFrom cfg time) =
      Prepend.right (Preparation := Preparation)
        { tapes := (preparation.runFrom cfg time).withState (some machine.initial) } := by
    simp [Prepend.left, Prepend.right, Cfg.mapState, Cfg.withState, hhalt]
  rw [runConfigFrom_add, OracleComp.runState_bind,
    Prepend.runState_left machine preparation oracle time cfg s hlive, PMF.pure_bind]
  simp only [hhandoff, Prepend.runConfigFrom_right, OracleComp.runState_map]

end Turing.OracleTM
