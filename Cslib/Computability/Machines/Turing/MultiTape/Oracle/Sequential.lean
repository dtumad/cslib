/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Prepend
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Halting

/-!
# Sequencing probabilistic oracle machines

The first machine's halting transition transfers control to the second. Every tape, including
the oracle communication tapes, is retained. The composition theorem allows the first machine's
stopping time to depend on random choices and oracle answers: two halting bounds add.

This is sequencing on shared tapes. Supplying a fresh encoded input and clean communication state
to the continuation is a separate obligation of the higher-level composition compiler.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State₀ State₁ OracleState : Type} {input : List Bool}

/-- Transfer control to the second machine when the first halts, retaining all tapes. -/
@[simps! initial] def seq (first : OracleTM k State₀) (second : OracleTM k State₁) :
    OracleTM k (State₀ ⊕ State₁) :=
  Turing.OracleTM.mk (.inl first.initial) fun state symbol work answer coin =>
    match state with
    | .inl state =>
      match first.transition state symbol work answer coin with
      | .step action bit move => .step
        { action with state := some (action.state.elim (.inr second.initial) .inl) } bit move
      | .query next => .query (.inl next)
    | .inr state =>
      match second.transition state symbol work answer coin with
      | .step action bit move => .step { action with state := action.state.map .inr } bit move
      | .query next => .query (.inr next)

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem seq_transition (first : OracleTM k State₀) (second : OracleTM k State₁) :
    (seq first second).transition =
  fun state symbol work answer coin =>
    match state with
    | .inl state =>
      match first.transition state symbol work answer coin with
      | .step action bit move => .step
        { action with state := some (action.state.elim (.inr second.initial) .inl) } bit move
      | .query next => .query (.inl next)
    | .inr state =>
      match second.transition state symbol work answer coin with
      | .step action bit move => .step { action with state := action.state.map .inr } bit move
      | .query next => .query (.inr next) := by
  funext state symbol work answer coin
  simp only [seq, Turing.OracleTM.transition_mk]

namespace Sequential

/-- Run the first phase in left states, dispatching its halt to the second initial state. -/
def left (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    Config k (State₀ ⊕ State₁) input :=
  { cfg with
    tapes := cfg.tapes.mapState (fun state => some (state.elim (.inr second.initial) .inl)) }

/-- Start the continuation on the tapes and communication state left by the first machine. -/
def start (second : OracleTM k State₁) (cfg : Config k State₀ input) : Config k State₁ input :=
  { cfg with tapes := cfg.tapes.withState (some second.initial) }

@[simp] theorem left_state (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    (left second cfg).tapes.state =
      some (cfg.tapes.state.elim (.inr second.initial) .inl) := rfl

@[simp] theorem left_inputSymbol (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    (left second cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem left_workTapeSymbols (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    (left second cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem left_answerSymbol (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    (left second cfg).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem left_queryBuffer (second : OracleTM k State₁) (cfg : Config k State₀ input) :
    (left second cfg).queryBuffer = cfg.queryBuffer := rfl

theorem step_left (second : OracleTM k State₁) (cfg : Config k State₀ input)
    (action : Action k Bool State₀) (bit : Option Bool) (move : SignType) :
    (left second cfg).step
        { action with state := some (action.state.elim (.inr second.initial) .inl) } bit move =
      left second (cfg.step action bit move) := rfl

theorem receive_left (second : OracleTM k State₁) (cfg : Config k State₀ input)
    (next : State₀) (answer : List Bool) :
    (left second cfg).receive (.inl next) answer = left second (cfg.receive next answer) := rfl

theorem left_halted (second : OracleTM k State₁) (cfg : Config k State₀ input)
    (h : cfg.tapes.state = none) :
    left second cfg = Prepend.right (start second cfg) := by
  simp [left, start, Prepend.right, Cfg.mapState, Cfg.withState, h]

/-- While the first machine is active, one step mirrors its complete oracle program. -/
theorem runConfigFrom_one (first : OracleTM k State₀) (second : OracleTM k State₁)
    (cfg : Config k State₀ input) (h : cfg.tapes.state ≠ none) :
    (first.seq second).runConfigFrom 1 (left second cfg) =
      left second <$> first.runConfigFrom 1 cfg := by
  cases hs : cfg.tapes.state with
  | none => exact (h hs).elim
  | some state =>
    simp only [runConfigFrom_zero, runConfigFrom_succ, left_state, hs, Option.elim_some,
      left_inputSymbol,
      left_workTapeSymbols, left_answerSymbol, seq_transition, map_bind]
    congr 1
    funext coin
    cases first.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin with
    | step action bit move => simp [step_left]
    | query next => simp [receive_left]

/-- After handoff, the continuation runs its unchanged program in right states. -/
theorem runConfigFrom_right (first : OracleTM k State₀) (second : OracleTM k State₁)
    (fuel : ℕ) (cfg : Config k State₁ input) :
    (first.seq second).runConfigFrom fuel (Prepend.right cfg) =
      Prepend.right <$> second.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [hs]
    | some state =>
      simp only [runConfigFrom_succ, Prepend.right_state, hs, Option.map_some,
        Prepend.right_inputSymbol, Prepend.right_workTapeSymbols, Prepend.right_answerSymbol,
        seq_transition, map_bind]
      congr 1
      funext coin
      cases second.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbol coin with
      | step action bit move => simp [Prepend.step_right, ih]
      | query next => simp [Prepend.receive_right, ih, map_bind]

end Sequential

/-- Sequential halting bounds add, even when the first stopping time depends on random choices.
The distribution retains the final machine configuration and the oracle's private state. -/
theorem runState_runConfigFrom_seq (first : OracleTM k State₀) (second : OracleTM k State₁)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (cfg : Config k State₀ input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : ∀ result ∈ (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).support,
      result.1.tapes.state = none)
    (hsecond :
      ∀ result ∈ (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).support,
      ∀ final ∈ (OracleComp.runState oracle
        (second.runConfigFrom secondTime (Sequential.start second result.1)) result.2).support,
        final.1.tapes.state = none) :
    OracleComp.runState oracle
      ((first.seq second).runConfigFrom (firstTime + secondTime) (Sequential.left second cfg)) s =
      (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).bind
        (fun result => (OracleComp.runState oracle
          (second.runConfigFrom secondTime (Sequential.start second result.1)) result.2).map
          (fun (final, s') => (Prepend.right final, s'))) := by
  induction firstTime generalizing cfg s with
  | zero =>
    have hhalt := hfirst (cfg, s) (by simp)
    simp only [Nat.zero_add, runConfigFrom_zero, OracleComp.runState_pure, PMF.pure_bind]
    rw [Sequential.left_halted second cfg hhalt, Sequential.runConfigFrom_right,
      OracleComp.runState_map]
  | succ firstTime ih =>
    by_cases hhalt : cfg.tapes.state = none
    · have hsecond' := hsecond (cfg, s) (by simp [hhalt])
      simp only [runConfigFrom_halted first _ cfg hhalt, OracleComp.runState_pure, PMF.pure_bind]
      rw [Sequential.left_halted second cfg hhalt, Sequential.runConfigFrom_right,
        OracleComp.runState_map, Nat.add_comm (firstTime + 1) secondTime,
        runState_runConfigFrom_add_of_halted second oracle _ secondTime (firstTime + 1) s hsecond']
    · have hsplit : firstTime + 1 = 1 + firstTime := by omega
      have hstep : firstTime + 1 + secondTime = 1 + (firstTime + secondTime) := by omega
      rw [hstep, runConfigFrom_add, Sequential.runConfigFrom_one first second cfg hhalt,
        OracleComp.runState_bind, OracleComp.runState_map, PMF.bind_map]
      rw [hsplit, runConfigFrom_add, OracleComp.runState_bind, PMF.bind_bind]
      apply Probability.PMF.bind_congr_on_support
      rintro ⟨next, s'⟩ hnext
      dsimp only [Function.comp_def]
      apply ih
      · intro final hfinal
        apply hfirst final
        rw [hsplit, runConfigFrom_add, OracleComp.runState_bind]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hfinal⟩
      · intro final hfinal
        apply hsecond final
        rw [hsplit, runConfigFrom_add, OracleComp.runState_bind]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hfinal⟩

/-- A deterministic preparation phase hands its exact restored configuration to the continuation. -/
theorem runState_runConfigFrom_seq_pure (first : OracleTM k State₀) (second : OracleTM k State₁)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (cfg ready : Config k State₀ input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s =
      PMF.pure (ready, s))
    (hready : ready.tapes.state = none)
    (hsecond : ∀ final ∈ (OracleComp.runState oracle
      (second.runConfigFrom secondTime (Sequential.start second ready)) s).support,
      final.1.tapes.state = none) :
    OracleComp.runState oracle
      ((first.seq second).runConfigFrom (firstTime + secondTime) (Sequential.left second cfg)) s =
      (OracleComp.runState oracle
        (second.runConfigFrom secondTime (Sequential.start second ready)) s).map
        (fun (final, s') => (Prepend.right final, s')) := by
  rw [runState_runConfigFrom_seq first second oracle cfg firstTime secondTime s
    (by simpa [hfirst] using hready) (by simpa [hfirst] using hsecond), hfirst, PMF.pure_bind]

/-- Observing only the result gives the usual monadic sequencing law under the same bounds. -/
theorem runState_runFrom_seq (first : OracleTM k State₀) (second : OracleTM k State₁)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (cfg : Config k State₀ input) (firstTime secondTime : ℕ) (s : OracleState)
    (hfirst : ∀ result ∈ (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).support,
      result.1.tapes.state = none)
    (hsecond :
      ∀ result ∈ (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).support,
      ∀ final ∈ (OracleComp.runState oracle
        (second.runConfigFrom secondTime (Sequential.start second result.1)) result.2).support,
        final.1.tapes.state = none) :
    OracleComp.runState oracle
      ((first.seq second).runFrom (firstTime + secondTime) (Sequential.left second cfg)) s =
      (OracleComp.runState oracle (first.runConfigFrom firstTime cfg) s).bind
        (fun result => OracleComp.runState oracle
          (second.runFrom secondTime (Sequential.start second result.1)) result.2) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_seq first second oracle cfg firstTime secondTime s hfirst hsecond)
  simpa [runFrom_eq_map_runConfigFrom, OracleComp.runState_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def] using h

end Turing.OracleTM
