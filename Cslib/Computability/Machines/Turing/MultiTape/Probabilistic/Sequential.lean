/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Sequential composition on shared machine tapes

The first machine's halting transition starts the second machine, retaining ordinary tapes and
all communication channels. Pathwise halting bounds add even when the stopping time depends on
coins or oracle responses. The composition law is an equality of free programs and therefore
preserves every stateful interpretation.

Preparing a fresh encoded input and clearing subroutine storage are separate, charged operations.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State₀ State₁ Oracle : Type} {input : List Bool}

/-- Transfer control on the first machine's halting transition, preserving all tapes. -/
def seq (first : MultiTapePTM k Bool State₀ Oracle) (second : MultiTapePTM k Bool State₁ Oracle) :
    MultiTapePTM k Bool (State₀ ⊕ State₁) Oracle where
  initial := .inl first.initial
  tr state symbol work answer bit := match state with
    | .inl state => match first.tr state symbol work answer bit with
      | .step action symbol move => .step
        { action with state := some (action.state.elim (.inr second.initial) .inl) } symbol move
      | .query oracle next => .query oracle (.inl next)
    | .inr state => match second.tr state symbol work answer bit with
      | .step action symbol move => .step { action with state := action.state.map .inr } symbol move
      | .query oracle next => .query oracle (.inr next)

namespace Sequential

/-- First-phase configurations map halting to the second machine's initial state. -/
def left (second : MultiTapePTM k Bool State₁ Oracle) (cfg : Config k Bool State₀ Oracle input) :
    Config k Bool (State₀ ⊕ State₁) Oracle input :=
  { cfg with
    tapes := cfg.tapes.mapState (fun state => some (state.elim (.inr second.initial) .inl)) }

/-- Second-phase configurations use right control states, including the shared halting state. -/
def right (cfg : Config k Bool State₁ Oracle input) :
    Config k Bool (State₀ ⊕ State₁) Oracle input :=
  { cfg with tapes := cfg.tapes.mapState (Option.map .inr) }

/-- Start the second machine with the data and channels left by the first. -/
def start (second : MultiTapePTM k Bool State₁ Oracle) (cfg : Config k Bool State₀ Oracle input) :
    Config k Bool State₁ Oracle input :=
  { cfg with tapes := cfg.tapes.withState (some second.initial) }

theorem left_halted (second : MultiTapePTM k Bool State₁ Oracle)
    (cfg : Config k Bool State₀ Oracle input) (h : cfg.tapes.state = none) :
    left second cfg = right (start second cfg) := by
  simp [left, start, right, Cfg.mapState, Cfg.withState, h]

@[simp] theorem left_state (second : MultiTapePTM k Bool State₁ Oracle)
    (cfg : Config k Bool State₀ Oracle input) :
    (left second cfg).tapes.state =
      some (cfg.tapes.state.elim (.inr second.initial) .inl) := rfl

@[simp] theorem right_state (cfg : Config k Bool State₁ Oracle input) :
    (right (State₀ := State₀) cfg).tapes.state = cfg.tapes.state.map .inr := rfl

@[simp] theorem left_inputSymbol (second : MultiTapePTM k Bool State₁ Oracle)
    (cfg : Config k Bool State₀ Oracle input) :
    (left second cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem left_workTapeSymbols (second : MultiTapePTM k Bool State₁ Oracle)
    (cfg : Config k Bool State₀ Oracle input) :
    (left second cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem left_answerSymbols (second : MultiTapePTM k Bool State₁ Oracle)
    (cfg : Config k Bool State₀ Oracle input) :
    (left second cfg).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem right_inputSymbol (cfg : Config k Bool State₁ Oracle input) :
    (right (State₀ := State₀) cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem right_workTapeSymbols (cfg : Config k Bool State₁ Oracle input) :
    (right (State₀ := State₀) cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem right_answerSymbols (cfg : Config k Bool State₁ Oracle input) :
    (right (State₀ := State₀) cfg).answerSymbols = cfg.answerSymbols := rfl

variable [DecidableEq Oracle]

/-- The first phase simulates the complete local transition, including oracle submission. -/
theorem step_left (first : MultiTapePTM k Bool State₀ Oracle)
    (second : MultiTapePTM k Bool State₁ Oracle) (cfg : Config k Bool State₀ Oracle input)
    (h : cfg.tapes.state ≠ none) :
    (first.seq second).step (left second cfg) = left second <$> first.step cfg := by
  cases hs : cfg.tapes.state with
  | none => exact (h hs).elim
  | some state =>
    simp only [step, left_state, hs, Option.elim_some, seq, map_bind,
      left_inputSymbol, left_workTapeSymbols, left_answerSymbols]
    apply bind_congr
    intro bit
    cases first.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [Config.step, Config.receive, Turing.Action.apply, left, Cfg.mapState]

/-- The second phase runs without changing its interactions or communication storage. -/
theorem step_right (first : MultiTapePTM k Bool State₀ Oracle)
    (second : MultiTapePTM k Bool State₁ Oracle) (cfg : Config k Bool State₁ Oracle input) :
    (first.seq second).step (right cfg) = right <$> second.step cfg := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, right_state, hs, Option.map_some, seq, map_bind,
      right_inputSymbol, right_workTapeSymbols, right_answerSymbols]
    apply bind_congr
    intro bit
    cases second.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [Config.step, Config.receive, Turing.Action.apply, right, Cfg.mapState]

theorem runConfigFrom_right (first : MultiTapePTM k Bool State₀ Oracle)
    (second : MultiTapePTM k Bool State₁ Oracle) (fuel : ℕ)
    (cfg : Config k Bool State₁ Oracle input) :
    (first.seq second).runConfigFrom fuel (right cfg) =
      right <$> second.runConfigFrom fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    simp only [runConfigFrom_succ, step_right, bind_map_left, map_bind]
    exact bind_congr ih

end Sequential

variable [DecidableEq Oracle]

/-- Halting bounds add under sequencing; equality includes every oracle interaction. -/
theorem runConfigFrom_seq (first : MultiTapePTM k Bool State₀ Oracle)
    (second : MultiTapePTM k Bool State₁ Oracle) (firstTime secondTime : ℕ)
    (cfg : Config k Bool State₀ Oracle input) (hfirst : first.HaltsWithin firstTime cfg)
    (hsecond : ∀ mid, MonadAttach.CanReturn (first.runConfigFrom firstTime cfg) mid →
      second.HaltsWithin secondTime (Sequential.start second mid)) :
    (first.seq second).runConfigFrom (firstTime + secondTime) (Sequential.left second cfg) = (do
      let mid ← first.runConfigFrom firstTime cfg
      Sequential.right <$> second.runConfigFrom secondTime (Sequential.start second mid)) := by
  induction firstTime generalizing cfg with
  | zero =>
    have hhalt := hfirst cfg rfl
    simp only [Nat.zero_add, runConfigFrom_zero, pure_bind]
    rw [Sequential.left_halted second cfg hhalt, Sequential.runConfigFrom_right]
  | succ firstTime ih =>
    by_cases hhalt : cfg.tapes.state = none
    · simp only [runConfigFrom_halted first _ cfg hhalt, pure_bind]
      rw [Sequential.left_halted second cfg hhalt, Sequential.runConfigFrom_right,
        Nat.add_comm (firstTime + 1) secondTime]
      exact congrArg (Functor.map Sequential.right)
        ((hsecond cfg (by simp [hhalt])).runConfigFrom_add (firstTime + 1))
    · rw [Nat.succ_add, runConfigFrom_succ, Sequential.step_left first second cfg hhalt,
        runConfigFrom_succ, bind_map_left, bind_assoc]
      apply FreeM.bind_congr_of_canReturn
      intro mid hmid
      apply ih
      · intro final hfinal
        exact hfirst final ((FreeM.canReturn_bind _ _ _).mpr ⟨mid, hmid, hfinal⟩)
      · intro final hfinal
        exact hsecond final ((FreeM.canReturn_bind _ _ _).mpr ⟨mid, hmid, hfinal⟩)

/-- The same sum of transition bounds halts on every path of the composed machine. -/
theorem HaltsWithin.seq {first : MultiTapePTM k Bool State₀ Oracle}
    {second : MultiTapePTM k Bool State₁ Oracle} {firstTime secondTime : ℕ}
    {cfg : Config k Bool State₀ Oracle input} (hfirst : first.HaltsWithin firstTime cfg)
    (hsecond : ∀ mid, MonadAttach.CanReturn (first.runConfigFrom firstTime cfg) mid →
      second.HaltsWithin secondTime (Sequential.start second mid)) :
    (first.seq second).HaltsWithin (firstTime + secondTime) (Sequential.left second cfg) := by
  intro final hfinal
  rw [runConfigFrom_seq first second firstTime secondTime cfg hfirst hsecond] at hfinal
  obtain ⟨mid, hmid, hfinal⟩ := (FreeM.canReturn_bind _ _ _).mp hfinal
  obtain ⟨result, hresult, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  simp [hsecond mid hmid result hresult]

end Turing.MultiTapePTM
