/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Init.Control.Option

/-!
# Recording and replaying prefixes through ordinary handlers

A replay handler consumes recorded answers until the prefix is exhausted, then forwards the
remaining operations. Both mismatched requests and unused recorded suffixes are rejected.
The handler carries data only; it does not store or decode a program continuation.
-/

@[expose] public section

namespace PFunctor.FreeM

section Handlers

universe u

variable {P : PFunctor.{u, u}} {α : Type u}

/-- Forward a request and append its answer to the recorded execution. -/
def traceHandler (op : P.A) : StateT (List (Sigma P.B)) P.FreeM (P.B op) := fun events =>
  (fun answer => (answer, events ++ [⟨op, answer⟩])) <$> lift op

/-- Recording through a stateful handler appends exactly the source program's trace. -/
theorem liftM_traceHandler (program : P.FreeM α) (events : List (Sigma P.B)) :
    (program.liftM traceHandler).run events =
      (fun out => (out.1, events ++ out.2)) <$> trace program := by
  induction program generalizing events with
  | pure value => simp
  | lift_bind op cont ih =>
    change (lift op >>= fun answer => ((cont answer).liftM traceHandler).run
      (events ++ [⟨op, answer⟩])) =
        (fun out => (out.1, events ++ out.2)) <$> trace (.liftBind op cont)
    simp only [ih, trace, map_eq_pure_bind, LawfulMonad.bind_assoc,
      LawfulMonad.pure_bind, List.append_assoc, List.singleton_append]

/-- The ordinary trace operation can run through an interpreter's stateful handler. -/
theorem trace_eq_liftM (program : P.FreeM α) :
    trace program = (program.liftM traceHandler).run [] := by
  simp [liftM_traceHandler]

variable [DecidableEq P.A]

/-- Answer from a recorded prefix, then forward fresh requests. A mismatched shape fails. -/
def replayHandler (op : P.A) : StateT (List (Sigma P.B)) (OptionT P.FreeM) (P.B op) :=
  fun events => match events with
  | [] => OptionT.mk ((fun answer => some (answer, [])) <$> lift op)
  | ⟨recorded, answer⟩ :: events =>
    if h : recorded = op then pure (h ▸ answer, events) else failure

@[simp] theorem replayHandler_run_nil (op : P.A) :
    (replayHandler op).run [] = OptionT.mk ((fun answer => some (answer, [])) <$> lift op) := rfl

@[simp] theorem replayHandler_run_cons (op recorded : P.A) (answer : P.B recorded)
    (events : List (Sigma P.B)) :
    (replayHandler op).run (⟨recorded, answer⟩ :: events) =
      if h : recorded = op then pure (h ▸ answer, events) else failure := rfl

/-- Execute from the start using a recorded prefix. Reject a prefix extending past return. -/
def runWithReplay (events : List (Sigma P.B)) (program : P.FreeM α) : OptionT P.FreeM α := do
  let (value, remaining) ← (program.liftM replayHandler).run events
  if remaining.isEmpty then pure value else failure

theorem liftM_replayHandler_nil (program : P.FreeM α) :
    ((program.liftM replayHandler).run []).run =
      (fun value => some (value, [])) <$> program := by
  induction program with
  | pure value => rfl
  | lift_bind op cont ih =>
    change (lift op >>= fun answer => (((cont answer).liftM replayHandler).run []).run) = _
    simp only [ih, bind_eq_bind, _root_.map_bind]

/-- Running with a prefix executes exactly the continuation reconstructed by structural replay.
All effects before the replay point are suppressed, and fresh effects retain their order. -/
theorem runWithReplay_eq (events : List (Sigma P.B)) (program : P.FreeM α) :
    (runWithReplay events program).run =
      (replay events program).elim (pure none) (fun rest => some <$> rest) := by
  induction events generalizing program with
  | nil =>
    simp only [runWithReplay, OptionT.run_bind, liftM_replayHandler_nil]
    simp [replay]
  | cons event events ih =>
    rcases event with ⟨recorded, answer⟩
    cases program with
    | pure value => simp [runWithReplay, replay]
    | liftBind op cont =>
      by_cases h : recorded = op
      · subst recorded
        simpa [runWithReplay, replay] using ih (cont answer)
      · simp [runWithReplay, replay, h]

@[simp] theorem runWithReplay_nil (program : P.FreeM α) :
    (runWithReplay [] program).run = some <$> program := by
  rw [runWithReplay_eq, replay_nil, Option.elim_some]

/-- Consuming a matching prefix entry performs no visible operation. -/
@[simp] theorem runWithReplay_lift_bind_cons (op : P.A) (answer : P.B op)
    (events : List (Sigma P.B)) (cont : P.B op → P.FreeM α) :
    (runWithReplay (⟨op, answer⟩ :: events) (lift op >>= cont)).run =
      (runWithReplay events (cont answer)).run := by
  change (runWithReplay (⟨op, answer⟩ :: events) (.liftBind op cont)).run = _
  simp only [runWithReplay_eq, replay, dite_true]

end Handlers

section Stateful

universe u

variable {P Q : PFunctor.{u, u}} {α State : Type u}

/-- An invariant preserved by each successful handler call holds after an adaptive program.
The invariant may relate the final state to the entire trace, including an existing prefix.
Aborted runs have no successful result and impose no postcondition. -/
theorem trace_liftM_stateT_invariant
    (handler : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (invariant : List (Sigma Q.B) → State → Prop)
    (step : ∀ op before state answer state' events, invariant before state →
      MonadAttach.CanReturn (trace ((handler op).run state).run)
        (some (answer, state'), events) → invariant (before ++ events) state')
    (x : P.FreeM α) (before : List (Sigma Q.B)) (state : State)
    (hstate : invariant before state) {a : α} {state' : State} {events : List (Sigma Q.B)}
    (h : MonadAttach.CanReturn (trace ((x.liftM handler).run state).run)
      (some (a, state'), events)) : invariant (before ++ events) state' := by
  induction x generalizing before state a state' events with
  | pure value =>
    have hout : (some (a, state'), events) = (some (value, state), []) := h
    cases hout
    simpa using hstate
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind, StateT.run_bind] at h
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk] at h
    rw [bind_eq_bind] at h
    obtain ⟨out, first, rest, hfirst, hrest, rfl⟩ := (canReturn_trace_bind _ _ _).mp h
    cases out with
    | none => cases hrest
    | some out =>
      simpa only [List.append_assoc] using
        ih out.1 (before ++ first) out.2 (step op _ _ _ _ _ hstate hfirst) hrest

end Stateful

end PFunctor.FreeM
