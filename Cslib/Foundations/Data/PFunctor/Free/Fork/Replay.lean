/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork
public import Cslib.Foundations.Data.PFunctor.Free.Trace.Handler
public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered

/-!
# Forking by replaying a recorded prefix

The first execution records its operations and answers. Replaying its prefix from the original
program recovers the selected continuation without reissuing any earlier effect. This is an
exact program equality, including the order of the two suffixes and all returned observations.
-/

@[expose] public section

namespace PFunctor.FreeM

universe u
variable {P : PFunctor.{u, u}} {α : Type u} [DecidableEq P.A]

/-- Replay the recorded prefix and fork at the selected occurrence. A malformed trace or an
out-of-range index gives no second run. Only the fresh suffix performs effects. -/
private def forkAtTrace (select : P.A → Bool) : ℕ → List (Sigma P.B) → P.FreeM α →
    P.FreeM (Option ((op : P.A) × P.B op × P.B op × α))
  | _, [], _ => pure none
  | _, _ :: _, .pure _ => pure none
  | index, ⟨recorded, answer⟩ :: events, .liftBind op cont =>
    if h : recorded = op then
      if select op then
        match index with
        | 0 => do
          let answer' ← lift op
          let second ← cont answer'
          pure (some ⟨op, h ▸ answer, answer', second⟩)
        | index + 1 => forkAtTrace select index events (cont (h ▸ answer))
      else forkAtTrace select index events (cont (h ▸ answer))
    else pure none

/-- Run once, select an occurrence from the result, and recover its continuation by replay. -/
private def forkWithContinuationReplay (select : P.A → Bool) (choose : α → Option ℕ)
    (program : P.FreeM α) :
    P.FreeM (α × Option ((op : P.A) × P.B op × P.B op × α)) := do
  let (first, events) ← trace program
  let second ← (choose first).elim (pure none)
    (fun index => forkAtTrace select index events program)
  pure (first, second)

private theorem queryBoundP_forkAtTrace_le (target select : P.A → Bool) (index : ℕ)
    (events : List (Sigma P.B)) (program : P.FreeM α) :
    queryBoundP target (forkAtTrace select index events program) ≤ queryBoundP target program := by
  induction program generalizing index events with
  | pure value => cases events <;> exact le_rfl
  | lift_bind op cont ih =>
    change queryBoundP target (forkAtTrace select index events (.liftBind op cont)) ≤
      queryBoundP target (.liftBind op cont)
    cases events with
    | nil => exact bot_le
    | cons event events =>
      rcases event with ⟨recorded, answer⟩
      by_cases heq : recorded = op
      · subst recorded
        have hrest (index) : queryBoundP target (forkAtTrace select index events (cont answer)) ≤
            queryBoundP target (.liftBind op cont) :=
          (ih answer index events).trans
            ((le_iSup (fun a => queryBoundP target (cont a)) answer).trans le_add_self)
        cases hs : select op with
        | false =>
          simpa only [forkAtTrace, dite_true, hs, Bool.false_eq_true, ↓reduceIte] using hrest index
        | true =>
          cases index with
          | zero =>
            simp only [forkAtTrace, dite_true, hs, ↓reduceIte, ← map_eq_pure_bind,
              queryBoundP_lift_bind, queryBoundP_map]
            exact le_rfl
          | succ index =>
            simpa only [forkAtTrace, dite_true, hs, ↓reduceIte] using hrest index
      · simp only [forkAtTrace, dite_eq_right heq, queryBoundP_pure, zero_le]

/-- Saving a continuation and replaying its recorded prefix give exactly the same program. -/
private theorem fork_eq_forkWithContinuationReplay (select : P.A → Bool) (choose : α → Option ℕ)
    (program : P.FreeM α) :
    fork select choose program = forkWithContinuationReplay select choose program := by
  induction program generalizing choose with
  | pure value =>
    cases hc : choose value <;>
      simp [forkWithContinuationReplay, hc, forkAtTrace]
  | lift_bind op cont ih =>
    change fork select choose (.liftBind op cont) =
      forkWithContinuationReplay select choose (.liftBind op cont)
    rw [fork]
    simp only [forkWithContinuationReplay, trace, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
    congr 1
    funext answer
    rw [ih]
    simp only [forkWithContinuationReplay, LawfulMonad.bind_assoc]
    congr 1
    funext first
    rcases first with ⟨value, events⟩
    cases hs : select op with
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
        _root_.bind_pure, forkAtTrace, dite_true]
    | true =>
      cases hc : choose value with
      | none => simp [hs, hc, forkAtTrace]
      | some index =>
        cases index with
        | zero => simp [hs, hc, forkAtTrace]
        | succ index => simp [hs, hc, forkAtTrace]

/-- Split immediately before the selected occurrence. The prefix includes unselected operations. -/
def forkPrefix (select : P.A → Bool) : ℕ → List (Sigma P.B) →
    Option (List (Sigma P.B) × Sigma P.B)
  | _, [] => none
  | index, event :: events =>
    if select event.1 then
      match index with
      | 0 => some ([], event)
      | index + 1 => (forkPrefix select index events).map (fun out => (event :: out.1, out.2))
    else (forkPrefix select index events).map (fun out => (event :: out.1, out.2))

omit [DecidableEq P.A] in
/-- When every operation is eligible, the fork prefix is an ordinary list slice. -/
@[simp] theorem forkPrefix_true (index : ℕ) (events : List (Sigma P.B)) :
    forkPrefix (fun _ => true) index events =
      events[index]?.map (fun event => (events.take index, event)) := by
  induction index generalizing events with
  | zero => cases events <;> rfl
  | succ index ih =>
    cases events with
    | nil => rfl
    | cons event events => simp [forkPrefix, ih, Option.map_map, Function.comp_def]

/-- Reexecute from the start with the recorded prefix and a fresh answer at the selected point.
The replay handler rejects incompatible recorded requests. -/
def restartAtTrace (select : P.A → Bool) (index : ℕ) (events : List (Sigma P.B))
    (program : P.FreeM α) : P.FreeM (Option ((op : P.A) × P.B op × P.B op × α)) :=
  (forkPrefix select index events).elim (pure none) fun (before, ⟨op, answer⟩) => do
    let answer' ← lift op
    let second ← (runWithReplay (before ++ [⟨op, answer'⟩]) program).run
    pure (second.map fun value => ⟨op, answer, answer', value⟩)

private theorem forkAtTrace_eq_restartAtTrace (select : P.A → Bool) (index : ℕ)
    (program : P.FreeM α) {value : α} {events : List (Sigma P.B)}
    (h : MonadAttach.CanReturn (trace program) (value, events)) :
    forkAtTrace select index events program = restartAtTrace select index events program := by
  induction program generalizing index value events with
  | pure result =>
    have heq : (value, events) = (result, []) := h
    cases heq
    rfl
  | lift_bind op cont ih =>
    obtain ⟨answer, after, hafter, rfl⟩ := (canReturn_trace_lift_bind op cont value events).mp h
    change forkAtTrace select index (⟨op, answer⟩ :: after) (.liftBind op cont) = _
    cases hs : select op with
    | false =>
      simp only [forkAtTrace, dite_true, hs, Bool.false_eq_true, ↓reduceIte]
      rw [ih answer index hafter]
      simp only [restartAtTrace, forkPrefix, hs, Bool.false_eq_true, ↓reduceIte]
      cases forkPrefix select index after with
      | none => rfl
      | some focus =>
        rcases focus with ⟨before, event⟩
        simp only [Option.map_some, Option.elim_some, List.cons_append, bind_eq_bind,
          runWithReplay_lift_bind_cons]
    | true =>
      cases index with
      | zero =>
        simp [forkAtTrace, hs, restartAtTrace, forkPrefix, runWithReplay_lift_bind_cons]
      | succ index =>
        simp only [forkAtTrace, dite_true, hs, ↓reduceIte]
        rw [ih answer index hafter]
        simp only [restartAtTrace, forkPrefix, hs, ↓reduceIte]
        cases forkPrefix select index after with
        | none => rfl
        | some focus =>
          rcases focus with ⟨before, event⟩
          simp only [Option.map_some, Option.elim_some, List.cons_append, bind_eq_bind,
            runWithReplay_lift_bind_cons]

/-- Restarting at a recorded occurrence uses at most the source program's selected requests.
The prefix is supplied from the trace, without repeating its effects. -/
theorem queryBoundP_restartAtTrace_le (target select : P.A → Bool) (index : ℕ)
    (program : P.FreeM α) {value : α} {events : List (Sigma P.B)}
    (h : MonadAttach.CanReturn (trace program) (value, events)) :
    queryBoundP target (restartAtTrace select index events program) ≤
      queryBoundP target program := by
  rw [← forkAtTrace_eq_restartAtTrace select index program h]
  exact queryBoundP_forkAtTrace_le target select index events program

/-- Run twice from the original program, supplying recorded answers to the second run's
prefix. Only the trace is retained between runs; no continuation is stored. -/
def forkWithReplay (select : P.A → Bool) (choose : α → Option ℕ) (program : P.FreeM α) :
    P.FreeM (α × Option ((op : P.A) × P.B op × P.B op × α)) := do
  let (first, events) ← trace program
  let second ← (choose first).elim (pure none)
    (fun index => restartAtTrace select index events program)
  pure (first, second)

/-- Replaying recorded answers through a handler preserves the full two-run program, including
the selected operation, both its answers, and both results. -/
theorem fork_eq_forkWithReplay (select : P.A → Bool) (choose : α → Option ℕ)
    (program : P.FreeM α) : fork select choose program = forkWithReplay select choose program := by
  rw [fork_eq_forkWithContinuationReplay]
  unfold forkWithContinuationReplay forkWithReplay
  apply bind_congr_of_canReturn
  rintro ⟨value, events⟩ h
  cases hc : choose value with
  | none => simp [hc]
  | some index =>
    simp only [hc, Option.elim_some, forkAtTrace_eq_restartAtTrace select index program h]

omit [DecidableEq P.A] in
/-- A fork issues at most twice the source program's selected operations. Prefix replay
consumes recorded data and contributes no additional requests. -/
theorem queryBoundP_fork_le (target select : P.A → Bool) (choose : α → Option ℕ)
    (program : P.FreeM α) :
    queryBoundP target (fork select choose program) ≤ 2 * queryBoundP target program := by
  classical
  rw [fork_eq_forkWithContinuationReplay]
  unfold forkWithContinuationReplay
  apply (queryBoundP_bind_le target _ _ (queryBoundP target program) ?_).trans
  · simp [two_mul]
  · rintro ⟨value, events⟩
    cases hc : choose value with
    | none => simp [hc]
    | some index =>
      simp only [hc, Option.elim_some, ← map_eq_pure_bind, queryBoundP_map]
      exact queryBoundP_forkAtTrace_le target select index events program

/-- Two source-length answer tapes suffice for the whole two-run replay computation. -/
theorem queryBound_forkWithReplay_le (select : P.A → Bool) (choose : α → Option ℕ)
    (program : P.FreeM α) :
    queryBound (forkWithReplay select choose program) ≤ 2 * queryBound program := by
  rw [← fork_eq_forkWithReplay]
  simpa using queryBoundP_fork_le (fun _ => true) select choose program

end PFunctor.FreeM
