/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-!
# Recording and replaying polynomial programs

A trace records each operation with its dependent response type. Replaying checks operation
shapes as well as responses. The remaining continuation contains the program's private state;
replaying a prefix therefore preserves that state, rather than merely its output distribution.
-/

@[expose] public section

namespace PFunctor.FreeM

universe u

variable {P : PFunctor.{u, u}} {α β : Type u}

/-- Record operations and answers in their execution order. -/
def trace : P.FreeM α → P.FreeM (α × List (Sigma P.B))
  | .pure a => pure (a, [])
  | .liftBind op cont => do
    let answer ← lift op
    let (a, events) ← trace (cont answer)
    pure (a, ⟨op, answer⟩ :: events)

@[simp]
theorem trace_pure (a : α) : trace (pure a : P.FreeM α) = pure (a, []) := rfl

@[simp]
theorem trace_lift (op : P.A) :
    trace (lift (P := P) op) = (fun answer => (answer, [⟨op, answer⟩])) <$> lift op := rfl

theorem trace_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    trace (lift op >>= cont) = (do
      let answer ← lift op
      let out ← trace (cont answer)
      pure (out.1, ⟨op, answer⟩ :: out.2)) := rfl

theorem canReturn_trace_lift_bind (op : P.A) (cont : P.B op → P.FreeM α)
    (a : α) (events : List (Sigma P.B)) :
    MonadAttach.CanReturn (trace (lift op >>= cont)) (a, events) ↔
      ∃ answer after, MonadAttach.CanReturn (trace (cont answer)) (a, after) ∧
        events = ⟨op, answer⟩ :: after := by
  change MonadAttach.CanReturn ((lift op).bind fun answer =>
    (trace (cont answer)).bind fun out => pure (out.1, ⟨op, answer⟩ :: out.2)) _ ↔ _
  simp only [canReturn_bind, canReturn_lift, true_and, canReturn_pure, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨answer, b, after, h, rfl, hevents⟩
    exact ⟨answer, after, h, hevents⟩
  · rintro ⟨answer, after, h, hevents⟩
    exact ⟨answer, a, after, h, rfl, hevents⟩

/-- Sequential composition concatenates the two execution traces. -/
theorem trace_bind (x : P.FreeM α) (f : α → P.FreeM β) :
    trace (x >>= f) = (do
      let (a, before) ← trace x
      let (b, after) ← trace (f a)
      pure (b, before ++ after)) := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    change trace (.liftBind op fun answer => cont answer >>= f) = (do
      let (a, before) ← trace (.liftBind op cont)
      let (b, after) ← trace (f a)
      pure (b, before ++ after))
    simp only [trace, ih, LawfulMonad.bind_assoc, LawfulMonad.pure_bind, List.cons_append]

@[simp]
theorem trace_map (f : α → β) (x : P.FreeM α) :
    trace (f <$> x) = (fun out => (f out.1, out.2)) <$> trace x := by
  rw [map_eq_pure_bind, trace_bind]
  simp only [trace_pure, LawfulMonad.pure_bind, List.append_nil]
  rw [map_eq_pure_bind]

/-- A traced bind exposes the intermediate value and the two consecutive traces. -/
theorem canReturn_trace_bind (x : P.FreeM α) (f : α → P.FreeM β)
    (out : β × List (Sigma P.B)) :
    MonadAttach.CanReturn (trace (x >>= f)) out ↔
      ∃ a before after, MonadAttach.CanReturn (trace x) (a, before) ∧
        MonadAttach.CanReturn (trace (f a)) (out.1, after) ∧ out.2 = before ++ after := by
  rw [trace_bind]
  simp only [← bind_eq_bind, canReturn_bind, canReturn_pure, Prod.exists]
  constructor
  · rintro ⟨a, before, hx, b, after, hf, hout⟩
    cases hout
    exact ⟨a, before, after, hx, hf, rfl⟩
  · rintro ⟨a, before, after, hx, hf, hevents⟩
    exact ⟨a, before, hx, out.1, after, hf, Prod.ext rfl hevents⟩

/-- Forgetting the trace recovers the original program, including all its effects. -/
@[simp]
theorem map_fst_trace (x : P.FreeM α) :
    (fun out : α × List (Sigma P.B) => out.1) <$> trace x = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change ((fun out : α × List (Sigma P.B) => out.1) <$> (do
      let answer ← lift op
      let out ← trace (cont answer)
      pure (out.1, ⟨op, answer⟩ :: out.2))) = (lift op >>= cont)
    simp only [_root_.map_bind, LawfulApplicative.map_pure]
    congr 1
    funext answer
    exact (FreeM.bind_pure_comp (fun out : α × List (Sigma P.B) => out.1)
      (trace (cont answer))).trans (ih answer)

/-- Forgetting a reachable trace leaves a reachable return value. -/
theorem canReturn_of_trace (x : P.FreeM α) {out : α × List (Sigma P.B)}
    (h : MonadAttach.CanReturn (trace x) out) : MonadAttach.CanReturn x out.1 := by
  rw [← map_fst_trace x]
  exact (canReturn_map _ _ _).mpr ⟨out, h, rfl⟩

/-- Every structurally reachable return value has a finite execution trace. -/
theorem exists_trace_of_canReturn (x : P.FreeM α) {a : α} (h : MonadAttach.CanReturn x a) :
    ∃ events, MonadAttach.CanReturn (trace x) (a, events) := by
  induction x with
  | pure value =>
    have ha : a = value := h
    exact ⟨[], by simp [ha]⟩
  | lift_bind op cont ih =>
    obtain ⟨answer, hanswer⟩ := (canReturn_lift_bind _ _ _).mp h
    obtain ⟨events, hevents⟩ := ih answer hanswer
    exact ⟨⟨op, answer⟩ :: events,
      (canReturn_trace_lift_bind _ _ _ _).mpr ⟨answer, events, hevents, rfl⟩⟩

/-- Recording an already recorded program duplicates its trace without adding effects. -/
theorem trace_trace (x : P.FreeM α) :
    trace (trace x) = (fun out : α × List (Sigma P.B) => (out, out.2)) <$> trace x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    rw [bind_eq_bind, trace_lift_bind]
    simp only [trace_bind, trace_lift, trace_pure, ih, _root_.bind_map_left,
      _root_.map_bind, LawfulMonad.bind_assoc, LawfulMonad.pure_bind,
      LawfulApplicative.map_pure, List.append_nil, List.singleton_append]

/-- Replay a trace prefix. A mismatched operation or a trace extending past return is rejected.
An exhausted trace returns the exact remaining computation, which may then use fresh randomness. -/
def replay [DecidableEq P.A] : List (Sigma P.B) → P.FreeM α → Option (P.FreeM α)
  | [], x => some x
  | _ :: _, .pure _ => none
  | ⟨recordedOp, answer⟩ :: events, .liftBind op cont =>
    if h : recordedOp = op then replay events (cont (h ▸ answer)) else none

@[simp]
theorem replay_nil [DecidableEq P.A] (x : P.FreeM α) : replay [] x = some x := rfl

/-- A recorded trace replays to the recorded result, for every structurally reachable path. -/
theorem replay_trace [DecidableEq P.A] (x : P.FreeM α) {out : α × List (Sigma P.B)}
    (h : MonadAttach.CanReturn (trace x) out) : replay out.2 x = some (pure out.1) := by
  induction x generalizing out with
  | pure a =>
    have ho : out = (a, []) := h
    subst out
    rfl
  | lift_bind op cont ih =>
    obtain ⟨answer, h⟩ := (canReturn_lift_bind _ _ _).mp h
    obtain ⟨rest, hrest, hout⟩ := (canReturn_bind _ _ _).mp h
    have ho : out = (rest.1, ⟨op, answer⟩ :: rest.2) := hout
    subst out
    change replay (⟨op, answer⟩ :: rest.2) (.liftBind op cont) = some (pure rest.1)
    rw [replay, dite_eq_left rfl]
    exact ih answer hrest

/-- Prefix replay composes without resetting the continuation's private state. -/
theorem replay_append [DecidableEq P.A] (before after : List (Sigma P.B)) (x : P.FreeM α) :
    replay (before ++ after) x = (replay before x).bind (replay after) := by
  induction before generalizing x with
  | nil => rfl
  | cons event before ih =>
    cases event with
    | mk recordedOp answer =>
      cases x with
      | pure a => rfl
      | liftBind op cont =>
        by_cases h : recordedOp = op
        · subst recordedOp
          simpa only [List.cons_append, replay, dite_true] using ih (cont answer)
        · simp only [List.cons_append, replay, dite_eq_right h, Option.bind_none]

/-- A trace of the remaining program extends the replayed prefix to a complete trace. -/
theorem canReturn_trace_of_replay [DecidableEq P.A] (before : List (Sigma P.B))
    (x y : P.FreeM α) (hreplay : replay before x = some y)
    {a : α} {after : List (Sigma P.B)} (h : MonadAttach.CanReturn (trace y) (a, after)) :
    MonadAttach.CanReturn (trace x) (a, before ++ after) := by
  induction before generalizing x with
  | nil =>
    cases hreplay
    exact h
  | cons event before ih =>
    rcases event with ⟨recordedOp, answer⟩
    cases x with
    | pure a => cases hreplay
    | liftBind op cont =>
      simp only [replay] at hreplay
      split at hreplay
      next heq =>
        subst recordedOp
        exact (canReturn_trace_lift_bind _ _ _ _).mpr
          ⟨answer, before ++ after, ih _ hreplay, rfl⟩
      next => cases hreplay

/-- Any recorded prefix of a traced program is a prefix of the returned trace. -/
theorem trace_prefix_of_replay [DecidableEq P.A] (before : List (Sigma P.B))
    (x : P.FreeM α) (rest : P.FreeM (α × List (Sigma P.B)))
    (hreplay : replay before (trace x) = some rest) {out : α × List (Sigma P.B)}
    (h : MonadAttach.CanReturn rest out) : before <+: out.2 := by
  obtain ⟨after, hafter⟩ := exists_trace_of_canReturn rest h
  have htrace := canReturn_trace_of_replay before (trace x) rest hreplay hafter
  rw [trace_trace] at htrace
  obtain ⟨_, _, heq⟩ := (canReturn_map _ _ _).mp htrace
  have hevents : out.2 = before ++ after := by
    have hfirst := congrArg Prod.fst heq
    cases hfirst
    exact congrArg Prod.snd heq
  exact ⟨after, hevents.symm⟩

end PFunctor.FreeM
