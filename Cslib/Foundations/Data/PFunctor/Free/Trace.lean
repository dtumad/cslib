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

variable {P : PFunctor.{u, u}} {α : Type u}

/-- Record operations and answers in their execution order. -/
def trace : P.FreeM α → P.FreeM (α × List (Sigma P.B))
  | .pure a => pure (a, [])
  | .liftBind op cont => do
    let answer ← lift op
    let (a, events) ← trace (cont answer)
    pure (a, ⟨op, answer⟩ :: events)

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

end PFunctor.FreeM
