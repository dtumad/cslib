/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Trace

/-!
# Adaptive forking of polynomial programs

The first result selects an occurrence of a chosen family of operations. `fork` retains the
continuation at that occurrence and runs it again with a fresh answer. The selected occurrence
is counted from zero; `none` or an index beyond the execution causes no second run.

Mutable state must be inlined before forking: the saved continuation then contains the exact
cache and private state at the selected operation. Interpreting the remaining operations with
measures supplies independent randomness to the two suffixes.
-/

@[expose] public section

namespace PFunctor.FreeM

universe u

variable {P : PFunctor.{u, u}} {α : Type u}

/-- Fork after seeing the first result. The optional result records the operation, both answers,
and the second output. The prefix is executed once, and the first output is always retained. -/
def fork (select : P.A → Bool) (choose : α → Option ℕ) :
    P.FreeM α → P.FreeM (α × Option ((op : P.A) × P.B op × P.B op × α))
  | .pure a => pure (a, none)
  | .liftBind op cont => do
    let answer ← lift op
    let first ← fork select (if select op then
      fun a => match choose a with | some (n + 1) => some n | _ => none
      else choose) (cont answer)
    if select op && (choose first.1 == some 0) then
      let answer' ← lift op
      let second ← cont answer'
      pure (first.1, some ⟨op, answer, answer', second⟩)
    else pure first

@[simp]
theorem fork_pure (select : P.A → Bool) (choose : α → Option ℕ) (a : α) :
    fork select choose (pure a) = pure (a, none) := rfl

/-- The recorded first result belongs to the original program for every choice of responses. -/
theorem canReturn_fst_fork (select : P.A → Bool) (choose : α → Option ℕ) (x : P.FreeM α)
    {out : α × Option ((op : P.A) × P.B op × P.B op × α)}
    (h : MonadAttach.CanReturn (fork select choose x) out) :
    MonadAttach.CanReturn x out.1 := by
  induction x generalizing choose out with
  | pure a =>
    have ho : out = (a, none) := h
    subst out
    exact rfl
  | lift_bind op cont ih =>
    obtain ⟨answer, h⟩ := (canReturn_lift_bind _ _ _).mp h
    obtain ⟨first, hfirst, h⟩ := (canReturn_bind _ _ _).mp h
    split at h
    · obtain ⟨answer', h⟩ := (canReturn_lift_bind _ _ _).mp h
      obtain ⟨second, _, h⟩ := (canReturn_bind _ _ _).mp h
      have ho : out = (first.1, some ⟨op, answer, answer', second⟩) := h
      subst out
      exact ⟨answer, ih answer _ (out := first) hfirst⟩
    · have ho : out = first := h
      subst out
      exact ⟨answer, ih answer _ hfirst⟩

/-- Disabling the selector performs precisely one execution, with no extra effects. -/
theorem fork_choose_none (select : P.A → Bool) (x : P.FreeM α) :
    fork select (fun _ => none) x = (fun a => (a, none)) <$> x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change fork select (fun _ => none) (.liftBind op cont) = _
    rw [fork]
    simp only [ite_self, reduceBEq, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      _root_.bind_pure, ih, bind_eq_bind, _root_.map_bind]

/-- A successful fork shares an exact replay prefix and the same continuation at its focus.
In particular, state captured by that continuation is shared by the two executions. -/
theorem fork_sound [DecidableEq P.A] (select : P.A → Bool) (choose : α → Option ℕ)
    (x : P.FreeM α) {first : α} {event : (op : P.A) × P.B op × P.B op × α}
    (h : MonadAttach.CanReturn (fork select choose x) (first, some event)) :
    ∃ before cont n, choose first = some n ∧
      before.countP (fun e : Sigma P.B => select e.1) = n ∧ select event.1 = true ∧
      replay before x = some (.liftBind event.1 cont) ∧
      MonadAttach.CanReturn (cont event.2.1) first ∧
      MonadAttach.CanReturn (cont event.2.2.1) event.2.2.2 := by
  induction x generalizing choose first event with
  | pure a => cases h
  | lift_bind op cont ih =>
    obtain ⟨answer, h⟩ := (canReturn_lift_bind _ _ _).mp h
    obtain ⟨out, hout, h⟩ := (canReturn_bind _ _ _).mp h
    split at h
    next hfocus =>
      obtain ⟨answer', h⟩ := (canReturn_lift_bind _ _ _).mp h
      obtain ⟨second, hsecond, h⟩ := (canReturn_bind _ _ _).mp h
      have ho : (first, some event) = (out.1, some ⟨op, answer, answer', second⟩) := h
      cases ho
      have hf : select op = true ∧ choose out.1 = some 0 := by simpa using hfocus
      obtain ⟨hselect, hchoose⟩ := hf
      exact ⟨[], cont, 0, by simpa using hchoose, rfl, hselect, rfl,
        canReturn_fst_fork _ _ _ hout, hsecond⟩
    next hfocus =>
      have ho : (first, some event) = out := h
      subst out
      obtain ⟨before, rest, n, hchoose, hcount, hselect, hreplay, hfirst, hsecond⟩ :=
        ih answer _ hout
      refine ⟨⟨op, answer⟩ :: before, rest, if select op then n + 1 else n, ?_, ?_,
        hselect, ?_, hfirst, hsecond⟩
      · cases hs : select op with
        | false => simpa [hs] using hchoose
        | true =>
          simp only [hs, ↓reduceIte] at hchoose ⊢
          cases hc : choose first with
          | none => simp [hc] at hchoose
          | some k =>
            cases k with
            | zero => simp [hc] at hchoose
            | succ k => simpa [hc] using hchoose
      · cases hs : select op <;> simp [hcount, hs]
      · change replay (⟨op, answer⟩ :: before) (.liftBind op cont) = _
        simpa only [replay, dite_true] using hreplay

end PFunctor.FreeM
