/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Mathlib.Data.Nat.PSub

/-!
# Adaptive forking of polynomial programs

The first result selects an occurrence of a chosen family of operations. `fork` retains the
continuation at that occurrence and runs it again with a fresh answer. The selected occurrence
is counted from zero; `none` or an index beyond the execution causes no second run.

Mutable state must be inlined before forking: the saved continuation then contains the exact
cache and private state at the selected operation. Interpreting the remaining operations with
measures supplies independent randomness to the two suffixes.

To share a private random tape across both suffixes, sample it before the first selected operation
and pass its bits explicitly to the program. `fork_lift_bind_of_not_select` moves such sampling
outside the fork. Random effects left inside the continuation are resampled, so moving private
randomness outside is a choice of coupling, not merely a change of implementation.
-/

@[expose] public section

/-- Decrementing an optional position succeeds exactly on positive positions. -/
@[simp]
theorem Option.bind_ppred_eq_some {choice : Option ℕ} {n : ℕ} :
    choice.bind Nat.ppred = some n ↔ choice = some (n + 1) := by
  cases choice <;> simp [Nat.ppred_eq_some, eq_comm]

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
      fun a => (choose a).bind Nat.ppred
      else choose) (cont answer)
    if select op && (choose first.1 == some 0) then
      let answer' ← lift op
      let second ← cont answer'
      pure (first.1, some ⟨op, answer, answer', second⟩)
    else pure first

@[simp]
theorem fork_pure (select : P.A → Bool) (choose : α → Option ℕ) (a : α) :
    fork select choose (pure a) = pure (a, none) := rfl

/-- An unselected operation is performed once, and its response is shared by both continuations.
In particular, private randomness sampled here is retained even if it is used after the fork. -/
theorem fork_lift_bind_of_not_select (select : P.A → Bool) (choose : α → Option ℕ)
    (op : P.A) (cont : P.B op → P.FreeM α) (hselect : select op = false) :
    fork select choose (lift op >>= cont) =
      (lift op >>= fun answer => fork select choose (cont answer)) := by
  change fork select choose (.liftBind op cont) = _
  simp only [fork, hselect, Bool.false_eq_true, ↓reduceIte, Bool.false_and, _root_.bind_pure]

/-- Sampling a fixed number of responses to an unselected operation before the program shares
the entire sampled tape across the two runs, including entries read after the fork point. -/
theorem fork_mapM_bind_of_not_select {ι : Type u} (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (inputs : List ι)
    (cont : List (P.B op) → P.FreeM α) (hselect : select op = false) :
    fork select choose (inputs.mapM (fun _ => lift op) >>= cont) =
      (inputs.mapM (fun _ => lift op) >>= fun tape => fork select choose (cont tape)) := by
  induction inputs generalizing cont with
  | nil => simp
  | cons value inputs ih =>
    simp only [List.mapM_cons, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
    rw [fork_lift_bind_of_not_select _ _ _ _ hselect]
    congr 1
    funext answer
    exact ih (fun tape => cont (answer :: tape))

/-- Successful forks whose two executions select occurrence `n` and give distinct answers. -/
def forkSuccess (choose : α → Option ℕ) (n : ℕ) :
    Set (α × Option ((op : P.A) × P.B op × P.B op × α)) :=
  {out | ∃ event, out.2 = some event ∧ choose out.1 = some n ∧
    choose event.2.2.2 = some n ∧ event.2.1 ≠ event.2.2.1}

@[simp]
theorem not_mem_forkSuccess_none (choose : α → Option ℕ) (n : ℕ) (a : α) :
    (a, none) ∉ forkSuccess (P := P) choose n := by simp [forkSuccess]

@[simp]
theorem mem_forkSuccess_some (choose : α → Option ℕ) (n : ℕ) (a : α)
    (event : (op : P.A) × P.B op × P.B op × α) :
    (a, some event) ∈ forkSuccess choose n ↔
      choose a = some n ∧ choose event.2.2.2 = some n ∧ event.2.1 ≠ event.2.2.1 := by
  constructor
  · rintro ⟨_, heq, h⟩
    cases heq
    exact h
  · exact fun h => ⟨event, rfl, h⟩

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
      exact (canReturn_lift_bind op cont _).mpr ⟨answer, ih answer _ (out := first) hfirst⟩
    · have ho : out = first := h
      subst out
      exact (canReturn_lift_bind op cont _).mpr ⟨answer, ih answer _ hfirst⟩

/-- Disabling the selector performs precisely one execution, with no extra effects. -/
theorem fork_choose_none (select : P.A → Bool) (x : P.FreeM α) :
    fork select (fun _ => none) x = (fun a => (a, none)) <$> x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change fork select (fun _ => none) (.liftBind op cont) = _
    rw [fork]
    simp only [Option.bind_none, ite_self, reduceBEq, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, _root_.bind_pure, ih, bind_eq_bind, _root_.map_bind]

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

/-- Both recorded executions contain the selected operation immediately after their shared
prefix. Their responses at that operation may differ. -/
theorem fork_trace_prefix (select : P.A → Bool)
    (choose : α × List (Sigma P.B) → Option ℕ) (x : P.FreeM α)
    {first : α × List (Sigma P.B)}
    {event : (op : P.A) × P.B op × P.B op × (α × List (Sigma P.B))}
    (h : MonadAttach.CanReturn (fork select choose (trace x)) (first, some event)) :
    ∃ before n, choose first = some n ∧
      before.countP (fun e : Sigma P.B => select e.1) = n ∧ select event.1 = true ∧
      before ++ [⟨event.1, event.2.1⟩] <+: first.2 ∧
      before ++ [⟨event.1, event.2.2.1⟩] <+: event.2.2.2.2 := by
  classical
  obtain ⟨before, cont, n, hchoose, hcount, hselect, hreplay, hfirst, hsecond⟩ :=
    fork_sound select choose (trace x) h
  have extend (answer : P.B event.1) :
      replay (before ++ [⟨event.1, answer⟩]) (trace x) = some (cont answer) := by
    rw [replay_append, hreplay]
    change replay [⟨event.1, answer⟩] (.liftBind event.1 cont) = _
    rw [replay, dite_eq_left rfl, replay_nil]
  exact ⟨before, n, hchoose, hcount, hselect,
    trace_prefix_of_replay _ x _ (extend _) hfirst,
    trace_prefix_of_replay _ x _ (extend _) hsecond⟩

end PFunctor.FreeM
