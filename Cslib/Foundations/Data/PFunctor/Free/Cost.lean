/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Data.ENat.Monoid
public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Init.Control.Option

/-!
# Worst-case operation count

`queryBound` counts visible operations, taking a supremum over all responses. It can be infinite
even for a well-founded program if branches have unbounded finite lengths. It does not charge
local computation. A machine runtime certificate must additionally account for that work.

For example, reading a natural number `n` and then making `n` further calls always terminates,
but has no uniform finite bound. Finite response types rule this out: `queryBound_ne_top` proves
that every program with finite branching has a finite bound.
-/

@[expose] public section

namespace PFunctor.FreeM

section Operations

universe uA uB uQ

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}} {α β : Type uB}

/-- The supremum of the operation counts of all execution paths. -/
noncomputable def queryBound : P.FreeM α → ℕ∞
  | .pure _ => 0
  | .liftBind _ cont => 1 + ⨆ b, queryBound (cont b)

@[simp]
theorem queryBound_pure (a : α) : queryBound (pure a : P.FreeM α) = 0 := rfl

@[simp]
theorem queryBound_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    queryBound (lift op >>= cont) = 1 + ⨆ b, queryBound (cont b) := rfl

@[simp]
theorem queryBound_lift (op : P.A) : queryBound (lift (P := P) op) = 1 := by
  change 1 + ⨆ _ : P.B op, (0 : ℕ∞) = 1
  simp

/-- A well-founded program with finite response types has a finite worst-case operation count. -/
theorem queryBound_ne_top [∀ op, Finite (P.B op)] (x : P.FreeM α) : queryBound x ≠ ⊤ := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    intro h
    rcases ENat.add_eq_top.mp h with h | h
    · exact ENat.one_ne_top h
    · exact iSup_ne_top ih h

/-- Sequential composition adds worst-case bounds. -/
theorem queryBound_bind_le (x : P.FreeM α) (f : α → P.FreeM β) (bound : ℕ∞)
    (hf : ∀ a, queryBound (f a) ≤ bound) :
    queryBound (x >>= f) ≤ queryBound x + bound := by
  induction x with
  | pure a => simpa using hf a
  | lift_bind op cont ih =>
    change 1 + ⨆ b, queryBound (cont b >>= f) ≤ (1 + ⨆ b, queryBound (cont b)) + bound
    rw [add_assoc]
    gcongr
    exact iSup_le fun b => (ih b).trans
      (add_le_add (le_iSup (fun b => queryBound (cont b)) b) le_rfl)

/-- Mapping the result preserves the number of operations. -/
@[simp]
theorem queryBound_map (f : α → β) (x : P.FreeM α) :
    queryBound (f <$> x) = queryBound x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change (1 + ⨆ b, queryBound (f <$> cont b)) = 1 + ⨆ b, queryBound (cont b)
    simp only [ih]

/-- Aborting sequential composition does not charge for an unexecuted continuation. -/
theorem queryBound_optionT_bind_le (x : OptionT P.FreeM α) (f : α → OptionT P.FreeM β)
    (bound : ℕ∞) (hf : ∀ a, queryBound (f a).run ≤ bound) :
    queryBound (x >>= f).run ≤ queryBound x.run + bound := by
  simp only [OptionT.run_bind]
  apply queryBound_bind_le
  intro value
  cases value with
  | none => exact bot_le
  | some value => exact hf value

/-- Inlining handlers charges their implementation, rather than treating them as unit-cost. -/
theorem queryBound_liftM_le (handler : (op : P.A) → Q.FreeM (P.B op))
    (bound : ℕ∞) (h : ∀ op, queryBound (handler op) ≤ bound) (x : P.FreeM α) :
    queryBound (x.liftM handler) ≤ queryBound x * bound := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind]
    calc
      _ ≤ queryBound (handler op) + (⨆ b, queryBound (cont b)) * bound :=
        queryBound_bind_le _ _ _ fun b => (ih b).trans
          (by gcongr; exact le_iSup (fun b => queryBound (cont b)) b)
      _ ≤ bound + (⨆ b, queryBound (cont b)) * bound := add_le_add (h op) le_rfl
      _ = _ := by
        change bound + (⨆ b, queryBound (cont b)) * bound =
          (1 + ⨆ b, queryBound (cont b)) * bound
        rw [add_mul, one_mul]

end Operations

section Selected

universe uA uB uQ

section Bounds

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}} {α β : Type uB}

/-- The worst-case number of selected operations. Unselected operations contribute no cost. -/
noncomputable def queryBoundP (select : P.A → Bool) : P.FreeM α → ℕ∞
  | .pure _ => 0
  | .liftBind op cont => (if select op then 1 else 0) + ⨆ answer, queryBoundP select (cont answer)

@[simp]
theorem queryBoundP_pure (select : P.A → Bool) (a : α) :
    queryBoundP select (pure a : P.FreeM α) = 0 := rfl

@[simp]
theorem queryBoundP_lift_bind (select : P.A → Bool) (op : P.A) (cont : P.B op → P.FreeM α) :
    queryBoundP select (lift op >>= cont) =
      (if select op then 1 else 0) + ⨆ answer, queryBoundP select (cont answer) := rfl

@[simp]
theorem queryBoundP_lift (select : P.A → Bool) (op : P.A) :
    queryBoundP select (lift (P := P) op) = if select op then 1 else 0 := by
  change (if select op then 1 else 0) + ⨆ _ : P.B op, (0 : ℕ∞) = _
  simp

@[simp]
theorem queryBoundP_false (x : P.FreeM α) : queryBoundP (fun _ => false) x = 0 := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    simp only [bind_eq_bind, queryBoundP_lift_bind, Bool.false_eq_true, ↓reduceIte,
      ih, ENat.iSup_zero, add_zero]

@[simp]
theorem queryBoundP_true (x : P.FreeM α) : queryBoundP (fun _ => true) x = queryBound x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    simp only [bind_eq_bind, queryBoundP_lift_bind, queryBound_lift_bind, ↓reduceIte, ih]

/-- Counting only selected operations never exceeds the total operation bound. -/
theorem queryBoundP_le_queryBound (select : P.A → Bool) (x : P.FreeM α) :
    queryBoundP select x ≤ queryBound x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind op cont ih =>
    simp only [bind_eq_bind, queryBoundP_lift_bind, queryBound_lift_bind]
    apply add_le_add _ (iSup_mono ih)
    cases select op <;> simp

/-- Finite response types also give a finite bound on every selected family of operations. -/
theorem queryBoundP_ne_top [∀ op, Finite (P.B op)] (select : P.A → Bool) (x : P.FreeM α) :
    queryBoundP select x ≠ ⊤ :=
  ne_top_of_le_ne_top (queryBound_ne_top x) (queryBoundP_le_queryBound select x)

/-- Bounds on selected operations add under sequential composition. -/
theorem queryBoundP_bind_le (select : P.A → Bool) (x : P.FreeM α) (f : α → P.FreeM β)
    (bound : ℕ∞) (hf : ∀ a, queryBoundP select (f a) ≤ bound) :
    queryBoundP select (x >>= f) ≤ queryBoundP select x + bound := by
  induction x with
  | pure a => simpa using hf a
  | lift_bind op cont ih =>
    change (if select op then 1 else 0) + ⨆ answer, queryBoundP select (cont answer >>= f) ≤
      ((if select op then 1 else 0) + ⨆ answer, queryBoundP select (cont answer)) + bound
    rw [add_assoc]
    gcongr
    exact iSup_le fun answer => (ih answer).trans
      (add_le_add (le_iSup (fun b => queryBoundP select (cont b)) answer) le_rfl)

@[simp]
theorem queryBoundP_map (select : P.A → Bool) (f : α → β) (x : P.FreeM α) :
    queryBoundP select (f <$> x) = queryBoundP select x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change (if select op then 1 else 0) + ⨆ answer, queryBoundP select (f <$> cont answer) =
      (if select op then 1 else 0) + ⨆ answer, queryBoundP select (cont answer)
    simp only [ih]

/-- An inlined operation may use at most the cost charged to its source operation. -/
theorem queryBoundP_liftM_le_mul (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → Q.FreeM (P.B op)) (cost : ℕ∞)
    (hhandler : ∀ op, queryBoundP target (handler op) ≤ if select op then cost else 0)
    (x : P.FreeM α) : queryBoundP target (x.liftM handler) ≤ queryBoundP select x * cost := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind]
    calc
      _ ≤ queryBoundP target (handler op) + (⨆ b, queryBoundP select (cont b)) * cost :=
        queryBoundP_bind_le _ _ _ _ fun b => (ih b).trans
          (by gcongr; exact le_iSup (fun b => queryBoundP select (cont b)) b)
      _ ≤ (if select op then cost else 0) + (⨆ b, queryBoundP select (cont b)) * cost :=
        add_le_add (hhandler op) le_rfl
      _ = _ := by
        simp only [queryBoundP_lift_bind, add_mul]
        cases select op <;> simp

/-- An inlined operation may use at most the cost charged to its source operation. -/
theorem queryBoundP_liftM_le (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → Q.FreeM (P.B op))
    (hhandler : ∀ op, queryBoundP target (handler op) ≤ if select op then 1 else 0)
    (x : P.FreeM α) : queryBoundP target (x.liftM handler) ≤ queryBoundP select x := by
  simpa using queryBoundP_liftM_le_mul select target handler 1 hhandler x

/-- A finite query budget pays for the current operation before bounding each continuation. -/
theorem queryBoundP_cont_le (select : P.A → Bool) (op : P.A) (cont : P.B op → P.FreeM α)
    (n : ℕ) (h : queryBoundP select (lift op >>= cont) ≤ n) :
    (select op).toNat ≤ n ∧
      ∀ answer, queryBoundP select (cont answer) ≤ ((n - (select op).toNat : ℕ) : ℕ∞) := by
  have hsum : ((select op).toNat : ℕ∞) + ⨆ answer, queryBoundP select (cont answer) ≤ n := by
    cases hs : select op <;> simpa [queryBoundP_lift_bind, hs] using h
  have hcost : (select op).toNat ≤ n := by
    exact_mod_cast (le_self_add.trans hsum)
  refine ⟨hcost, fun answer => ?_⟩
  apply (ENat.add_le_add_iff_left (k := ((select op).toNat : ℕ∞)) (by simp)).mp
  calc
    _ ≤ (select op).toNat + ⨆ b, queryBoundP select (cont b) :=
      add_le_add le_rfl (le_iSup (fun b => queryBoundP select (cont b)) answer)
    _ ≤ n := hsum
    _ = _ := by norm_cast; omega

/-- Selecting either family costs at most the sum of the two separate bounds. -/
theorem queryBoundP_or_le (first second : P.A → Bool) (x : P.FreeM α) :
    queryBoundP (fun op => first op || second op) x ≤
      queryBoundP first x + queryBoundP second x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind op cont ih =>
    simp only [bind_eq_bind, queryBoundP_lift_bind]
    have hsup : (⨆ answer, queryBoundP (fun op => first op || second op) (cont answer)) ≤
        (⨆ answer, queryBoundP first (cont answer)) +
          ⨆ answer, queryBoundP second (cont answer) :=
      iSup_le fun answer => (ih answer).trans
        (add_le_add (le_iSup (fun b => queryBoundP first (cont b)) answer)
          (le_iSup (fun b => queryBoundP second (cont b)) answer))
    have hselect : (if first op || second op then 1 else 0 : ℕ∞) ≤
        (if first op then 1 else 0) + (if second op then 1 else 0) := by
      cases first op <;> cases second op <;> simp
    simpa only [add_add_add_comm] using add_le_add hselect hsup

end Bounds

variable {P : PFunctor.{uB, uB}} {α : Type uB}

/-- Recording an execution adds no operations. -/
@[simp] theorem queryBoundP_trace (select : P.A → Bool) (x : P.FreeM α) :
    queryBoundP select (trace x) = queryBoundP select x := by
  induction x with
  | pure value => rfl
  | lift_bind op cont ih =>
    change queryBoundP select (trace (.liftBind op cont)) =
      queryBoundP select (.liftBind op cont)
    simp only [trace, ← map_eq_pure_bind, queryBoundP_map, queryBoundP_lift_bind, ih]
    rfl

/-- Every recorded execution satisfies the worst-case bound on selected operations. -/
theorem countP_trace_le_queryBoundP (select : P.A → Bool) (x : P.FreeM α)
    {out : α × List (Sigma P.B)} (h : MonadAttach.CanReturn (trace x) out) :
    (out.2.countP (fun event => select event.1) : ℕ∞) ≤ queryBoundP select x := by
  induction x generalizing out with
  | pure a =>
    have hout : out = (a, []) := h
    subst out
    exact le_rfl
  | lift_bind op cont ih =>
    obtain ⟨answer, events, hrest, hevents⟩ := (canReturn_trace_lift_bind _ _ _ _).mp h
    have hle := (ih answer (out := (out.1, events)) hrest).trans
      (le_iSup (fun answer => queryBoundP select (cont answer)) answer)
    simp only [bind_eq_bind, queryBoundP_lift_bind, hevents, List.countP_cons]
    cases hselect : select op <;> simp_all [add_comm]

/-- If every operation has a response, bounding all complete executions bounds the program.
This lets observable execution traces certify a syntactic query budget. -/
theorem queryBoundP_le_of_countP_trace_le [∀ op, Nonempty (P.B op)]
    (select : P.A → Bool) (x : P.FreeM α) (n : ℕ)
    (h : ∀ out, MonadAttach.CanReturn (trace x) out →
      out.2.countP (fun event => select event.1) ≤ n) : queryBoundP select x ≤ n := by
  induction x generalizing n with
  | pure value => simp
  | lift_bind op cont ih =>
    have hnext answer out (hout : MonadAttach.CanReturn (trace (cont answer)) out) :
        (select op).toNat + out.2.countP (fun event => select event.1) ≤ n := by
      have := h (out.1, ⟨op, answer⟩ :: out.2)
        ((canReturn_trace_lift_bind op cont _ _).mpr ⟨answer, out.2, hout, rfl⟩)
      cases hs : select op <;> simpa [List.countP_cons, hs, Nat.add_comm] using this
    have hcost : (select op).toNat ≤ n := by
      obtain ⟨answer⟩ := (inferInstance : Nonempty (P.B op))
      obtain ⟨value, hvalue⟩ := exists_canReturn (cont answer)
      obtain ⟨events, hevents⟩ := exists_trace_of_canReturn (cont answer) hvalue
      exact Nat.le_trans (Nat.le_add_right _ _) (hnext answer (value, events) hevents)
    have hrest : (⨆ answer, queryBoundP select (cont answer)) ≤
        ((n - (select op).toNat : ℕ) : ℕ∞) := by
      apply iSup_le
      intro answer
      apply ih answer
      intro out hout
      have := hnext answer out hout
      omega
    calc
      _ = ((select op).toNat : ℕ∞) + ⨆ answer, queryBoundP select (cont answer) := by
        cases hs : select op <;> simp [queryBoundP_lift_bind, hs]
      _ ≤ (select op).toNat + (n - (select op).toNat : ℕ) := add_le_add le_rfl hrest
      _ = n := by norm_cast; omega

end Selected

section Stateful

universe u

variable {P Q : PFunctor.{u, u}} {α State : Type u}

/-- A stateful implementation charges at most `cost` target operations for each selected call. -/
theorem queryBoundP_liftM_stateT_le_mul (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → StateT State Q.FreeM (P.B op)) (cost : ℕ∞)
    (hhandler : ∀ op state, queryBoundP target ((handler op).run state) ≤
      if select op then cost else 0) (x : P.FreeM α) (state : State) :
    queryBoundP target ((x.liftM handler).run state) ≤ queryBoundP select x * cost := by
  induction x generalizing state with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind, StateT.run_bind]
    calc
      _ ≤ queryBoundP target ((handler op).run state) +
          (⨆ answer, queryBoundP select (cont answer)) * cost :=
        queryBoundP_bind_le _ _ _ _ fun out => (ih out.1 out.2).trans
          (by gcongr; exact le_iSup (fun b => queryBoundP select (cont b)) out.1)
      _ ≤ (if select op then cost else 0) +
          (⨆ answer, queryBoundP select (cont answer)) * cost :=
        add_le_add (hhandler op state) le_rfl
      _ = _ := by
        simp only [queryBoundP_lift_bind, add_mul]
        cases select op <;> simp

/-- The same charge remains valid for a handler that may abort. Failed calls do not execute
the continuation. -/
theorem queryBoundP_liftM_stateT_optionT_le_mul (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (cost : ℕ∞)
    (hhandler : ∀ op state, queryBoundP target ((handler op).run state).run ≤
      if select op then cost else 0) (x : P.FreeM α) (state : State) :
    queryBoundP target ((x.liftM handler).run state).run ≤ queryBoundP select x * cost := by
  induction x generalizing state with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind, StateT.run_bind]
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk]
    rw [bind_eq_bind]
    apply (queryBoundP_bind_le target _ _
      ((⨆ answer, queryBoundP select (cont answer)) * cost) ?_).trans
    · calc
        _ ≤ (if select op then cost else 0) +
            (⨆ answer, queryBoundP select (cont answer)) * cost :=
          add_le_add (hhandler op state) le_rfl
        _ = _ := by
          simp only [bind_eq_bind, queryBoundP_lift_bind, add_mul]
          cases select op <;> simp
    · intro out
      cases out with
      | none => exact bot_le
      | some out =>
        exact (ih out.1 out.2).trans
          (by gcongr; exact le_iSup (fun answer => queryBoundP select (cont answer)) out.1)

/-- Inlining a stateful handler preserves a query bound when every handler call uses at most
the cost charged to its source operation. Aborting a call does not run the continuation. -/
theorem queryBoundP_liftM_stateT_le (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (hhandler : ∀ op state, queryBoundP target ((handler op).run state).run ≤
      if select op then 1 else 0) (x : P.FreeM α) (state : State) :
    queryBoundP target ((x.liftM handler).run state).run ≤ queryBoundP select x := by
  simpa using queryBoundP_liftM_stateT_optionT_le_mul select target handler 1 hhandler x state

end Stateful

end PFunctor.FreeM
