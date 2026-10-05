/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Trace

/-! # Bounds on a selected family of operations -/

@[expose] public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
