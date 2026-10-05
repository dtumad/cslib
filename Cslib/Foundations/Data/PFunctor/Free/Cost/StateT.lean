/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered
public import Init.Control.Option

/-! # Operation bounds for stateful handlers -/

public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
