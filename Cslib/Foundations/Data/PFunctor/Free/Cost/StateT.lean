/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered
public import Init.Control.Option

/-! # Operation bounds for stateful handlers that may abort -/

public section

namespace PFunctor.FreeM

universe u

variable {P Q : PFunctor.{u, u}} {α State : Type u}

/-- Inlining a stateful handler preserves a query bound when every handler call uses at most
the cost charged to its source operation. Aborting a call does not run the continuation. -/
theorem queryBoundP_liftM_stateT_le (select : P.A → Bool) (target : Q.A → Bool)
    (handler : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (hhandler : ∀ op state, queryBoundP target ((handler op).run state).run ≤
      if select op then 1 else 0) (x : P.FreeM α) (state : State) :
    queryBoundP target ((x.liftM handler).run state).run ≤ queryBoundP select x := by
  induction x generalizing state with
  | pure a => exact le_rfl
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind, StateT.run_bind]
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk]
    rw [bind_eq_bind]
    apply (queryBoundP_bind_le target _ _ (⨆ answer, queryBoundP select (cont answer)) ?_).trans
    · exact add_le_add (hhandler op state) le_rfl
    · intro out
      cases out with
      | none => exact bot_le
      | some out =>
        exact (ih out.1 out.2).trans
          (le_iSup (fun answer => queryBoundP select (cont answer)) out.1)

end PFunctor.FreeM
