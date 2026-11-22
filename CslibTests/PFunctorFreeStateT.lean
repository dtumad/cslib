/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Basic
import Cslib.Foundations.Data.PFunctor.Free.StateT

/-! A state representation can forget part of the state while preserving failure. -/

namespace CslibTests.PFunctorFreeStateT

open PFunctor

private def step (n : Nat) : Option (Bool × Nat) :=
  match n with
  | 0 => none
  | k + 1 => some (k % 2 == 0, k)

-- Forgetting a Boolean flag preserves both failure and the remaining counter for every program.
example (p : (monomial Unit Bool).FreeM Bool) (s : Nat × Bool) :
    Prod.map id Prod.fst <$>
      (p.liftM (P := monomial Unit Bool) (m := StateT (Nat × Bool) Option) (fun _ st =>
        (fun (b, k) => (b, k, !st.2)) <$> step st.1)).run s =
      (p.liftM (P := monomial Unit Bool) (m := StateT Nat Option) (fun _ => step)).run s.1 := by
  apply PFunctor.FreeM.map_state_run_liftM
  intro _ st
  cases hs : step st.1 <;> simp [StateT.run, hs]

end CslibTests.PFunctorFreeStateT
