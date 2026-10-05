/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-! Reachability with empty responses, attached proofs, and independent universes. -/

open PFunctor MonadAttach

namespace CslibTests.PFunctorAttach

abbrev arity : PFunctor := ⟨Nat, Fin⟩

-- A nullary operation cannot return, despite being a well-founded program.
example (a : Nat) : ¬ CanReturn ((FreeM.lift (P := arity) 0).bind
    (fun b => Fin.elim0 b) : arity.FreeM Nat) a := by
  intro h
  obtain ⟨b, _⟩ := (FreeM.canReturn_lift_bind _ _ _).mp h
  exact Fin.elim0 b

-- Attached proofs can be used to refine the result type without changing the program.
example (x : arity.FreeM Nat) :
    Subtype.val <$> MonadAttach.attach x = x := by
  exact WeaklyLawfulMonadAttach.map_attach

-- The response and result universes are independent.
example (x : arity.FreeM (ULift.{2} Nat)) : (FreeM.support x).Finite :=
  FreeM.support_finite x

end CslibTests.PFunctorAttach
