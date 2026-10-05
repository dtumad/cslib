/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.MonadAttach

/-! Chosen responses, structural attachment, and independent universes. -/

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
example (x : arity.FreeM (ULift.{2} Nat)) :
    (FreeM.possibleOutputs (fun _ => Set.univ) x).Finite :=
  FreeM.possibleOutputs_finite _ (fun _ => Set.toFinite _) x

abbrev coin : PFunctor := ⟨Unit, fun _ => Bool⟩

-- Different response assignments describe the same syntax without competing instances.
example : FreeM.possibleOutputs (P := coin) (fun _ => {true}) (FreeM.lift ()) = {true} := by
  simp

example : FreeM.possibleOutputs (P := coin) (fun _ => {false}) (FreeM.lift ()) = {false} := by
  simp

example : CanReturn (FreeM.lift (P := coin) ()) false := by simp

-- The set interpretation uses the existing universal property into Mathlib's set monad.
example (responses : (op : coin.A) → Set (coin.B op)) (x : coin.FreeM Bool) :
    x.possibleOutputs responses = (x.liftM (m := SetM) responses).run :=
  FreeM.possibleOutputs_eq_liftM responses x

-- A chosen query handler attaches evidence about its own response assignment.
example : FreeM.attachWith (P := coin) (m := Option) (fun _ => {true})
    (fun _ => some ⟨true, rfl⟩) ((FreeM.lift ()).bind fun b => pure (!b)) =
      some ⟨false, true, rfl, rfl⟩ := rfl

-- An empty response assignment is meaningful for a handler that fails.
example : FreeM.attachWith (P := coin) (m := Option) (fun _ => ∅)
    (fun _ => none) (FreeM.lift ()) = none := rfl

-- Chosen output sets also bound interpretations into ordinary monads.
example (x : coin.FreeM Bool) {b : Bool}
    (h : CanReturn (x.liftM (fun _ => (some true : Option Bool))) b) :
    b ∈ FreeM.possibleOutputs (P := coin) (fun _ => {true}) x := by
  refine FreeM.mem_possibleOutputs_of_canReturn_liftM _ _ ?_ x h
  intro op c hc
  exact (LawfulMonadAttach.eq_of_canReturn_pure hc).symm

-- Finite allowed response sets suffice even when the full response type is infinite.
example (x : (⟨Unit, fun _ => Nat⟩ : PFunctor).FreeM Nat) :
    (FreeM.possibleOutputs (fun _ => {0, 1}) x).Finite :=
  FreeM.possibleOutputs_finite _ (fun _ => (Set.finite_singleton _).insert _) x

end CslibTests.PFunctorAttach
