/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Lens

/-! A request's reply type can depend on its position, independently of the return universe. -/

open PFunctor

namespace Tests.PFunctorLens

private abbrev sized : PFunctor := ⟨Nat, fun n => Fin (n + 1)⟩

private def offset : Lens sized sized :=
  ⟨Nat.succ, fun (n : Nat) b => (0 : Fin (n + 1)).predAbove b⟩

example (x : sized.FreeM (ULift.{1} Nat)) :
    (x.mapLens offset).mapLens offset = x.mapLens (offset ∘ₗ offset) :=
  FreeM.mapLens_mapLens _ _ _

example (x : sized.FreeM Nat) :
    (x.mapLens offset).liftM (fun n => some (Fin.last n)) =
      x.liftM (fun n => some (offset.toFunB n (Fin.last (offset.toFunA n)))) :=
  FreeM.liftM_mapLens offset _ x

end Tests.PFunctorLens
