/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Resumption

/-! Coinduction and universe-polymorphic resumption operations. -/

namespace CslibTests.Resumption

open PFunctor

abbrev tick : PFunctor := ⟨Unit, fun _ => Unit⟩

def ticks (seed : Nat) : Resumption tick Empty :=
  Resumption.corec (fun n => .inr ⟨(), fun _ => n + 1⟩) seed

-- An unobservable change to the seed does not change the infinite query stream.
example (m n : Nat) : ticks m = ticks n := by
  refine Resumption.bisim (fun left right =>
    ∃ m n, left = ticks m ∧ right = ticks n) ?_ ⟨m, n, rfl, rfl⟩
  rintro _ _ ⟨m, n, rfl, rfl⟩
  refine .query () (fun _ => ticks (m + 1)) (fun _ => ticks (n + 1)) ?_ ?_
    (fun _ => ⟨m + 1, n + 1, rfl, rfl⟩)
  · rw [ticks, Resumption.dest_corec]
    rfl
  · rw [ticks, Resumption.dest_corec]
    rfl

example (n : Nat) : Resumption.dest
    (Resumption.map ULift.up (Resumption.pure (p := tick) n) :
      Resumption tick (ULift.{2} Nat)) = .inl (ULift.up n) := by
  simp

end CslibTests.Resumption
