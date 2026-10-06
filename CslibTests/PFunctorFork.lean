/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability

set_option linter.hashCommand false

/-! Forking selects a position adaptively, from the first run's final result, and reruns only the
continuation after it; the prefix, including private randomness, is shared. -/

open PFunctor

namespace PFunctorFork

abbrev effects : PFunctor := ⟨Bool, fun _ => ℕ⟩

/-- Answer each operation with a counter, so that fresh answers are visible. -/
def counted (_ : effects.A) : StateM ℕ ℕ := fun count => (count, count + 1)

def program : effects.FreeM (ℕ × ℕ × ℕ) := do
  let saved ← FreeM.lift false
  let first ← FreeM.lift true
  let last ← FreeM.lift true
  pure (saved, first, last)

def runFork (choose : (ℕ × ℕ × ℕ) → Option ℕ) : StateM ℕ
    ((ℕ × ℕ × ℕ) × Option (ℕ × ℕ × ℕ)) :=
  ((fun out => (out.1, out.2.map fun event => event.2.2.2)) <$>
    FreeM.fork id choose program).liftM counted

def choose (out : ℕ × ℕ × ℕ) : Option ℕ := if out.2.2 % 2 = 0 then some 1 else some 0

-- The unselected response is shared by both runs; only selected operations count toward the
-- position.
#guard ((runFork choose).run 0).run == (((0, 1, 2), some (0, 1, 3)), 4)
#guard ((runFork choose).run 1).run == (((1, 2, 3), some (1, 4, 5)), 6)

-- Missing and out-of-range selections make no further request.
#guard ((runFork (fun _ => none)).run 0).run == (((0, 1, 2), none), 3)
#guard ((runFork (fun _ => some 2)).run 0).run == (((0, 1, 2), none), 3)

def fixedTape (tape : List ℕ) : effects.FreeM (ℕ × ℕ) := do
  let challenge ← FreeM.lift true
  pure (challenge, tape.headD 0)

-- Private randomness sampled before the fork point is sampled once and shared by both runs,
-- although the program reads it afterwards.
example : FreeM.fork id (fun _ => some 0)
      ([()].mapM (fun _ => FreeM.lift false) >>= fixedTape) =
    ([()].mapM (fun _ => FreeM.lift false) >>= fun tape =>
      FreeM.fork id (fun _ => some 0) (fixedTape tape)) :=
  FreeM.fork_mapM_bind_of_not_select _ _ _ _ _ rfl

end PFunctorFork
