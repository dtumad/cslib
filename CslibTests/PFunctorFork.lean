/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Fork.Measure
import Cslib.Crypto.RandomOracle

set_option linter.hashCommand false

/-! Adaptive selection uses the first run's final response. Replay retains the prefix,
including a cache inlined through `StateT`, and only reruns the selected suffix. -/

open PFunctor Cslib.Crypto

namespace PFunctorFork

abbrev effects : PFunctor := ⟨Bool, fun _ => ℕ⟩

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

-- The saved ambient response survives either fork. Only hash operations count toward the index.
#guard ((runFork choose).run 0).run == (((0, 1, 2), some (0, 1, 3)), 4)
#guard ((runFork choose).run 1).run == (((1, 2, 3), some (1, 4, 5)), 6)

-- Missing and out-of-range selections consume no additional randomness.
#guard ((runFork (fun _ => none)).run 0).run == (((0, 1, 2), none), 3)
#guard ((runFork (fun _ => some 2)).run 0).run == (((0, 1, 2), none), 3)

def cached : effects.FreeM ((ℕ × ℕ × ℕ) × List (Bool × ℕ)) :=
  (do
    let saved ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) false
    let fresh ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) true
    let repeated ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) false
    pure (saved, fresh, repeated) : StateT (List (Bool × ℕ)) effects.FreeM (ℕ × ℕ × ℕ)).run []

def forkedCache : StateM ℕ
    (((ℕ × ℕ × ℕ) × List (Bool × ℕ)) × Option ((ℕ × ℕ × ℕ) × List (Bool × ℕ))) :=
  ((fun out => (out.1, out.2.map fun event => event.2.2.2)) <$>
    FreeM.fork id (fun _ => some 1) cached).liftM counted

-- Each branch has its own fresh entry; both retain and reuse the saved entry without a new draw.
#guard (forkedCache.run 0).run ==
  ((((0, 1, 0), [(true, 1), (false, 0)]), some ((0, 2, 0), [(true, 2), (false, 0)])), 3)

end PFunctorFork
