/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.RandomOracle

set_option linter.hashCommand false

/-! A lazily sampled random oracle answers repeated queries from its cache, sampling only on a miss.
The sampler here counts its calls, so fresh samples are visible. -/

namespace CslibTests.RandomOracle

open Cslib.Crypto

/-- A sampler returning a counter, so that each fresh sample is distinct. -/
def counter : StateM ℕ ℕ := fun count => (count, count + 1)

def queries : StateT (List (Bool × ℕ)) (StateM ℕ) (ℕ × ℕ × ℕ) := do
  let first ← RandomOracle.query counter false
  let other ← RandomOracle.query counter true
  let repeated ← RandomOracle.query counter false
  pure (first, other, repeated)

-- The repeated query is answered from the cache, so only two samples are drawn.
#guard ((queries.run []).run 0).1.1 == (0, 1, 0)
#guard ((queries.run []).run 0).2 == 2

end CslibTests.RandomOracle
