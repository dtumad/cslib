/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.RandomOracle
public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered

/-! # Sampling costs of cached random-oracle queries -/

public section

namespace Cslib.Crypto.RandomOracle

open PFunctor

variable {P : PFunctor.{0, 0}} {X Y : Type} [DecidableEq X]

/-- A cache hit is free; a miss runs the sampler exactly once. -/
theorem queryBoundP_query_le (select : P.A → Bool) (sample : P.FreeM Y)
    (input : X) (cache : List (X × Y)) :
    FreeM.queryBoundP select (query sample input cache) ≤ FreeM.queryBoundP select sample := by
  cases hx : cache.lookup input with
  | some answer => simp [query, hx]
  | none =>
    simp only [query, hx, ← map_eq_pure_bind, FreeM.queryBoundP_map, le_refl]

end Cslib.Crypto.RandomOracle
