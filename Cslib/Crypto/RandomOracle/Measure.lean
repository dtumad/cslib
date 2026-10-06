/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.RandomOracle
public import Cslib.Foundations.Data.PFunctor.Free.Measure.Support

/-! # Collision bounds for a cached random oracle -/

public section

namespace Cslib.Crypto.RandomOracle

open MeasureTheory
open scoped ENNReal

variable {X Y : Type} [DecidableEq X] [MeasurableSpace X]

/-- A cache with `n` entries is hit with probability at most `n * r` when each input has
probability at most `r`. Duplicate entries do not require a separate invariant. -/
theorem measure_lookup_isSome_le (μ : Measure X) (cache : List (X × Y)) (r : ℝ≥0∞)
    (h : ∀ input, μ {input} ≤ r) :
    μ {input | (cache.lookup input).isSome} ≤ cache.length * r := by
  induction cache with
  | nil => simp
  | cons entry cache ih =>
    have hevent : {input | ((entry :: cache).lookup input).isSome} =
        {entry.1} ∪ {input | (cache.lookup input).isSome} := by
      ext input
      by_cases heq : input = entry.1 <;> simp [heq]
    rw [hevent]
    calc
      _ ≤ μ {entry.1} + μ {input | (cache.lookup input).isSome} := measure_union_le _ _
      _ ≤ r + cache.length * r := add_le_add (h _) ih
      _ = _ := by simp [add_mul, add_comm]

end Cslib.Crypto.RandomOracle
