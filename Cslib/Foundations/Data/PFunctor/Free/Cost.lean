/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Truncate
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Data.ENat.Monoid

/-!
# Worst-case operation count

`queryBound` counts visible operations, taking a supremum over all responses. It can be infinite
even for a well-founded program if branches have unbounded finite lengths. It does not charge
local computation. A machine runtime certificate must additionally account for that work.
-/

@[expose] public section

namespace PFunctor.FreeM

universe uA uB uQ

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}} {α β : Type uB}

/-- The supremum of the operation counts of all execution paths. -/
noncomputable def queryBound : P.FreeM α → ℕ∞
  | .pure _ => 0
  | .liftBind _ cont => 1 + ⨆ b, queryBound (cont b)

@[simp]
theorem queryBound_pure (a : α) : queryBound (pure a : P.FreeM α) = 0 := rfl

@[simp]
theorem queryBound_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    queryBound (lift op >>= cont) = 1 + ⨆ b, queryBound (cont b) := rfl

@[simp]
theorem queryBound_lift (op : P.A) : queryBound (lift (P := P) op) = 1 := by
  change 1 + ⨆ _ : P.B op, (0 : ℕ∞) = 1
  simp

/-- Sequential composition adds worst-case bounds. -/
theorem queryBound_bind_le (x : P.FreeM α) (f : α → P.FreeM β) (bound : ℕ∞)
    (hf : ∀ a, queryBound (f a) ≤ bound) :
    queryBound (x >>= f) ≤ queryBound x + bound := by
  induction x with
  | pure a => simpa using hf a
  | lift_bind op cont ih =>
    change 1 + ⨆ b, queryBound (cont b >>= f) ≤ (1 + ⨆ b, queryBound (cont b)) + bound
    rw [add_assoc]
    gcongr
    exact iSup_le fun b => (ih b).trans
      (add_le_add (le_iSup (fun b => queryBound (cont b)) b) le_rfl)

/-- Mapping the result preserves the number of operations. -/
@[simp]
theorem queryBound_map (f : α → β) (x : P.FreeM α) :
    queryBound (f <$> x) = queryBound x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change (1 + ⨆ b, queryBound (f <$> cont b)) = 1 + ⨆ b, queryBound (cont b)
    simp only [ih]

/-- Inlining handlers charges their implementation, rather than treating them as unit-cost. -/
theorem queryBound_liftM_le (handler : (op : P.A) → Q.FreeM (P.B op))
    (bound : ℕ∞) (h : ∀ op, queryBound (handler op) ≤ bound) (x : P.FreeM α) :
    queryBound (x.liftM handler) ≤ queryBound x * bound := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind]
    calc
      _ ≤ queryBound (handler op) + (⨆ b, queryBound (cont b)) * bound :=
        queryBound_bind_le _ _ _ fun b => (ih b).trans
          (by gcongr; exact le_iSup (fun b => queryBound (cont b)) b)
      _ ≤ bound + (⨆ b, queryBound (cont b)) * bound := add_le_add (h op) le_rfl
      _ = _ := by
        change bound + (⨆ b, queryBound (cont b)) * bound =
          (1 + ⨆ b, queryBound (cont b)) * bound
        rw [add_mul, one_mul]

/-- Truncation gives a bound on every execution path, independently of the answer measures. -/
theorem queryBound_truncate (fuel : ℕ) (x : Resumption P α) :
    queryBound (Resumption.truncate fuel x) ≤ fuel := by
  induction fuel generalizing x with
  | zero =>
    rcases h : Resumption.dest x with a | node <;>
      simp [Resumption.truncate, h]
  | succ fuel ih =>
    rcases h : Resumption.dest x with a | ⟨op, cont⟩
    · simp [Resumption.truncate, h]
    · simp only [Resumption.truncate, h, queryBound, Nat.cast_add, Nat.cast_one]
      rw [add_comm (fuel : ℕ∞)]
      exact add_le_add le_rfl (iSup_le fun b => ih (cont b))

end PFunctor.FreeM
