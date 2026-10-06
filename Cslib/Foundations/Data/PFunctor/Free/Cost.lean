/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.State
public import Mathlib.Basic.ENNReal.Operations

/-!
# Worst-case cost of polynomial programs

Given a cost for each operation, `x.maxCost cost` is the largest total cost of the operations
performed along any path of `x`, whatever their responses. It bounds the expected cost under any
answers to the operations that are at most probabilities
(`PFunctor.Resumption.expectedCost_toResumption_le`).
-/

@[expose] public section

open scoped ENNReal

universe uA uB uS u v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type u} {β : Type v} (cost : P.A → ℝ≥0∞)

/-- The largest total cost of the operations performed along any path of `x`. -/
noncomputable def maxCost (x : P.FreeM α) (cost : P.A → ℝ≥0∞) : ℝ≥0∞ :=
  x.foldFreeM (fun _ => 0) fun a k => cost a + ⨆ b, k b

@[simp]
theorem maxCost_pure (a : α) : (pure a : P.FreeM α).maxCost cost = 0 := rfl

@[simp]
theorem maxCost_lift_bind (a : P.A) (k : P.B a → P.FreeM α) :
    ((lift a).bind (α := no_index (P.B a)) k).maxCost cost = cost a + ⨆ b, (k b).maxCost cost :=
  rfl

@[simp]
theorem maxCost_lift_bind' {α : Type uB} (a : P.A) (k : P.B a → P.FreeM α) :
    (Bind.bind (α := no_index (P.B a)) (lift a) k).maxCost cost =
      cost a + ⨆ b, (k b).maxCost cost :=
  rfl

@[simp]
theorem maxCost_lift (a : P.A) : maxCost (α := no_index (P.B a)) (lift a) cost = cost a := by
  simpa using maxCost_lift_bind cost a pure

theorem maxCost_bind_le (x : P.FreeM α) (f : α → P.FreeM β) :
    (x.bind f).maxCost cost ≤ x.maxCost cost + ⨆ a, (f a).maxCost cost := by
  induction x with
  | pure a => simpa using le_iSup (fun a => (f a).maxCost cost) a
  | lift_bind a k ih =>
    simpa [add_assoc] using add_le_add_right (iSup_le fun b => (ih b).trans
      (add_le_add_left (le_iSup (fun b => (k b).maxCost cost) b) _)) (cost a)

@[simp]
theorem maxCost_map (f : α → β) (x : P.FreeM α) : (x.map f).maxCost cost = x.maxCost cost := by
  induction x <;> simp [*]

@[simp]
theorem maxCost_map' {α β : Type u} (f : α → β) (x : P.FreeM α) :
    (f <$> x).maxCost cost = x.maxCost cost :=
  maxCost_map cost f x

/-- Threading a state through the operations does not change their costs along any path. -/
theorem maxCost_withState_le {S : Type uS} (x : P.FreeM α) (s : S) :
    (x.withState s).maxCost (fun a => cost a.1) ≤ x.maxCost cost := by
  induction x generalizing s with
  | pure a => simp
  | lift_bind a k ih =>
    simpa using add_le_add_right (iSup_le fun b : P.B a × S =>
      (ih b.1 b.2).trans (le_iSup (fun b => (k b).maxCost cost) b.1)) (cost a)

end PFunctor.FreeM
