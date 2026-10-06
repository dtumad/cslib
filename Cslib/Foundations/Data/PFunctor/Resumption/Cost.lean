/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Foundations.Data.PFunctor.Resumption.Measure

/-!
# Expected cost of resumptions

Given a cost for each operation and a measure `μ a` on the responses of each operation `a`, the
expected cost `r.expectedCost μ cost` of a resumption is the supremum of the expected costs
`approxCost μ cost n r` of the operations it performs within `n` steps. Runs that never return
contribute the cost of all of their operations, so the expected cost may be infinite.

When each `μ a` has mass at most one, the expected cost of a free program is at most the largest
cost along any of its paths (`expectedCost_toResumption_le`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe uA uB u

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)] {α : Type u}
  (μ : (a : P.A) → Measure (P.B a)) (cost : P.A → ℝ≥0∞)

/-- The expected cost of the operations a resumption performs within `n` steps, each operation `a`
answered according to `μ a`. -/
noncomputable def approxCost : ℕ → Resumption P α → ℝ≥0∞
  | 0, _ => 0
  | n + 1, r => (dest r).elim (fun _ => 0)
    fun x => cost x.fst + ∫⁻ b, approxCost n (x.snd b) ∂μ x.fst

@[simp]
theorem approxCost_zero (r : Resumption P α) : approxCost μ cost 0 r = 0 := rfl

@[simp]
theorem approxCost_pure (n : ℕ) (a : α) : approxCost μ cost n (pure a : Resumption P α) = 0 := by
  cases n <;> simp [approxCost]

@[simp]
theorem approxCost_succ_lift_bind (n : ℕ) (a : P.A) (k : P.B a → Resumption P α) :
    approxCost μ cost (n + 1) ((lift a).bind (α := no_index (P.B a)) k) =
      cost a + ∫⁻ b, approxCost μ cost n (k b) ∂μ a := by
  simp [approxCost]

@[simp]
theorem approxCost_succ_lift_bind' {α : Type uB} (n : ℕ) (a : P.A)
    (k : P.B a → Resumption P α) :
    approxCost μ cost (n + 1) (Bind.bind (α := no_index (P.B a)) (lift a) k) =
      cost a + ∫⁻ b, approxCost μ cost n (k b) ∂μ a :=
  approxCost_succ_lift_bind μ cost n a k

/-- The expected cost of the operations of `r`, each operation `a` answered according to `μ a`. -/
noncomputable def expectedCost (r : Resumption P α) (μ : (a : P.A) → Measure (P.B a))
    (cost : P.A → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ n, approxCost μ cost n r

@[simp]
theorem expectedCost_pure (a : α) : (pure a : Resumption P α).expectedCost μ cost = 0 := by
  simp [expectedCost]

theorem monotone_approxCost (r : Resumption P α) : Monotone (approxCost μ cost · r) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    cases r with
    | pure a => simp
    | lift_bind a k => simpa using add_le_add_right (lintegral_mono fun b => ih (k b)) (cost a)

theorem expectedCost_lift_bind [∀ a, DiscreteMeasurableSpace (P.B a)] (a : P.A)
    (k : P.B a → Resumption P α) :
    ((lift a).bind (α := no_index (P.B a)) k).expectedCost μ cost =
      cost a + ∫⁻ b, (k b).expectedCost μ cost ∂μ a := by
  rw [expectedCost, ← (monotone_approxCost μ cost _).iSup_nat_add 1]
  simp_rw [approxCost_succ_lift_bind, ← ENNReal.add_iSup, expectedCost]
  rw [lintegral_iSup (fun _ => .of_discrete) fun _ _ h b => monotone_approxCost μ cost (k b) h]

theorem expectedCost_lift_bind' [∀ a, DiscreteMeasurableSpace (P.B a)] {α : Type uB} (a : P.A)
    (k : P.B a → Resumption P α) :
    (Bind.bind (α := no_index (P.B a)) (lift a) k).expectedCost μ cost =
      cost a + ∫⁻ b, (k b).expectedCost μ cost ∂μ a :=
  expectedCost_lift_bind μ cost a k

/-- With responses of mass at most one, the expected cost of a free program is at most the largest
cost along any of its paths. -/
theorem expectedCost_toResumption_le (hμ : ∀ a, μ a Set.univ ≤ 1) (x : P.FreeM α) :
    x.toResumption.expectedCost μ cost ≤ x.maxCost cost := by
  refine iSup_le fun n => ?_
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    induction x with
    | pure a => simp
    | lift_bind a k _ =>
      simp only [FreeM.toResumption_lift_bind, approxCost_succ_lift_bind, FreeM.maxCost_lift_bind]
      refine add_le_add_right ((lintegral_mono fun b => (ih (k b)).trans
        (le_iSup (fun b => (k b).maxCost cost) b)).trans ?_) (cost a)
      rw [lintegral_const]
      exact mul_le_of_le_one_right' (hμ a)

end PFunctor.Resumption
