/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Resumption.Truncate
public import Cslib.Foundations.MeasureTheory.Monotone

/-!
# Returned values of possibly infinite computations

`outputMeasure μ k x` observes returns after at most `k` operations. Its increasing supremum
`returnedMeasure μ x` records nontermination as missing mass. Almost-sure termination is exactly
`IsProbabilityMeasure (returnedMeasure μ x)` when the operations are lossless.

This extends VCVio's finite-fuel semantics. Agreement with `FreeM` needs no uniform bound on
branch depth: well-founded, infinitely branching programs are included.
-/

@[expose] public section

open MeasureTheory

universe uA uB v

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  {α : Type v} [MeasurableSpace α]

/-- The measure of values returned within the given number of operations. Returns cost no fuel. -/
noncomputable def outputMeasure (μ : (op : P.A) → Measure (P.B op)) :
    ℕ → Resumption P α → Measure α
  | 0, x => match dest x with
    | .inl a => Measure.dirac a
    | .inr _ => 0
  | k + 1, x => match dest x with
    | .inl a => Measure.dirac a
    | .inr ⟨op, cont⟩ => (μ op).bind fun b => outputMeasure μ k (cont b)

variable (μ : (op : P.A) → Measure (P.B op))

@[simp]
theorem outputMeasure_pure (k : ℕ) (a : α) :
    outputMeasure μ k (pure a) = Measure.dirac a := by cases k <;> rfl

@[simp]
theorem outputMeasure_query_zero (op : P.A) (cont : P.B op → Resumption P α) :
    outputMeasure μ 0 (query op cont) = 0 := rfl

@[simp]
theorem outputMeasure_query_succ (k : ℕ) (op : P.A) (cont : P.B op → Resumption P α) :
    outputMeasure μ (k + 1) (query op cont) =
      (μ op).bind fun b => outputMeasure μ k (cont b) := rfl

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

/-- More fuel can only increase the measure of returned values. -/
theorem outputMeasure_le_succ (k : ℕ) (x : Resumption P α) :
    outputMeasure μ k x ≤ outputMeasure μ (k + 1) x := by
  induction k generalizing x with
  | zero =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      exact bot_le
  | succ k ih =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      exact Measure.bind_mono_right Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable (Filter.Eventually.of_forall fun b => ih (cont b))

theorem monotone_outputMeasure (x : Resumption P α) : Monotone (outputMeasure μ · x) :=
  monotone_nat_of_le_succ fun k => outputMeasure_le_succ μ k x

/-- The measure of all returned values, with divergence represented by missing mass. -/
noncomputable def returnedMeasure (x : Resumption P α) : Measure α :=
  ⨆ k, outputMeasure μ k x

theorem returnedMeasure_apply (x : Resumption P α) (s : Set α) (hs : MeasurableSet s) :
    returnedMeasure μ x s = ⨆ k, outputMeasure μ k x s :=
  Measure.iSup_apply_of_monotone _ (monotone_outputMeasure μ x) s hs

omit [∀ op, DiscreteMeasurableSpace (P.B op)] in
@[simp]
theorem returnedMeasure_pure (a : α) : returnedMeasure μ (pure a) = Measure.dirac a := by
  simp [returnedMeasure]

/-- Unfolding one operation commutes with the returned-output limit. -/
theorem returnedMeasure_query (op : P.A) (cont : P.B op → Resumption P α) :
    returnedMeasure μ (query op cont) = (μ op).bind fun b => returnedMeasure μ (cont b) := by
  rw [returnedMeasure, ← (monotone_outputMeasure μ (query op cont)).iSup_nat_add 1]
  simp only [outputMeasure_query_succ, returnedMeasure]
  exact (Measure.bind_iSup_of_monotone (fun _ => Measurable.of_discrete.aemeasurable)
    Measurable.of_discrete.aemeasurable (fun b => monotone_outputMeasure μ (cont b))).symm

/-- Every finite approximation is a subprobability measure when operations are lossless. -/
theorem outputMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)]
    (k : ℕ) (x : Resumption P α) : outputMeasure μ k x Set.univ ≤ 1 := by
  induction k generalizing x with
  | zero =>
    rcases hx : dest x with a | node <;> simp [outputMeasure, hx]
  | succ k ih =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
      calc
        _ ≤ ∫⁻ _b, 1 ∂μ op := lintegral_mono fun b => ih (cont b)
        _ = 1 := by simp

theorem returnedMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)]
    (x : Resumption P α) : returnedMeasure μ x Set.univ ≤ 1 := by
  rw [returnedMeasure_apply μ x Set.univ MeasurableSet.univ]
  exact iSup_le fun k => outputMeasure_apply_univ_le_one μ k x

/-- Every well-founded free program has exactly its original denotation in the resumption model. -/
@[simp]
theorem returnedMeasure_toResumption (x : P.FreeM α) :
    returnedMeasure μ x.toResumption = FreeM.denote μ x := by
  induction x with
  | pure a => exact returnedMeasure_pure μ a
  | lift_bind op cont ih =>
    change returnedMeasure μ (query op (fun b => (cont b).toResumption)) = _
    rw [returnedMeasure_query, FreeM.denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

end PFunctor.Resumption
