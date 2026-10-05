/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Measure
public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Probability semantics of finite truncation

Truncation returns `none` when its operation budget runs out. Pulling its measure back along
`some` gives precisely the finite returned-output measure, without normalizing successful runs.
-/

public section

open MeasureTheory

namespace PFunctor.Resumption

universe uA uB v

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  [∀ op, DiscreteMeasurableSpace (P.B op)] {α : Type v} [MeasurableSpace α]
  (μ : (op : P.A) → Measure (P.B op))

/-- Successful events in a finite truncation have exactly their finite returned-output mass. -/
theorem denote_truncate_some (k : ℕ) (x : Resumption P α) (s : Set α) (hs : MeasurableSet s) :
    FreeM.denote μ (truncate k x) (some '' s) = outputMeasure μ k x s := by
  classical
  have hs' := Option.measurableSet_some_image.mpr hs
  induction k generalizing x with
  | zero =>
    rcases hx : dest x with a | ⟨op, cont⟩ <;>
      simp [truncate, outputMeasure, hx, Measure.dirac_apply' _ hs',
        Measure.dirac_apply' _ hs, Set.indicator]
  | succ k ih =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [truncate, outputMeasure, hx, Measure.dirac_apply' _ hs',
        Measure.dirac_apply' _ hs, Set.indicator]
    · simp only [truncate, outputMeasure, hx]
      change FreeM.denote μ ((FreeM.lift op).bind (fun b => truncate k (cont b))) (some '' s) = _
      rw [FreeM.denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hs' Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
      exact lintegral_congr fun b => ih (cont b)

/-- Discarding the timeout outcome uses the standard measure pullback along `some`. -/
theorem comap_denote_truncate (k : ℕ) (x : Resumption P α) :
    (FreeM.denote μ (truncate k x)).comap some = outputMeasure μ k x := by
  ext s hs
  rw [Option.measurableEmbedding_some.comap_apply, denote_truncate_some μ k x s hs]

/-- With lossless operations, timeout accounts for exactly the mass not yet returned. -/
theorem denote_truncate_none [∀ op, IsProbabilityMeasure (μ op)]
    (k : ℕ) (x : Resumption P α) :
    FreeM.denote μ (truncate k x) {none} = 1 - outputMeasure μ k x Set.univ := by
  have hset : ({none} : Set (Option α)) = (some '' Set.univ)ᶜ := by
    ext a
    cases a <;> simp
  rw [hset, measure_compl (Option.measurableSet_some_image.mpr MeasurableSet.univ)
    (measure_ne_top _ _), measure_univ, denote_truncate_some μ k x Set.univ MeasurableSet.univ]

end PFunctor.Resumption
