/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Measurable dependent sums -/

public section

namespace Sigma

variable {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)]

/-- A set in a dependent sum is measurable precisely when each fiber is measurable. -/
theorem measurableSet_iff {s : Set (Sigma β)} :
    MeasurableSet s ↔ ∀ a, MeasurableSet (Sigma.mk a ⁻¹' s) :=
  MeasurableSpace.measurableSet_iInf

instance [∀ a, MeasurableSingletonClass (β a)] : MeasurableSingletonClass (Sigma β) where
  measurableSet_singleton x := by
    rw [measurableSet_iff]
    intro a
    rcases x with ⟨b, value⟩
    by_cases h : a = b
    · subst b
      have hpre : Sigma.mk a ⁻¹' {Sigma.mk a value} = {value} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => by cases h; rfl, congrArg (Sigma.mk a)⟩
      rw [hpre]
      exact measurableSet_singleton value
    · have hempty : Sigma.mk a ⁻¹' {Sigma.mk b value} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun heq => h (congrArg Sigma.fst heq)
      rw [hempty]
      exact MeasurableSet.empty

instance [∀ a, DiscreteMeasurableSpace (β a)] : DiscreteMeasurableSpace (Sigma β) where
  forall_measurableSet _ := measurableSet_iff.mpr fun _ => MeasurableSet.of_discrete

end Sigma
