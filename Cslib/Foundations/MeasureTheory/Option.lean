/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable optional values

The coproduct measurable structure on `Option α` treats `none` as a separate measurable point.
Adapted from VCVio's `ToMathlib.MeasureTheory.MeasurableSpace.Option`.
-/

@[expose] public section

namespace Option

variable {α β : Type*} [MeasurableSpace α]

instance instMeasurableSpace : MeasurableSpace (Option α) :=
  (inferInstance : MeasurableSpace α).map some ⊓
    (⊤ : MeasurableSpace Unit).map fun _ => none

@[fun_prop]
theorem measurable_some : Measurable (@some α) := Measurable.of_le_map inf_le_left

/-- Measurability of an optional event is determined by its successful branch. -/
theorem measurableSet_option_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (some ⁻¹' s) := by
  change MeasurableSet (some ⁻¹' s) ∧
    MeasurableSet ((fun _ : Unit => (none : Option α)) ⁻¹' s) ↔ _
  simp

@[simp]
theorem measurableSet_some_image {s : Set α} :
    MeasurableSet (some '' s : Set (Option α)) ↔ MeasurableSet s := by
  rw [measurableSet_option_iff, Set.preimage_image_eq s (Option.some_injective α)]

/-- `some` embeds the original measurable space as the successful outcomes. -/
theorem measurableEmbedding_some : MeasurableEmbedding (@some α) where
  injective := Option.some_injective α
  measurable := measurable_some
  measurableSet_image' _ hs := measurableSet_some_image.mpr hs

@[simp]
theorem measurableSet_none : MeasurableSet ({none} : Set (Option α)) := by
  rw [measurableSet_option_iff]
  simp only [Set.preimage, Set.mem_singleton_iff, reduceCtorEq, Set.ofPred_false,
    MeasurableSet.empty]

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton value := by
    cases value with
    | none => exact measurableSet_none
    | some a => simpa using measurableSet_some_image.mpr (measurableSet_singleton a)

/-- A measurable success branch and a fixed failure value give a measurable eliminator. -/
@[fun_prop]
theorem measurable_elim [MeasurableSpace β] (b : β) {f : α → β} (hf : Measurable f) :
    Measurable (fun x : Option α => x.elim b f) := by
  intro s hs
  rw [measurableSet_option_iff]
  exact hf hs

@[fun_prop]
theorem measurable_map [MeasurableSpace β] {f : α → β} (hf : Measurable f) :
    Measurable (Option.map f) :=
  measurable_elim none (measurable_some.comp hf)

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Option α) where
  forall_measurableSet _ := measurableSet_option_iff.mpr MeasurableSet.of_discrete

end Option
