/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Probability.UniformOn

/-! # Uniform measures and finite equivalences -/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- Independent uniform samples form a uniform pair. -/
theorem prod_uniformOn_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Finite α] [Finite β] :
    (uniformOn (Set.univ : Set α)).prod (uniformOn (Set.univ : Set β)) =
      uniformOn Set.univ := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [uniformOn_univ, Fintype.card_prod, ENNReal.mul_inv]

/-- A bijection preserves the uniform measure on a finite type. -/
theorem map_uniformOn_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Finite α] [Finite β]
    (e : α ≃ β) : (uniformOn (Set.univ : Set α)).map e = uniformOn Set.univ := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hpre : e ⁻¹' {b} = {e.symm b} := by
    ext a
    simp [Equiv.eq_symm_apply]
  rw [hpre]
  simp [uniformOn_univ, Fintype.card_congr e]

end ProbabilityTheory
