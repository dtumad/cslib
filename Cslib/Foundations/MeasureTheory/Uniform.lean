/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.UniformOn

/-!
# Sampling uniformly from a finite type

Composing with a bijection does not change what is sampled uniformly
(`uniformOn_univ_map_equiv`, `uniformOn_univ_bind_equiv`), and comparing a fair bit with an
independent guess gives a fair bit (`uniformOn_univ_bind_map_beq`). These are the steps by which a
secret drawn uniformly hides a message, as in one-time pads and hidden-bit games.

Independent uniform components form a uniform pair (`uniformOn_univ_bind_map_prodMk`), and the
uniform measure conditioned on a set is uniform on it (`uniformOn_univ_cond`), as is its image
under a map that is bijective from the set onto the whole type (`uniformOn_map_of_bijOn`). These
are the steps by which fair coins and rejection sample uniformly.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Sampling uniformly and applying a bijection samples uniformly. -/
theorem uniformOn_univ_bind_equiv [Finite α] [Finite β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (e : α ≃ β) (f : β → Measure γ) :
    (uniformOn Set.univ : Measure α).bind (fun a => f (e a)) =
      (uniformOn Set.univ : Measure β).bind f := by
  have := Fintype.ofFinite α; have := Fintype.ofFinite β
  ext s hs
  simp [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype,
    uniformOn_univ, Fintype.card_congr e, ← e.sum_comp]

/-- A bijection pushes the uniform measure forward to the uniform measure. -/
@[simp]
theorem uniformOn_univ_map_equiv [Finite α] [Finite β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformOn Set.univ : Measure α).map e = uniformOn Set.univ := by
  rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  exact (uniformOn_univ_bind_equiv e _).trans Measure.bind_dirac

/-- Sampling two components independently and uniformly samples a pair uniformly. -/
theorem uniformOn_univ_bind_map_prodMk [Finite α] [Finite β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] :
    (uniformOn Set.univ : Measure α).bind (fun a => (uniformOn Set.univ : Measure β).map (a, ·)) =
      uniformOn Set.univ := by
  have := Fintype.ofFinite α; have := Fintype.ofFinite β
  classical
  refine Measure.ext_of_singleton fun ⟨a, b⟩ => ?_
  have hpre (x : α) : Prod.mk x ⁻¹' {(a, b)} = if x = a then {b} else ∅ := by
    ext; split_ifs <;> simp [*]
  rw [Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable,
    lintegral_fintype, Finset.sum_eq_single a (fun x _ hx => by
      simp [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _), hpre, hx])
      (by simp)]
  simp [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _), hpre, uniformOn_univ,
    ENNReal.mul_inv, mul_comm]

/-- Conditioning the uniform measure on a set gives the uniform measure on the set. -/
theorem uniformOn_univ_cond [Finite α] [MeasurableSingletonClass α] (s : Set α) :
    (uniformOn Set.univ : Measure α)[|s] = uniformOn s := by
  rw [uniformOn, uniformOn, cond_cond_eq_cond_inter' .univ s.toFinite.measurableSet
    (by simp [Measure.count_apply_finite]), Set.univ_inter]

/-- A map from a set onto the whole type, bijective on the set, pushes the uniform measure on the
set forward to the uniform measure. -/
theorem uniformOn_map_of_bijOn [Finite α] [Finite β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] {s : Set α} {f : α → β} (hf : Set.BijOn f s Set.univ) :
    (uniformOn s).map f = uniformOn Set.univ := by
  refine Measure.ext_of_singleton fun b => ?_
  obtain ⟨a, ha, rfl⟩ := hf.surjOn (Set.mem_univ b)
  have hfiber : s ∩ f ⁻¹' {f a} = {a} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨⟨ha, rfl⟩, fun x hx => hf.injOn hx.1 ha hx.2⟩
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), uniformOn, uniformOn,
    cond_apply .of_discrete, cond_apply .of_discrete, hfiber, Set.univ_inter,
    Measure.count_apply .of_discrete, Measure.count_apply .of_discrete,
    Set.encard_congr hf.equiv]
  simp [Measure.count_apply]

/-- Whether a fair bit equals an independent guess is a fair bit. -/
theorem uniformOn_univ_bind_map_beq (ν : Measure Bool) [IsProbabilityMeasure ν] :
    (uniformOn Set.univ : Measure Bool).bind (fun a => ν.map (a == ·)) = uniformOn Set.univ := by
  have (b : Bool) : (uniformOn Set.univ : Measure Bool).bind (fun a => .dirac (a == b)) =
      uniformOn Set.univ :=
    (uniformOn_univ_bind_equiv (Equiv.ofBijective (· == b) (by cases b <;> decide)) _).trans
      Measure.bind_dirac
  simp_rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [Measure.bind_comm Measurable.of_discrete]
  simp only [this, Measure.bind_const, measure_univ, one_smul]

end ProbabilityTheory
