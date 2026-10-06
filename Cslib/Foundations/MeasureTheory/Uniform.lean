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
