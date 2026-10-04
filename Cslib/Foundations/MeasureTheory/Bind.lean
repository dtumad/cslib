/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Mapping before measure bind -/

public section

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Deterministic preprocessing composes with a measurable continuation. -/
theorem bind_map (μ : Measure α) {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [← bind_dirac_eq_map μ hf]
  calc
    _ = μ.bind (fun a => (dirac (f a)).bind g) :=
      bind_bind (measurable_dirac.comp hf).aemeasurable hg.aemeasurable
    _ = _ := by simp only [dirac_bind hg, Function.comp_def]

end MeasureTheory.Measure
