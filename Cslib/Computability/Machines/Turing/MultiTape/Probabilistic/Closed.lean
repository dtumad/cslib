/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure

/-! # Closed fair-coin programs -/

@[expose] public section

namespace Turing.MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory

variable [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]

/-- The probability interpretation of private coins with no external oracle operations. -/
noncomputable def coinMeasure (op : (effects Empty).A) : Measure ((effects Empty).B op) :=
  match op with
  | .inl _ => uniformOn Set.univ
  | .inr (port, _) => port.elim

instance (op : (effects Empty).A) : IsProbabilityMeasure (coinMeasure op) := by
  cases op with
  | inl _ => exact inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set Bool)))
  | inr request => exact request.1.elim

omit [DiscreteMeasurableSpace (List Bool)] in
@[simp] theorem denote_coin : FreeM.denote coinMeasure coin = uniformOn Set.univ :=
  FreeM.denote_lift coinMeasure (.inl ())

/-- The numerical binary sampler uses the same uniform bit as the machine transition. -/
theorem denote_finTwo_coin :
    FreeM.denote coinMeasure
      ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin) = uniformOn Set.univ := by
  rw [← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete, denote_coin]
  exact map_uniformOn_univ (Equiv.ofBijective
    (fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) (by decide))

end Turing.MultiTapePTM
