/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.DiscreteLog
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Mathlib.Probability.UniformOn

/-! # Success of a fixed discrete-logarithm guess -/

public section

namespace Cslib.Crypto.DiscreteLog

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A fixed scalar guesses exactly one of the uniformly sampled secrets. -/
theorem denote_experiment_const {P : PFunctor.{0, 0}} {F G : Type}
    [SMul F G] [DecidableEq G] [Finite F]
    [MeasurableSpace F] [MeasurableSingletonClass F]
    [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
    (μ : (op : P.A) → Measure (P.B op)) (sample : P.FreeM F) (g : G) (guess : F)
    (hg : Function.Injective (fun secret : F => secret • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ (experiment sample g (fun _ => pure (some guess))) {true} =
      (Nat.card F : ℝ≥0∞)⁻¹ := by
  let := Fintype.ofFinite F
  simp only [experiment, pure_bind, Option.any_some]
  rw [← map_eq_pure_bind, ← FreeM.map_eq_map,
    FreeM.denote_map _ _ _ Measurable.of_discrete, hsample,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hset : (fun secret : F => decide (guess • g = secret • g)) ⁻¹' {true} = {guess} := by
    ext secret
    simp [hg.eq_iff, eq_comm]
  rw [hset]
  simp [uniformOn_univ, Nat.card_eq_fintype_card]

end Cslib.Crypto.DiscreteLog
