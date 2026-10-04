/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.Oracle
import CslibTests.PFunctorProbability
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! These examples check native measure semantics, dependent sampling operations, and the
encryption-oracle reduction for a small cyclic group. The group is an API test, not a security
assumption or an efficient implementation of ElGamal. -/

open Cslib.Crypto PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctorCrypto

abbrev G := Multiplicative (ZMod 3)

instance : MeasurableSpace G := ⊤
instance : MeasurableSingletonClass G := ⟨fun _ => trivial⟩

def generator : G := Multiplicative.ofAdd 1

theorem generator_bijective : Function.Bijective (fun x : Fin 3 => generator ^ x.val) := by
  decide

abbrev randomness : PFunctor := ⟨Bool, fun | false => Fin 3 | true => Bool⟩

instance (op : randomness.A) : MeasurableSpace (randomness.B op) := by
  cases op <;> infer_instance

instance (op : randomness.A) : DiscreteMeasurableSpace (randomness.B op) := by
  cases op <;> infer_instance

noncomputable def answers : (op : randomness.A) → Measure (randomness.B op)
  | false => uniformOn Set.univ
  | true => uniformOn Set.univ

instance (op : randomness.A) : IsProbabilityMeasure (answers op) := by
  cases op <;> unfold answers <;> infer_instance

def sample : randomness.FreeM (Fin 3) := FreeM.lift (P := randomness) false
def coin : randomness.FreeM Bool := FreeM.lift (P := randomness) true

def challengeBit : PFunctorProbability.four.FreeM Bool :=
  FreeM.map (fun x : Fin 4 => decide (x.val < 2)) (FreeM.lift ())

theorem challengeBit_uniform :
    FreeM.denote PFunctorProbability.answers challengeBit = uniformOn Set.univ := by
  classical
  rw [challengeBit, FreeM.denote_map (P := PFunctorProbability.four)
    PFunctorProbability.answers _ _ Measurable.of_discrete]
  rw [FreeM.denote_lift (P := PFunctorProbability.four)]
  apply Measure.ext_of_singleton
  intro bit
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hfiber : (fun x : Fin 4 => decide (x.val < 2)) ⁻¹' {bit} =
      if bit then {0, 1} else {2, 3} := by
    ext x
    fin_cases x <;> cases bit <;> norm_num
  rw [hfiber, uniformOn_univ (Ω := Bool), Measure.count_singleton]
  cases bit <;> norm_num [PFunctorProbability.answers, uniformOn_univ, Measure.count_apply,
    Set.encard_insert_of_notMem, Set.encard_singleton]
  all_goals
    change ((2 : NNReal) : ℝ≥0∞) / ((4 : NNReal) : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_inv (by norm_num)]
    norm_num

/-- Each exponent request uses exact rejection sampling; challenge bits use a fresh draw. -/
def concreteHandler : (op : randomness.A) →
    Resumption PFunctorProbability.four (randomness.B op)
  | false => PFunctorProbability.sample
  | true => challengeBit.toResumption

theorem concreteHandler_correct (op : randomness.A) :
    Resumption.returnedMeasure PFunctorProbability.answers (concreteHandler op) = answers op := by
  cases op with
  | false => exact PFunctorProbability.returned_uniform
  | true =>
    change Resumption.returnedMeasure _ challengeBit.toResumption = _
    rw [Resumption.returnedMeasure_toResumption (P := PFunctorProbability.four)]
    exact challengeBit_uniform

-- The actual experiment below runs rejection samplers, including their infinite rejected paths.
example
    (choose : G → (randomness + PFunctor.mk G (fun _ => G × G)).FreeM (G × G × ℕ))
    (guess : ℕ → G × G → (randomness + PFunctor.mk G (fun _ => G × G)).FreeM Bool) :
    |Game.winProbability (Resumption.returnedMeasure PFunctorProbability.answers
        ((ElGamal.cpaOracleExperiment sample coin generator choose guess).liftM concreteHandler)) -
          1 / 2| =
      Game.advantage
        (Resumption.returnedMeasure PFunctorProbability.answers
          ((ElGamal.ddhReal sample generator
            (ElGamal.ddhOracleReduction sample coin generator choose guess)).liftM concreteHandler))
        (Resumption.returnedMeasure PFunctorProbability.answers
          ((ElGamal.ddhRandom sample generator
            (ElGamal.ddhOracleReduction sample coin generator choose guess)).liftM
              concreteHandler)) := by
  have hhandler : (fun op => Resumption.returnedMeasure
      PFunctorProbability.answers (concreteHandler op)) = answers := by
    funext op
    exact concreteHandler_correct op
  simp only [Resumption.returnedMeasure_liftM, hhandler]
  exact ElGamal.advantage_oracle_eq_ddh sample coin generator choose guess answers
    generator_bijective (FreeM.denote_lift (P := randomness) answers false)
      (FreeM.denote_lift (P := randomness) answers true)

-- Losing half the mass does not turn complement into `1 - p`.
example : Game.winProbability
    (((1 / 2 : ℝ≥0∞) • Measure.dirac true).map Bool.not) = 0 := by
  rw [Game.winProbability,
    map_measureReal_apply Measurable.of_discrete (measurableSet_singleton _)]
  simp [measureReal_def]

example : Game.advantage ((1 / 2 : ℝ≥0∞) • Measure.dirac true) (Measure.dirac false) = 1 / 2 := by
  simp [Game.winProbability, measureReal_def]

end PFunctorCrypto
