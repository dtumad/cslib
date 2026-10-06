/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.Security
import Cslib.Foundations.Data.PFunctor.Resumption.Uniform

/-! ElGamal in a group of order three with two sources of randomness: an operation selecting a
uniform element of each `Fin (k + 1)`; and fair coin flips alone, from which exponents are sampled
by rejection. -/

namespace CslibTests.ElGamal

open Cslib Cslib.Crypto ElGamal PFunctor MeasureTheory ProbabilityTheory

abbrev G₃ := Multiplicative (ZMod 3)

instance : MeasurableSpace G₃ := ⊤

instance : DiscreteMeasurableSpace G₃ := ⟨fun _ => trivial⟩

section Selection

/-- One operation for each `k`, answered by an element of `Fin (k + 1)`. -/
abbrev Select : PFunctor := ⟨ℕ, fun k => Fin (k + 1)⟩

noncomputable abbrev uniform (k : Select.A) : Measure (Select.B k) := uniformOn Set.univ

-- Exponents are selected in one step, whatever the order of the group, and the challenge coin is
-- a selection from `Fin 2`.
example {State : Type} [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (choose : G₃ → Select.FreeM (G₃ × G₃ × State)) (guess : State → G₃ × G₃ → Select.FreeM Bool) :=
  cpa_advantage_eq_ddh_advantage (PFunctor.FreeM.isMeasureSemantics_toMeasure uniform)
    (PFunctor.FreeM.lift (P := Select) 2) (finTwoEquiv <$> PFunctor.FreeM.lift (P := Select) 1)
    (.ofAdd 1) choose guess (by decide) (PFunctor.FreeM.toMeasure_lift _ _) (by simp)

end Selection

section FairCoins

-- With fair coins alone, exponents are sampled exactly by rejection, a resumption, and the
-- adversary's phases are free programs of coin flips lifted into resumptions, so they return
-- almost surely.
example {State : Type} [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (choose : G₃ → coinOracle.FreeM (G₃ × G₃ × State))
    (guess : State → G₃ × G₃ → coinOracle.FreeM Bool) :=
  cpa_advantage_eq_ddh_advantage (Resumption.isMeasureSemantics_toMeasure fairCoins)
    (Resumption.uniformFin 3) (monadLift FreeM.coin) (.ofAdd 1) (fun pk => monadLift (choose pk))
    (fun state c => monadLift (guess state c)) (by decide) (Resumption.toMeasure_uniformFin 3)
    (by simp)

end FairCoins

end CslibTests.ElGamal
