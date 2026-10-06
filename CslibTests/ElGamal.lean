/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.Coins

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

/-- Groups of order three at every security parameter, without sampling. -/
def groups : GroupGen Select.FreeM where
  Desc := Unit
  Elem _ := G₃
  order _ := 3
  gen _ := .ofAdd 1
  bijective_pow _ := by decide
  setup _ := pure ()

/-- Select an element of each `Fin k` in one step. -/
def uniformSelect (k : ℕ+) : Select.FreeM (Fin k) :=
  finCongr k.natPred_add_one <$> PFunctor.FreeM.lift (P := Select) k.natPred

def coinSelect : Select.FreeM Bool := finTwoEquiv <$> PFunctor.FreeM.lift (P := Select) 1

-- Adversaries selecting their coins have the advantage of their reductions at every security
-- parameter, so ElGamal is secure against all of them if DDH is hard against all distinguishers.
example (A : (ElGamal.scheme groups uniformSelect).EavAdversary Select.FreeM) (n : ℕ) :=
  ElGamal.eavAdvantage_eq_ddhAdvantage coinSelect
    (PFunctor.FreeM.isMeasureSemantics_toMeasure uniform) (by simp [uniformSelect])
    (by simp [coinSelect]) A n

example (h : groups.DDHHard (·.toMeasure uniform) uniformSelect fun _ => True) :
    (ElGamal.scheme groups uniformSelect).EavSecure (·.toMeasure uniform) coinSelect
      fun _ => True :=
  ElGamal.eavSecure_of_ddhHard coinSelect (PFunctor.FreeM.isMeasureSemantics_toMeasure uniform)
    (by simp [uniformSelect]) (by simp [coinSelect]) (fun _ _ => trivial) h

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

/-- Groups of order three at every security parameter, described without flipping coins. -/
def coinGroups : GroupGen coinOracle.FreeM where
  Desc := Unit
  Elem _ := G₃
  order _ := 3
  gen _ := .ofAdd 1
  bijective_pow _ := by decide
  setup _ := pure ()

-- Asymptotically, every hypothesis holds over fair coins alone.
example (A : (ElGamal.scheme coinGroups Resumption.uniformFin).EavAdversary coinOracle.FreeM)
    (n : ℕ) :=
  ElGamal.eavAdvantage_eq_ddhAdvantage_coins coinGroups A n

end FairCoins

end CslibTests.ElGamal
