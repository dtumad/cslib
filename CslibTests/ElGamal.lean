/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.Security
import Cslib.Foundations.Control.Monad.Free
import Cslib.Foundations.Data.PFunctor.Basic
import Cslib.Foundations.Data.PFunctor.Free.Measure

/-! ElGamal with two sources of randomness: an operation selecting a uniform element of each
`Fin (k + 1)`, in a group of order three; and fair coin flips alone, in the group of order two. -/

namespace CslibTests.ElGamal

open Cslib Cslib.Crypto ElGamal PFunctor MeasureTheory ProbabilityTheory

section Selection

/-- One operation for each `k`, answered by an element of `Fin (k + 1)`. -/
abbrev Select : PFunctor := ⟨ℕ, fun k => Fin (k + 1)⟩

noncomputable abbrev uniform (k : Select.A) : Measure (Select.B k) := uniformOn Set.univ

abbrev G₃ := Multiplicative (ZMod 3)

instance : MeasurableSpace G₃ := ⊤

instance : DiscreteMeasurableSpace G₃ := ⟨fun _ => trivial⟩

-- Exponents are selected in one step, whatever the order of the group, and the challenge coin is
-- a selection from `Fin 2`.
example {State : Type} [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (choose : G₃ → Select.FreeM (G₃ × G₃ × State)) (guess : State → G₃ × G₃ → Select.FreeM Bool) :=
  cpa_advantage_eq_ddh_advantage (PFunctor.FreeM.isMeasureSemantics_toMeasure uniform)
    (PFunctor.FreeM.lift (P := Select) 2) (finTwoEquiv <$> PFunctor.FreeM.lift (P := Select) 1)
    (.ofAdd 1) choose guess (by decide) (PFunctor.FreeM.toMeasure_lift _ _) (by simp)

end Selection

/-! With fair coin flips alone, programs are written in the free monad of a coin-flip effect, whose
semantics answers each flip by the operation of `y^Bool`, distributed uniformly. Exponents are
sampled exactly in a group whose order is a power of two; other orders need rejection sampling,
as a resumption. -/

section Coin

abbrev G := Multiplicative (ZMod 2)

instance : MeasurableSpace G := ⊤

instance : DiscreteMeasurableSpace G := ⟨fun _ => trivial⟩

def g : G := .ofAdd 1

inductive Flip : Type → Type
  | flip : Flip Bool

def flip : Cslib.FreeM Flip Bool := .lift .flip

def exponent : Cslib.FreeM Flip (Fin 2) := finTwoEquiv.symm <$> flip

/-- Answer each flip by the operation of `y^Bool`. -/
def interp : {ι : Type} → Flip ι → (y^Bool).FreeM ι
  | _, .flip => PFunctor.FreeM.lift ()

noncomputable abbrev fair (a : (y^Bool).A) : Measure ((y^Bool).B a) := uniformOn Set.univ

theorem isMeasureSemantics :
    IsMeasureSemantics (Cslib.FreeM Flip) fun x => (x.liftM interp).toMeasure fair :=
  (PFunctor.FreeM.isMeasureSemantics_toMeasure fair).comp (Cslib.FreeM.isMonadHom_liftM interp)

theorem toMeasure_flip : (flip.liftM interp).toMeasure fair = uniformOn Set.univ := by
  simp [flip, interp, fair]

-- A sampler built from other operations discharges the uniformity hypothesis.
theorem toMeasure_exponent : (exponent.liftM interp).toMeasure fair = uniformOn Set.univ := by
  rw [exponent, isMeasureSemantics.map_map_of_discrete, toMeasure_flip, uniformOn_univ_map_equiv]

-- The adversary's phases are free programs, so they return almost surely.
example {State : Type} [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (choose : G → Cslib.FreeM Flip (G × G × State))
    (guess : State → G × G → Cslib.FreeM Flip Bool) :=
  cpa_advantage_eq_ddh_advantage isMeasureSemantics exponent flip g choose guess (by decide)
    toMeasure_exponent toMeasure_flip

end Coin

end CslibTests.ElGamal
