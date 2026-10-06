/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.Schnorr.Extraction
import Cslib.Foundations.Data.PFunctor.Resumption.Uniform
import Mathlib.Algebra.Field.ZMod

/-! Schnorr identification over the field with three elements, with fair coins alone: scalars are
sampled exactly by rejection, and the prover is a free program of coin flips lifted into
resumptions. -/

namespace CslibTests.Schnorr

open Cslib Cslib.Crypto Schnorr PFunctor MeasureTheory ProbabilityTheory

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

instance : MeasurableSpace (ZMod 3) := ⊤

instance : DiscreteMeasurableSpace (ZMod 3) := ⟨fun _ => trivial⟩

/-- Read a sample from `Fin 3` as a scalar. -/
def toScalar : Fin ((3 : ℕ+) : ℕ) ≃ ZMod 3 := (finCongr rfl).trans (ZMod.finEquiv 3).toEquiv

/-- A uniform scalar, sampled by rejection from fair coins. -/
def scalar : Resumption coinOracle (ZMod 3) := toScalar <$> Resumption.uniformFin 3

theorem toMeasure_scalar : scalar.toMeasure fairCoins = uniformOn Set.univ := by
  rw [scalar, Resumption.toMeasure_map_of_discrete' fairCoins, Resumption.toMeasure_uniformFin,
    uniformOn_univ_map_equiv]

-- Honest transcripts are distributed as simulated ones.
example (g : ZMod 3) (secret : ZMod 3) :=
  sem_realTranscript_eq_simulateTranscript g (Resumption.isMeasureSemantics_toMeasure fairCoins)
    scalar toMeasure_scalar secret

-- The extraction bound holds for every prover whose phases are free programs of coin flips.
example (g pk : ZMod 3) (commit : coinOracle.FreeM (ZMod 3 × Bool))
    (response : Bool → ZMod 3 → coinOracle.FreeM (ZMod 3)) :=
  le_sem_extractor (Resumption.isMeasureSemantics_toMeasure fairCoins) scalar g pk
    (monadLift commit) (fun state c => monadLift (response state c)) toMeasure_scalar

end CslibTests.Schnorr
