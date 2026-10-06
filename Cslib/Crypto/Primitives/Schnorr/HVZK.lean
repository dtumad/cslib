/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Defs
public import Cslib.Foundations.Control.Monad.MeasureSemantics
public import Cslib.Foundations.MeasureTheory.Uniform
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Honest-verifier zero knowledge of Schnorr identification

Under any measure semantics of the monad (`Cslib.IsMeasureSemantics`) with a uniform sampler of
scalars, an honest transcript is distributed exactly as a simulated one, which needs only the
public key (`sem_realTranscript_eq_simulateTranscript`). The simulated commitment alone is uniform
(`sem_simulateTranscript_map_fst`), which bounds collisions when a signing simulator programs a
random oracle.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open MeasureTheory ProbabilityTheory

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F] (g : G)

/-- For a fixed challenge, the simulated commitment of a uniform response is uniform. -/
theorem uniformOn_map_simulatedCommitment [MeasurableSpace G] [MeasurableSingletonClass G]
    [Finite G] (hg : Function.Bijective (fun scalar : F => scalar • g)) (pk : G) (challenge : F) :
    (uniformOn (Set.univ : Set F)).map (fun response => response • g - challenge • pk) =
      uniformOn Set.univ :=
  uniformOn_univ_map_equiv
    ((Equiv.ofBijective (fun scalar : F => scalar • g) hg).trans (Equiv.subRight _))

variable {m : Type → Type*} [Monad m]
  {sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α} (hsem : IsMeasureSemantics m sem)
  (sample : m F) (hsample : sem sample = uniformOn Set.univ)
include hsem hsample

/-- Perfect honest-verifier zero knowledge: an honest transcript is distributed as a simulated
one, which needs only the public key. -/
theorem sem_realTranscript_eq_simulateTranscript [MeasurableSpace G] (secret : F) :
    sem (realTranscript sample g secret) = sem (simulateTranscript sample g (secret • g)) := by
  simp only [realTranscript, simulateTranscript, hsem.map_bind_of_discrete, hsem.map_pure,
    hsample]
  rw [Measure.bind_comm .of_discrete]
  congr 1
  funext challenge
  conv_rhs => rw [← uniformOn_univ_bind_equiv (Equiv.addRight (challenge * secret))]
  congr 1
  funext nonce
  simp [respond, add_smul, mul_smul]

/-- Forgetting the challenge and response of a simulated transcript leaves a uniform
commitment. -/
theorem sem_simulateTranscript_map_fst [LawfulMonad m] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Finite G]
    (hg : Function.Bijective (fun scalar : F => scalar • g)) (pk : G) :
    (sem (simulateTranscript sample g pk)).map Prod.fst = uniformOn Set.univ := by
  rw [← hsem.map_map _ measurable_fst]
  simp only [simulateTranscript, map_bind, map_pure, hsem.map_bind_of_discrete, hsem.map_pure,
    hsample]
  simp_rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete,
    uniformOn_map_simulatedCommitment g hg pk]
  rw [Measure.bind_const, measure_univ, one_smul]

end Cslib.Crypto.Schnorr
