/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Bind
public import Cslib.Foundations.MeasureTheory.Uniform
public import Mathlib.Algebra.Group.Equiv.Basic

/-! # Measure semantics of Schnorr transcripts -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory

variable {P : PFunctor.{0, 0}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))
  {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
  [MeasurableSpace G] (sample : P.FreeM F) (g : G)

/-- Perfect honest-verifier zero knowledge, as equality of the entire transcript measures.
The simulator needs only the public key. -/
theorem denote_realTranscript_eq_simulateTranscript (secret : F)
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ (realTranscript sample g secret) =
      FreeM.denote μ (simulateTranscript sample g (secret • g)) := by
  simp only [realTranscript, simulateTranscript, FreeM.denote_bind_of_discrete,
    FreeM.denote_pure, hsample]
  rw [Measure.bind_comm Measurable.of_discrete]
  apply congrArg (Measure.bind (uniformOn (Set.univ : Set F)))
  funext challenge
  let e := Equiv.addRight (challenge * secret)
  let f : F → Measure (G × F × F) := fun response =>
    Measure.dirac (response • g - challenge • secret • g, challenge, response)
  calc
    _ = ((uniformOn (Set.univ : Set F)).map e).bind f := by
      rw [Measure.bind_map _ Measurable.of_discrete Measurable.of_discrete]
      congr 1
      funext nonce
      simp [e, f, respond, add_smul, mul_smul]
    _ = _ := by rw [map_uniformOn_univ]

omit μ sample in
/-- For a fixed challenge, the simulated commitment is uniform. This is the collision term
needed when programming a signing response into a random oracle. -/
theorem uniform_simulatedCommitment [MeasurableSingletonClass G] [Finite G]
    (hg : Function.Bijective (fun scalar : F => scalar • g)) (pk : G) (challenge : F) :
    (uniformOn (Set.univ : Set F)).map (fun response => response • g - challenge • pk) =
      uniformOn Set.univ :=
  map_uniformOn_univ
    ((Equiv.ofBijective (fun scalar : F => scalar • g) hg).trans (Equiv.subRight _))

end Cslib.Crypto.Schnorr
