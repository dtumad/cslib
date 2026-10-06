/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Defs
public import Cslib.Foundations.Control.Monad.MeasureSemantics
public import Cslib.Foundations.MeasureTheory.Uniform
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Security of ElGamal encryption under DDH

We analyse the chosen-plaintext experiment in a monad `m` with a measure semantics `sem`
(`Cslib.IsMeasureSemantics`). The exponent sampler, the challenge coin and both phases of the
adversary are arbitrary computations in `m`, which may use any randomness or oracles `m` provides.
For instance, `m` may be the polynomial programs with an operation selecting a uniform element of
each `Fin k`, so that exponents are sampled in one step
(`PFunctor.FreeM.isMeasureSemantics_toMeasure`), or the resumptions over a single fair coin, so
that exponents are drawn by rejection sampling, which returns almost surely but not within a
bounded number of flips (`PFunctor.Resumption.isMeasureSemantics_toMeasure`).

Run on a Diffie–Hellman triple, `ddhReduction` plays exactly the chosen-plaintext experiment
(`sem_realExperiment_ddhReduction`). Run on a triple with an independent third exponent, the
challenge ciphertext is a uniform group element whatever the message, so the reduction outputs a
fair coin (`sem_idealExperiment_ddhReduction`); this needs the sampler and the coin to be uniform,
`g` to generate a group of order `n`, and the adversary to return almost surely. Hence the
adversary's advantage in guessing the challenge coin equals the reduction's advantage in
distinguishing the two experiments (`cpa_advantage_eq_ddh_advantage`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Cslib.Crypto.ElGamal

variable {m : Type → Type*} [Monad m] [LawfulMonad m]
  {sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α} (hsem : IsMeasureSemantics m sem)
  {G State : Type} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State] {n : ℕ}
  (sample : m (Fin n)) (coin : m Bool) (g : G)
  (choose : G → m (G × G × State)) (guess : State → G × G → m Bool)
include hsem

/-- On a Diffie–Hellman triple, the reduction plays the chosen-plaintext experiment: the two
programs differ only in when the encryption exponent is sampled. -/
theorem sem_realExperiment_ddhReduction :
    sem (DDH.realExperiment sample g (ddhReduction coin choose guess)) =
      sem (cpaExperiment sample coin g choose guess) := by
  simp only [DDH.realExperiment, ddhReduction, cpaExperiment, challenge, keygen, encrypt,
    bind_assoc, pure_bind, hsem.map_bind_of_discrete, pow_mul]
  congr! 2 with x
  rw [Measure.bind_comm .of_discrete]
  congr! 2 with msgs
  exact Measure.bind_comm .of_discrete

variable [∀ pk, IsProbabilityMeasure (sem (choose pk))]
  [∀ state ciphertext, IsProbabilityMeasure (sem (guess state ciphertext))]

/-- On a triple with an independent third exponent, the reduction outputs a fair coin, provided
both phases of the adversary return almost surely. -/
theorem sem_idealExperiment_ddhReduction
    (hg : Function.Bijective fun x : Fin n => g ^ x.val)
    (hsample : sem sample = uniformOn Set.univ) (hcoin : sem coin = uniformOn Set.univ) :
    sem (DDH.idealExperiment sample g (ddhReduction coin choose guess)) = uniformOn Set.univ := by
  have : Finite G := .of_surjective _ hg.2
  have : Nonempty (Fin n) := ⟨(Equiv.ofBijective _ hg).symm 1⟩
  have : IsProbabilityMeasure (sem sample) := hsample ▸ inferInstance
  have key (pk head : G) :
      (sem sample).bind (fun z => sem (ddhReduction coin choose guess pk head (g ^ z.val))) =
        uniformOn Set.univ := by
    simp only [ddhReduction, challenge, pure_bind, bind_pure_comp, hsem.map_bind_of_discrete,
      hsem.map_map_of_discrete, hcoin, hsample]
    rw [Measure.bind_comm .of_discrete]
    trans (sem (choose pk)).bind fun _ => uniformOn Set.univ
    · congr! with b
      rw [Measure.bind_comm .of_discrete]
      trans (uniformOn Set.univ : Measure Bool).bind fun a =>
        (uniformOn Set.univ : Measure G).bind fun h => (sem (guess b.2.2 (head, h))).map (a == ·)
      · congr! with a
        rw [← uniformOn_univ_bind_equiv
          ((Equiv.ofBijective _ hg).trans (Equiv.mulLeft (if a then b.2.1 else b.1)))]
        rfl
      · rw [Measure.bind_comm .of_discrete]
        simp only [uniformOn_univ_bind_map_beq, Measure.bind_const, measure_univ, one_smul]
    · simp only [Measure.bind_const, measure_univ, one_smul]
  simp [DDH.idealExperiment, hsem.map_bind_of_discrete, key, Measure.bind_const]

/-- The advantage of a chosen-plaintext adversary in guessing the challenge coin is the advantage
of the reduction in distinguishing Diffie–Hellman triples. -/
theorem cpa_advantage_eq_ddh_advantage
    (hg : Function.Bijective fun x : Fin n => g ^ x.val)
    (hsample : sem sample = uniformOn Set.univ) (hcoin : sem coin = uniformOn Set.univ) :
    |(sem (cpaExperiment sample coin g choose guess)).real {true} - 1 / 2| =
      |(sem (DDH.realExperiment sample g (ddhReduction coin choose guess))).real {true} -
        (sem (DDH.idealExperiment sample g (ddhReduction coin choose guess))).real {true}| := by
  rw [sem_realExperiment_ddhReduction hsem,
    sem_idealExperiment_ddhReduction hsem sample coin g choose guess hg hsample hcoin]
  congr 2
  rw [measureReal_def, uniformOn_univ]
  simp

end Cslib.Crypto.ElGamal
