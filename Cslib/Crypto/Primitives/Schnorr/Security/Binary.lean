/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Binary
public import Cslib.Crypto.DiscreteLog.Security

/-!
# Computational EUF-CMA security of binary Schnorr

Uniform discrete-logarithm hardness implies negligible forgery probability for the honest
bounded binary implementation. A single adversary machine supplies the saved private tape,
the replay clock, and the source query budgets. The reduction's complete machine is constructed
from the encoded group and scalar primitives. The ideal challenge sampler remains external.
-/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory Turing.MultiTapeTM Turing.MultiTapePTM
  Turing.MultiTapeMachine

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  [∀ n, MeasurableSpace (F n)] [∀ n, MeasurableSingletonClass (F n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, MeasurableSingletonClass (G n)]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- The actual binary Schnorr game is EUF-CMA secure under uniform discrete-logarithm
hardness. The attempt budget is efficiently computed and at least the security parameter.
Every sampler failure loses; no conditioning or asymptotic field-size premise is used. -/
theorem negligible_unforgeabilityWordExperiment_of_dlog
    (element : ∀ n, Computability.Encoding (G n) Bool) (order attempts : ℕ → ℕ)
    (scalar : ∀ n, F n ≃ Fin (order n)) (g : ∀ n, G n)
    (adversary : ∀ n, G n →
      (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word (G n) (F n)).FreeM
        (Word × G n × F n))
    (hadversary : IsPPT (sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding))
      wordEncoding (fun arg => ((Computability.encodingList Bool).bitPair
        ((element arg.1).bitPair (.finEquiv (scalar arg.1)))).bitOption.encode <$>
          ((adversary arg.1 arg.2).liftM (encodeEffects
            (signatureRequestEncoding (Computability.encodingList Bool) (element arg.1))
            (signatureResponseEncoding (element arg.1) (.finEquiv (scalar arg.1))))).run))
    (horder : IsPolyTime unaryEncoding (fun n => binaryEncoding (order n)))
    (hattempts : IsPolyTime unaryEncoding (fun n => unaryEncoding (attempts n)))
    (hbudget : ∀ n, n ≤ attempts n)
    (hg : IsPolyTime unaryEncoding (fun n => (element n).encode (g n)))
    (hz : IsPolyTime unaryEncoding (fun n => finEquivEncoding (scalar n) 0))
    (hgroupDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 + arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))
    (hscalarSub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (finEquivEncoding (scalar n))))
      (fun arg => finEquivEncoding (scalar arg.1) (arg.2.1 - arg.2.2)))
    (hscalarDiv : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (finEquivEncoding (scalar n))))
      (fun arg => finEquivEncoding (scalar arg.1) (arg.2.1 / arg.2.2)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, (finEquivEncoding (scalar n) value).length ≤ scalarSize n)
    (hgenerator : ∀ n, Function.Bijective (fun secret : F n => secret • g n))
    (hdlog : Game.Secure
      (fun (test : ∀ n, G n → (effects Empty).FreeM (Option (F n))) n =>
        (uniformOn (Set.univ : Set (F n))).bind (fun secret =>
          (FreeM.denote coinMeasure (test n (secret • g n))).map
            (fun out => out.any (fun value => decide (value • g n = secret • g n)))))
      (fun _ _ => Measure.dirac false)
      (fun test => IsPPT (sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding))
        wordEncoding (fun arg => optionEncoding (finEquivEncoding (scalar arg.1)) <$>
          test arg.1 arg.2))) :
    Negligible (fun n => ((unforgeabilityWordExperiment (scalar n) (attempts n) (g n)
      (adversary n)).toMeasure (.ofMeasure coinMeasure) {some true}).toReal) := by
  classical
  let : ∀ n, Fintype (F n) := fun n => Fintype.ofEquiv (Fin (order n)) (scalar n).symm
  let : ∀ n, Countable (G n) := fun n => (element n).encode_injective.countable
  obtain ⟨implementation⟩ := isPPT_iff_nonempty_realizer.mp hadversary
  let : Finite implementation.State := implementation.finiteState
  let : Fintype implementation.State := Fintype.ofFinite _
  let control := finiteEncoding implementation.State
  let input := sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding)
  let reduce n pk := dlogReductionWord (Oracle := Empty) (element n) (scalar n)
    implementation.machine (input ⟨n, pk⟩) (Snapshot.initial implementation.machine.initial)
      (g n) pk (implementation.clock (input ⟨n, pk⟩).length) (attempts n)
  have hi := isPolyTime_input input
  have hp := hi.sigma_fst
  have hr : IsPPT input wordEncoding (fun arg =>
      optionEncoding (finEquivEncoding (scalar arg.1)) <$> reduce arg.1 arg.2) :=
    isPPT_dlogReductionWord element scalar horder hz hgroupDecode hsmul hadd hsub
      hscalarSub hscalarDiv input implementation.machine hp (hg.comp_encoded hp)
      hi.sigma_snd (isPolyTime_const input (machineSnapshotEncoding implementation.tapes
        implementation.ports control (Snapshot.initial implementation.machine.initial))) hi
      (implementation.isPolyTime_clock.comp_encoded hi.unaryLength)
      (hattempts.comp_encoded hp) hgroup hscalar hgsize hfsize
  let probability n := ∫⁻ secret : F n, (reduce n (secret • g n)).toMeasure
    (.ofMeasure coinMeasure) {out | ∃ value, out = some value ∧ value • g n = secret • g n}
      ∂uniformOn Set.univ
  have hprobability : Negligible (fun n => (probability n).toReal) := by
    have h := hdlog reduce hr
    simp only [Game.advantage_dirac_false, Game.winProbability, measureReal_def] at h
    convert h using 1
    funext n
    congr 1
    rw [Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro secret
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
    congr 1
    ext out
    cases out <;> simp
  have hinverse := DiscreteLog.negligible_inv_card_of_secure g
    (fun n => (element n).toEmbedding) (fun n => finEquivEncoding (scalar n))
    (fun n => (hgenerator n).injective) hz hdlog
  let T n := implementation.clock (2 * n + groupSize n + 1)
  have hT : PolynomiallyBounded T :=
    implementation.polynomiallyBounded_clock.comp (by fun_prop)
  have hclock (n : ℕ) (pk : G n) : implementation.clock (input ⟨n, pk⟩).length ≤ T n := by
    apply implementation.clock_mono
    simp only [input, length_sigmaEncoding, unaryEncoding_apply, List.length_replicate]
    exact Nat.add_le_add_right (Nat.add_le_add_left (hgsize n pk) (2 * n)) 1
  have hcollision := hinverse.mul_polynomiallyBounded
    (count := fun n => T n * (T n + T n)) (by fun_prop)
  have hhash := hinverse.mul_polynomiallyBounded
    (count := fun n => T n + 1) (by fun_prop)
  have hcutoff := negligible_sampling_error (draws := fun n => 4 * T n + 2)
    (by fun_prop) hbudget
  have hroot := Negligible.sqrt (Negligible.mul_polynomiallyBounded
    (count := fun n => T n + 1) (hprobability.add hcutoff) (by fun_prop))
  apply negligible_of_le ((hcollision.add hhash).add hroot) (fun _ => ENNReal.toReal_nonneg)
  intro n
  have h := unforgeabilityWordExperiment_bound_sqrt (element n) (scalar n) implementation
    (fun pk => (⟨n, pk⟩ : Σ n, G n)) (adversary n) (fun _ => rfl)
    (g n) (hgenerator n) (T n) (attempts n) (hclock n)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, div_eq_mul_inv,
    Pi.add_apply, probability, reduce] using h

end Cslib.Crypto.Schnorr
