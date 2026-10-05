/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Fork
public import Cslib.Computability.PolynomialTime.Sampling.Finite
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import Cslib.Foundations.Data.PFunctor.Free.Random.Approximation
public import Cslib.Crypto.Primitives.Schnorr.Simulation.Probability

/-!
# Schnorr replay with bounded binary sampling

The reduction receives its discrete-logarithm challenge externally. It samples one private
machine tape and `4 * clock + 2` scalar slots: two per possible signing request, followed by
two hash tapes that each include final verification. Every scalar slot is checked before
execution. Both runs share the same private randomness.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

section Reduction

variable {F G Oracle : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

private abbrev scalarEffects (F : Type) :=
  PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk Unit (fun _ => F)

private def withScalarSampling {α : Type}
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM α) :
    (signatureEffects (scalarEffects F) Word G F).FreeM α :=
  source.liftM (P := signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F) (fun
    | .inl op => FreeM.lift (P := signatureEffects (scalarEffects F) Word G F) (.inl (.inl op))
    | .inr op => FreeM.lift (P := signatureEffects (scalarEffects F) Word G F) (.inr op))

/-- Honest binary EUF-CMA: key generation, signing, and new hash entries use bounded scalar
sampling, while the adversary keeps its native fair coins. Any exhausted draw loses. -/
def unforgeabilityWordExperiment {order : ℕ} (scalar : F ≃ Fin order) (attempts : ℕ) (g : G)
    (adversary : G → (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F)) : (effects Empty).FreeM (Option Bool) :=
  ((unforgeabilityExperiment (F := F) (G := G)
    (FreeM.lift (P := PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk Unit (fun _ => F)) (.inr ())) g
    (fun pk => (adversary pk).liftM
      (P := signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F) (fun
        | .inl op => FreeM.lift (P := signatureEffects
            (PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk Unit (fun _ => F)) Word G F)
              (.inl (.inl op))
        | .inr op => FreeM.lift (P := signatureEffects
            (PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk Unit (fun _ => F)) Word G F)
              (.inr op)))).liftM
      (P := PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk Unit (fun _ => F)) (fun
      | .inl _ => OptionT.mk (some <$> coin)
      | .inr _ => OptionT.mk (Option.map scalar.symm <$>
          FreeM.sampleFin ((fun bit : Bool => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
            order order.size attempts))).run

/-- The complete binary reduction. Exhaustion of any presampled slot aborts, including slots
that the subsequent runs would not consume. No secret-key sampler is part of this program. -/
def dlogReductionWord (element : Computability.Encoding G Bool) {order : ℕ}
    (scalar : F ≃ Fin order) {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G) (clock attempts : ℕ) :
    (effects Oracle).FreeM (Option F) := do
  let coins ← (List.replicate clock ()).mapM (fun _ => coin)
  let samples ← (List.replicate (4 * clock + 2) ()).mapM (fun _ =>
    FreeM.sampleFin ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
      order order.size attempts)
  pure (do
    let tape ← (samples.mapM id).map (List.map scalar.symm)
    dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot g pk
      (tape.take (2 * clock)) ((tape.drop (2 * clock)).take (clock + 1))
      (tape.drop (3 * clock + 1)))

private theorem simulatedForgery_withScalarSampling (sample : (scalarEffects F).FreeM F)
    (g pk : G)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F)) :
    simulatedForgery FreeM.lift sample (fun _ => sample) g pk
      (fun _ => withScalarSampling source) =
    simulatedForgery (fun op => FreeM.lift (P := scalarEffects F) (.inl op)) sample
      (fun _ => sample) g pk (fun _ => source) := by
  have h : (withScalarSampling source).liftM
      (simulatedSignatureHandler FreeM.lift sample (fun _ => sample) g pk) =
      source.liftM (simulatedSignatureHandler
        (fun op => FreeM.lift (P := scalarEffects F) (.inl op)) sample
        (fun _ => sample) g pk) := by
    rw [withScalarSampling, FreeM.liftM_comp]
    congr 1
    funext op
    cases op with
    | inl op =>
      simp only [FreeM.liftM_lift
        (P := signatureEffects (scalarEffects F) Word G F), simulatedSignatureHandler]
      rfl
    | inr op =>
      cases op <;> simp only [FreeM.liftM_lift
        (P := signatureEffects (scalarEffects F) Word G F), simulatedSignatureHandler]
  simp only [simulatedForgery, h]

end Reduction

section QueryBound

variable {F G Input : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

private theorem queryBoundP_withScalarSampling_le
    (element : Computability.Encoding G Bool) (scalar : Computability.Encoding F Bool)
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element scalar))).run)
    (select : (Word × G) ⊕ Word → Bool) :
    FreeM.queryBoundP (Sum.elim (fun _ => false) select) (withScalarSampling source) ≤
      implementation.clock (input a).length := by
  unfold withScalarSampling
  refine (FreeM.queryBoundP_liftM_le
    (P := signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F)
    (Q := signatureEffects (scalarEffects F) Word G F) (Sum.elim (fun _ => false) select)
    (Sum.elim (fun _ => false) select) _ ?_ source).trans ?_
  · intro op
    cases op <;>
      simp only [FreeM.queryBoundP_lift (P := signatureEffects (scalarEffects F) Word G F),
        Sum.elim_inl, Sum.elim_inr] <;> exact le_rfl
  · refine (queryBoundP_le_encodeEffects
      (signatureRequestEncoding (Computability.encodingList Bool) element)
      (signatureResponseEncoding element scalar) select source).trans ?_
    have h := implementation.queryBoundP_le a (Sum.elim (fun _ => false)
      (fun query => ((signatureRequestEncoding (Computability.encodingList Bool) element
        ).decodeChecked query.2).any select)) rfl
    simpa only [hsource, FreeM.queryBoundP_map] using h

end QueryBound

section Cutoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]

/-- Bounded scalar sampling loses at most `(4 * clock + 2) * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` for the complete
reduction and every payoff that gives failure value zero. The challenge is fixed externally;
the bound includes every private and hash slot, and the private machine coins are exact. -/
theorem lintegral_dlogReductionWord_le (element : Computability.Encoding G Bool) {order : ℕ}
    (scalar : F ≃ Fin order) {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G) (clock attempts : ℕ)
    (post : Option F → ℝ≥0∞) (hpost : ∀ out, post out ≤ 1) (hnone : post none = 0) :
    let finish coins (tape : List F) :=
      dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot g pk
        (tape.take (2 * clock)) ((tape.drop (2 * clock)).take (clock + 1))
        (tape.drop (3 * clock + 1))
    let bits := (List.replicate clock ()).mapM (fun _ => coin (Oracle := Empty))
    let ideal := (List.replicate (4 * clock + 2) ()).mapM
      (fun _ => FreeM.lift (P := PFunctor.mk Unit (fun _ => Fin order)) ())
    (∫⁻ coins, ∫⁻ out, post out ∂((fun tape => finish coins (tape.map scalar.symm)) <$>
      ideal).toMeasure (.ofMeasure (fun _ => uniformOn Set.univ))
        ∂bits.toMeasure (.ofMeasure coinMeasure)) ≤
      (∫⁻ out, post out ∂(dlogReductionWord (Oracle := Empty) element scalar machine word
        snapshot g pk clock attempts).toMeasure (.ofMeasure coinMeasure)) +
          (4 * clock + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  intro finish bits ideal
  have horder : 0 < order := Nat.zero_lt_of_lt (scalar 0).isLt
  let : NeZero order := ⟨horder.ne'⟩
  let : MeasurableSpace (List (Fin order)) := ⊤
  let : MeasurableSpace (List (Option (Fin order))) := ⊤
  let samples := (List.replicate (4 * clock + 2) ()).mapM (fun _ =>
    FreeM.sampleFin ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$>
      coin (Oracle := Empty)) order order.size attempts)
  let actual coins := (fun results => (results.mapM id).bind
    (fun tape => finish coins (tape.map scalar.symm))) <$> samples
  have hpoint (coins : Word) :
      (∫⁻ out, post out ∂((fun tape => finish coins (tape.map scalar.symm)) <$>
        ideal).toMeasure (.ofMeasure (fun _ => uniformOn Set.univ))) ≤
        (∫⁻ out, post out ∂(actual coins).toMeasure (.ofMeasure coinMeasure)) +
          (4 * clock + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
    have h := FreeM.lintegral_replicate_uniform_le_sampleFin_add coinMeasure _ denote_finTwo_coin
      order order.size attempts (4 * clock + 2) (Nat.lt_size_self order).le
      (Nat.two_pow_size_le_twice order horder)
      (fun tape => post (finish coins (tape.map scalar.symm))) (fun tape => hpost _)
    change _ ≤ (∫⁻ out, post out ∂FreeM.denote coinMeasure (actual coins)) + _
    rw [show actual coins = (fun results => (results.mapM id).bind
      (fun tape => finish coins (tape.map scalar.symm))) <$> samples from rfl]
    simp only [FreeM.toMeasure, ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete]
    rw [lintegral_map' Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
    rw [lintegral_map' Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
    convert h using 1
    congr 1
    rw [← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete,
      lintegral_map' Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro results
    cases results.mapM id <;> simp [hnone]
  have heq : dlogReductionWord (Oracle := Empty) element scalar machine word snapshot
      g pk clock attempts = bits >>= actual := by
    simp only [dlogReductionWord, bits, actual, samples, map_eq_pure_bind]
    congr 1
    funext coins
    congr 1
    funext results
    cases results.mapM id <;> rfl
  rw [heq]
  change _ ≤ (∫⁻ out, post out ∂FreeM.denote coinMeasure (bits >>= actual)) + _
  rw [FreeM.denote_bind_of_discrete,
    Measure.lintegral_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  calc
    _ ≤ ∫⁻ coins, (∫⁻ out, post out ∂(actual coins).toMeasure (.ofMeasure coinMeasure)) +
        (4 * clock + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts
          ∂bits.toMeasure (.ofMeasure coinMeasure) := lintegral_mono hpoint
    _ = _ := by rw [lintegral_add_right _ measurable_const]; simp [FreeM.toMeasure]

/-- The scalar cutoff also bounds a replay written with explicit ideal samplers. Their laws
are the only probabilistic premises; consecutive blocks form the single prepared scalar tape. -/
theorem lintegral_dlogReductionFromAnswers_le_word {P : PFunctor.{0, 0}}
    [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
    (μ : OutputMeasure P)
    (bit : P.FreeM Bool) (sample : P.FreeM F)
    (hbit : bit.toMeasure μ = uniformOn Set.univ)
    (hsample : sample.toMeasure μ = uniformOn Set.univ)
    (element : Computability.Encoding G Bool) {order : ℕ} (scalar : F ≃ Fin order)
    {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G) (clock attempts : ℕ)
    (post : Option F → ℝ≥0∞) (hpost : ∀ out, post out ≤ 1) (hnone : post none = 0) :
    (∫⁻ out, post out ∂(do
      let coins ← (List.replicate clock ()).mapM (fun _ => bit)
      let privateScalars ← (List.replicate (2 * clock) ()).mapM (fun _ => sample)
      let answers ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      let fresh ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      pure (dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot
        g pk privateScalars answers fresh)).toMeasure μ) ≤
      (∫⁻ out, post out ∂(dlogReductionWord (Oracle := Empty) element scalar machine word
        snapshot g pk clock attempts).toMeasure (.ofMeasure coinMeasure)) +
          (4 * clock + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  let : Fintype F := Fintype.ofEquiv (Fin order) scalar.symm
  let : MeasurableSpace (List F) := ⊤
  let : MeasurableSpace (List (Fin order)) := ⊤
  let draw := FreeM.lift (P := PFunctor.mk Unit (fun _ => Fin order)) ()
  let ν : OutputMeasure (PFunctor.mk Unit (fun _ => Fin order)) :=
    .ofMeasure (fun _ => uniformOn Set.univ)
  let finish coins (tape : List F) :=
    dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot g pk
      (tape.take (2 * clock)) ((tape.drop (2 * clock)).take (clock + 1))
      (tape.drop (3 * clock + 1))
  have hsplit (coins : Word) :
      (do
        let tape ← (List.replicate (4 * clock + 2) ()).mapM (fun _ => sample)
        pure (finish coins tape)) = (do
        let privateScalars ← (List.replicate (2 * clock) ()).mapM (fun _ => sample)
        let answers ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
        let fresh ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
        pure (dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot
          g pk privateScalars answers fresh)) := by
    have hcount : 4 * clock + 2 = 2 * clock + ((clock + 1) + (clock + 1)) := by omega
    have hdrop (tape : List F) : tape.drop (3 * clock + 1) =
        (tape.drop (2 * clock)).drop (clock + 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    simp only [finish, hcount, hdrop]
    rw [FreeM.bind_replicate_add sample (2 * clock) ((clock + 1) + (clock + 1))
      (fun before after => pure (dlogReductionFromAnswers element (.finEquiv scalar)
        machine word coins snapshot g pk before (after.take (clock + 1))
          (after.drop (clock + 1))))]
    apply bind_congr
    intro privateScalars
    exact FreeM.bind_replicate_add sample (clock + 1) (clock + 1)
      (fun answers fresh => pure (dlogReductionFromAnswers element (.finEquiv scalar)
        machine word coins snapshot g pk privateScalars answers fresh))
  have hscalar : FreeM.denote μ sample = FreeM.denote ν (scalar.symm <$> draw) := by
    rw [← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete,
      FreeM.denote_lift]
    exact hsample.trans (map_uniformOn_univ scalar.symm).symm
  have hmap (count : ℕ) : (List.replicate count ()).mapM (fun _ => scalar.symm <$> draw) =
      List.map scalar.symm <$> (List.replicate count ()).mapM (fun _ => draw) := by
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [List.replicate_succ, List.mapM_cons, ih, List.mapM_cons]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind, List.map_cons]
  have htape := FreeM.denote_replicate_congr μ ν sample (scalar.symm <$> draw)
    hscalar (4 * clock + 2)
  rw [hmap] at htape
  have hbits := FreeM.denote_replicate_congr μ coinMeasure bit (coin (Oracle := Empty))
    (hbit.trans (by simp)) clock
  have h := lintegral_dlogReductionWord_le element scalar machine word snapshot g pk clock
    attempts post hpost hnone
  convert h using 1
  simp only [FreeM.toMeasure]
  have hprogram : (do
      let coins ← (List.replicate clock ()).mapM (fun _ => bit)
      let privateScalars ← (List.replicate (2 * clock) ()).mapM (fun _ => sample)
      let answers ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      let fresh ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      pure (dlogReductionFromAnswers element (.finEquiv scalar) machine word coins snapshot
        g pk privateScalars answers fresh)) =
      (do
        let coins ← (List.replicate clock ()).mapM (fun _ => bit)
        let tape ← (List.replicate (4 * clock + 2) ()).mapM (fun _ => sample)
        pure (finish coins tape)) := by
    apply bind_congr
    intro coins
    exact (hsplit coins).symm
  rw [hprogram]
  rw [FreeM.denote_bind_of_discrete, hbits,
    Measure.lintegral_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro coins
  rw [← map_eq_pure_bind, ← FreeM.map_eq_map,
    FreeM.denote_map _ _ _ Measurable.of_discrete, htape,
    ← FreeM.denote_map _ _ _ Measurable.of_discrete]
  simp only [FreeM.map_eq_map, Functor.map_map]
  rfl

/-- Concrete reduction for the original typed adversary and the actual bounded binary
machine. Both replay runs share private randomness; the challenge key is supplied externally. -/
theorem le_toMeasure_dlogReductionWord {P : PFunctor.{0, 0}} {Input : Type}
    [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (μ : OutputMeasure P) [∀ op, IsProbabilityMeasure (μ op)]
    (bit : P.FreeM Bool) (sample : P.FreeM F)
    (hbit : bit.toMeasure μ = uniformOn Set.univ)
    (hsample : sample.toMeasure μ = uniformOn Set.univ)
    (element : Computability.Encoding G Bool) {order : ℕ} (scalar : F ≃ Fin order)
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair (.finEquiv scalar))).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element (.finEquiv scalar)))).run)
    (g pk : G) (attempts : ℕ) :
    let clock := implementation.clock (input a).length
    let ε := ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
      (fun _ => source)).run).toMeasure μ {out | out.isSome}
    ε * (ε / (clock + 1 : ℕ) - 1 / (Nat.card F : ℝ≥0∞)) ≤
      (dlogReductionWord (Oracle := Empty) element scalar implementation.machine (input a)
        (Snapshot.initial implementation.machine.initial) g pk clock attempts).toMeasure
          (.ofMeasure coinMeasure) {out | ∃ secret, out = some secret ∧ secret • g = pk} +
            (4 * clock + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  let : Fintype F := Fintype.ofEquiv (Fin order) scalar.symm
  let : Countable G := element.encode_injective.countable
  let : MeasurableSpace (List F) := ⊤
  let : MeasurableSpace (List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) := ⊤
  let : MeasurableSpace (List Word × List ((Word × G) × F)) := ⊤
  let event : Set (Option F) := {out | ∃ secret, out = some secret ∧ secret • g = pk}
  have hfork := le_toMeasure_dlogReductionFromAnswers_typed element (.finEquiv scalar) μ
    implementation a source hsource bit sample hbit g pk (1 / Nat.card F) (fun answer => by
      rw [hsample]
      simp [uniformOn_univ, Nat.card_eq_fintype_card])
  have hcutoff := lintegral_dlogReductionFromAnswers_le_word μ bit sample hbit hsample element
    scalar implementation.machine (input a) (Snapshot.initial implementation.machine.initial)
    g pk (implementation.clock (input a).length) attempts (event.indicator (fun _ => 1))
      (fun out => by by_cases h : out ∈ event <;> simp [h]) (by simp [event])
  simp only [lintegral_indicator_const MeasurableSet.of_discrete, one_mul] at hcutoff
  exact hfork.trans hcutoff

/-- Honest binary EUF-CMA security reduces to the actual binary replay machine. The secret
challenge is sampled ideally outside the reduction, so its cutoff charge is `4 * T + 2`.
The chosen adversary machine supplies the hash and signing budgets through its clock. -/
theorem unforgeabilityWordExperiment_bound {Input : Type}
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (element : Computability.Encoding G Bool) {order : ℕ} (scalar : F ≃ Fin order)
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (index : G → Input)
    (adversary : G → (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : ∀ pk, program (index pk) = ((Computability.encodingList Bool).bitPair
      (element.bitPair (.finEquiv scalar))).bitOption.encode <$>
        ((adversary pk).liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element (.finEquiv scalar)))).run)
    (g : G) (hg : Function.Bijective (fun secret : F => secret • g))
    (T attempts : ℕ) (hclock : ∀ pk, implementation.clock (input (index pk)).length ≤ T) :
    let reduce pk := dlogReductionWord (Oracle := Empty) element scalar implementation.machine
      (input (index pk)) (Snapshot.initial implementation.machine.initial) g pk
      (implementation.clock (input (index pk)).length) attempts
    let ε := (unforgeabilityWordExperiment scalar attempts g adversary).toMeasure
      (.ofMeasure coinMeasure) {some true}
    let ε' := ε - T * (T + T) / (Nat.card F : ℝ≥0∞)
    ε' * (ε' / (T + 1 : ℕ) - 1 / (Nat.card F : ℝ≥0∞)) ≤
      (∫⁻ secret : F, (reduce (secret • g)).toMeasure (.ofMeasure coinMeasure)
        {out | ∃ value, out = some value ∧ value • g = secret • g}
          ∂uniformOn Set.univ) + (4 * T + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  intro reduce ε
  let : Fintype F := Fintype.ofEquiv (Fin order) scalar.symm
  let : Countable G := element.encode_injective.countable
  let : MeasurableSpace (List Word) := ⊤
  let : MeasurableSpace (List ((Word × G) × F)) := ⊤
  let : ∀ op, MeasurableSpace ((scalarEffects F).B op) :=
    OutputMeasure.sumMeasurableSpace (PFunctor.mk Unit (fun _ => Bool))
      (PFunctor.mk Unit (fun _ => F))
  let : ∀ op, Countable ((scalarEffects F).B op) := by
    rintro (op | op)
    · exact inferInstanceAs (Countable Bool)
    · exact inferInstanceAs (Countable F)
  let μ : OutputMeasure (scalarEffects F) :=
    (OutputMeasure.ofMeasure (fun _ : Unit => uniformOn (Set.univ : Set Bool))).sum
      (.ofMeasure (fun _ : Unit => uniformOn (Set.univ : Set F)))
  let bit : (scalarEffects F).FreeM Bool := FreeM.lift (P := scalarEffects F) (.inl ())
  let sample : (scalarEffects F).FreeM F := FreeM.lift (P := scalarEffects F) (.inr ())
  let original pk := withScalarSampling (adversary pk)
  let cutoff : (op : (scalarEffects F).A) → OptionT (effects Empty).FreeM
      ((scalarEffects F).B op)
    | .inl _ => OptionT.mk (some <$> coin)
    | .inr _ => OptionT.mk (Option.map scalar.symm <$>
        FreeM.sampleFin ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          order order.size attempts)
  have hbit : bit.toMeasure μ = uniformOn Set.univ := by
    exact FreeM.denote_lift (P := scalarEffects F) μ (.inl ())
  have hsample : sample.toMeasure μ = uniformOn Set.univ := by
    exact FreeM.denote_lift (P := scalarEffects F) μ (.inr ())
  have hstep : ∀ op, (FreeM.denote coinMeasure (cutoff op).run).comap some ≤ μ op := by
    rintro (op | op)
    · simp only [cutoff, OptionT.run_mk, ← FreeM.map_eq_map,
        FreeM.denote_map _ _ _ Measurable.of_discrete]
      rw [Option.measurableEmbedding_some.comap_map]
      exact le_of_eq denote_coin
    · exact FreeM.comap_denote_map_sampleFin_le coinMeasure _ denote_finTwo_coin
        order order.size attempts scalar.symm (Nat.lt_size_self order).le
  have hgame : ε ≤ (unforgeabilityExperiment sample g original).toMeasure μ {true} := by
    have heq : unforgeabilityWordExperiment scalar attempts g adversary =
        ((unforgeabilityExperiment sample g original).liftM cutoff).run := by
      rfl
    simpa only [ε, heq, FreeM.toMeasure, Set.image_singleton] using
      FreeM.denote_liftM_option_le μ coinMeasure cutoff hstep
        (unforgeabilityExperiment sample g original) {true}
  have hqueries (pk : G) (select : (Word × G) ⊕ Word → Bool) :
      FreeM.queryBoundP (Sum.elim (fun _ => false) select) (original pk) ≤ T :=
    (queryBoundP_withScalarSampling_le element (.finEquiv scalar) implementation (index pk)
      (adversary pk) (hsource pk) select).trans (by exact_mod_cast hclock pk)
  let success (secret : F) := ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g
    (secret • g) adversary).run).toMeasure μ {out | out.isSome}
  have hsimulation : ε ≤ (∫⁻ secret, success secret ∂uniformOn Set.univ) +
      T * (T + T) / (Nat.card F : ℝ≥0∞) := by
    have h := denote_unforgeabilityExperiment_le_simulatedForgery_add μ sample g original
      hg hsample T T (fun pk => by
        convert hqueries pk (Sum.elim (fun _ => false) (fun _ => true)) using 1
        congr 1
        funext op
        rcases op with op | (input | message) <;> rfl)
      (fun pk => by
        convert hqueries pk (Sum.elim (fun _ => true) (fun _ => false)) using 1
        congr 1
        funext op
        rcases op with op | (input | message) <;> rfl)
    have heq (pk : G) : simulatedForgery FreeM.lift sample (fun _ => sample) g pk original =
        simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk adversary := by
      exact simulatedForgery_withScalarSampling sample g pk (adversary pk)
    change FreeM.denote μ sample = _ at hsample
    simpa only [heq, FreeM.toMeasure, hsample, success] using hgame.trans h
  let probability (secret : F) := (reduce (secret • g)).toMeasure (.ofMeasure coinMeasure)
    {out | ∃ value, out = some value ∧ value • g = secret • g}
  have hpoint (secret : F) : success secret *
      (success secret / (T + 1 : ℕ) - 1 / (Nat.card F : ℝ≥0∞)) ≤
      probability secret + (4 * T + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
    have h := le_toMeasure_dlogReductionWord μ bit sample hbit hsample element scalar
      implementation (index (secret • g)) (adversary (secret • g)) (hsource _) g
      (secret • g) attempts
    change success secret * (success secret /
      (implementation.clock (input (index (secret • g))).length + 1 : ℕ) -
        1 / (Nat.card F : ℝ≥0∞)) ≤ probability secret +
      (4 * implementation.clock (input (index (secret • g))).length + 2 : ℕ) *
        (2 : ℝ≥0∞)⁻¹ ^ attempts at h
    apply le_trans ?_ (h.trans ?_)
    · gcongr
      exact hclock (secret • g)
    · gcongr
      exact hclock (secret • g)
  have haverage := ENNReal.mul_sub_lintegral_le (μ := uniformOn (Set.univ : Set F))
    (f := success) Measurable.of_discrete.aemeasurable (fun _ => prob_le_one)
    (T + 1) (1 / Nat.card F)
  have hsim := tsub_le_iff_right.mpr hsimulation
  calc
    _ ≤ (∫⁻ secret, success secret ∂uniformOn Set.univ) *
        ((∫⁻ secret, success secret ∂uniformOn Set.univ) / (T + 1 : ℕ) -
          1 / (Nat.card F : ℝ≥0∞)) := by gcongr
    _ ≤ ∫⁻ secret, success secret * (success secret / (T + 1 : ℕ) -
        1 / (Nat.card F : ℝ≥0∞)) ∂uniformOn Set.univ := by
      simpa only [Nat.cast_add, Nat.cast_one] using haverage
    _ ≤ ∫⁻ secret, probability secret + (4 * T + 2 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ attempts
        ∂uniformOn Set.univ := lintegral_mono hpoint
    _ = _ := by rw [lintegral_add_right _ measurable_const]; simp [probability]

/-- Square-root form of the honest binary reduction, ready for asymptotic security. -/
theorem unforgeabilityWordExperiment_bound_sqrt {Input : Type}
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (element : Computability.Encoding G Bool) {order : ℕ} (scalar : F ≃ Fin order)
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (index : G → Input)
    (adversary : G → (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : ∀ pk, program (index pk) = ((Computability.encodingList Bool).bitPair
      (element.bitPair (.finEquiv scalar))).bitOption.encode <$>
        ((adversary pk).liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element (.finEquiv scalar)))).run)
    (g : G) (hg : Function.Bijective (fun secret : F => secret • g))
    (T attempts : ℕ) (hclock : ∀ pk, implementation.clock (input (index pk)).length ≤ T) :
    let reduce pk := dlogReductionWord (Oracle := Empty) element scalar implementation.machine
      (input (index pk)) (Snapshot.initial implementation.machine.initial) g pk
      (implementation.clock (input (index pk)).length) attempts
    let p := ∫⁻ secret : F, (reduce (secret • g)).toMeasure (.ofMeasure coinMeasure)
      {out | ∃ value, out = some value ∧ value • g = secret • g} ∂uniformOn Set.univ
    ((unforgeabilityWordExperiment scalar attempts g adversary).toMeasure
      (.ofMeasure coinMeasure) {some true}).toReal ≤
      (T : ℝ) * (T + T) / Nat.card F + (T + 1) / Nat.card F +
        Real.sqrt ((T + 1) * (p.toReal + (4 * T + 2) * (2⁻¹ : ℝ) ^ attempts)) := by
  intro reduce p
  let : Fintype F := Fintype.ofEquiv (Fin order) scalar.symm
  have hp : p ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ : F, 1 ∂uniformOn Set.univ := lintegral_mono fun _ => prob_le_one
      _ = 1 := by simp
  have hp_top : p ≠ ⊤ := ne_of_lt (hp.trans_lt (by simp))
  have hcard : (Nat.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F)).ne'
  have hbound := unforgeabilityWordExperiment_bound element scalar implementation index
    adversary hsource g hg T attempts hclock
  have h := ENNReal.toReal_le_mul_add_sqrt_of_mul_sub_le
    (by positivity) (by simp) (by finiteness) (by finiteness) hbound
  have hsub := ENNReal.le_toReal_sub
    (a := (unforgeabilityWordExperiment scalar attempts g adversary).toMeasure
      (.ofMeasure coinMeasure) {some true})
    (b := T * (T + T) / (Nat.card F : ℝ≥0∞)) (by finiteness)
  change _ ≤ _ + Real.sqrt (_ * (p + _).toReal) at h
  rw [ENNReal.toReal_add hp_top (by finiteness)] at h
  rw [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hsub
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat] at h hsub
  push_cast at h
  simp only [div_eq_mul_inv] at h hsub ⊢
  linarith

end Cutoff

section PolynomialTime

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  {Oracle : Type} [Finite Oracle] [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- A single polynomial-time machine prepares both random tapes, runs the checked replay,
and extracts a scalar. All representation and arithmetic costs are included. -/
theorem isPPT_dlogReductionWord
    (element : ∀ n, Computability.Encoding (G n) Bool) {order : ℕ → ℕ}
    (scalar : ∀ n, F n ≃ Fin (order n))
    (horder : IsPolyTime unaryEncoding (fun n => binaryEncoding (order n)))
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
    {Input : Type} (input : Input ↪ Word) {parameter clock attempts : Input → ℕ}
    {generator publicKey : ∀ a, G (parameter a)}
    {k ports : ℕ} {State : Type} [Finite State] {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : Input → Snapshot k Bool State (Fin ports)} {word : Input → Word}
    (hp : IsPolyTime input (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime input (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime input (fun a => (element (parameter a)).encode (publicKey a)))
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word)
    (hclock : IsPolyTime input (fun a => unaryEncoding (clock a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, (finEquivEncoding (scalar n) value).length ≤ scalarSize n) :
    IsPPT (Oracle := Oracle) input wordEncoding (fun a =>
      optionEncoding (finEquivEncoding (scalar (parameter a))) <$>
        dlogReductionWord (element (parameter a)) (scalar (parameter a)) machine (word a)
          (snapshot a) (generator a) (publicKey a) (clock a) (attempts a)) := by
  let Prepared := Σ a : Input × Word, Option (List (F (parameter a.1)))
  let withCoins := pairEncoding input wordEncoding
  let withScalars : Prepared ↪ Word := sigmaEncoding withCoins (fun a =>
    optionEncoding (listEncoding (finEquivEncoding (scalar (parameter a.1)))))
  have hi := isPolyTime_input withScalars
  have ha := hi.sigma_fst.fst
  have hn := hp.comp_encoded ha
  have ht := hclock.comp_encoded ha
  have hprivateCount := (isPolyTime_const withScalars (unaryEncoding 2)).unary_mul ht
  have hhashCount := ht.unary_add (isPolyTime_const withScalars (unaryEncoding 1))
  have hfreshStart := ((isPolyTime_const withScalars (unaryEncoding 3)).unary_mul ht).unary_add
    (isPolyTime_const withScalars (unaryEncoding 1))
  have htape := hi.sigma_snd.option_getD
    (fallback := fun _ => []) (isPolyTime_const withScalars [])
  have hprivate := htape.list_take_indexed hprivateCount
  have hhash := (htape.list_drop_indexed hprivateCount).list_take_indexed
    (count := fun a : Prepared => clock a.1.1 + 1) hhashCount
  have hfresh := htape.list_drop_indexed
    (count := fun a : Prepared => 3 * clock a.1.1 + 1) hfreshStart
  have hdecode := IsPolyTime.decode_finEquiv scalar
    (horder.comp_encoded (isPolyTime_input
      (sigmaEncoding unaryEncoding (fun _ => wordEncoding))).sigma_fst)
    (isPolyTime_input (sigmaEncoding unaryEncoding (fun _ => wordEncoding))).sigma_snd
  have hreplay := isPolyTime_dlogReductionFromAnswers element
    (fun n => Computability.Encoding.finEquiv (scalar n)) hz hgroupDecode hdecode hsmul hadd hsub
    hscalarSub hscalarDiv withScalars machine hn (hg.comp_encoded ha) (hpk.comp_encoded ha)
    (hs.comp_encoded ha) (hw.comp_encoded ha) hi.sigma_fst.snd hprivate
    hgroup hscalar hgsize hfsize
  simp only [Computability.Encoding.finEquiv_toEmbedding, wordEncoding,
    Function.Embedding.refl_apply] at hreplay
  have hpair : IsPolyTime withScalars (fun arg => pairEncoding
      (listEncoding (finEquivEncoding (scalar (parameter arg.1.1))))
      (listEncoding (finEquivEncoding (scalar (parameter arg.1.1))))
      (((arg.2.getD []).drop (2 * clock arg.1.1)).take (clock arg.1.1 + 1),
        (arg.2.getD []).drop (3 * clock arg.1.1 + 1))) := by
    simpa only [pairEncoding_apply, wordEncoding, Function.Embedding.refl_apply,
      listEncoding, Function.Embedding.coeFn_mk] using
      hhash.pair (left := wordEncoding) (right := wordEncoding) hfresh
  have hargs := hi.sigma (index := withScalars) (parameter := id)
    (element := fun i : Prepared => pairEncoding
      (listEncoding (finEquivEncoding (scalar (parameter i.1.1))))
      (listEncoding (finEquivEncoding (scalar (parameter i.1.1))))) hpair
  let run (arg : Prepared) (tape : List (F (parameter arg.1.1))) :=
      dlogReductionFromAnswers (element (parameter arg.1.1))
        (.finEquiv (scalar (parameter arg.1.1))) machine (word arg.1.1) arg.1.2
        (snapshot arg.1.1) (generator arg.1.1) (publicKey arg.1.1)
        (tape.take (2 * clock arg.1.1)) ((tape.drop (2 * clock arg.1.1)).take (clock arg.1.1 + 1))
        (tape.drop (3 * clock arg.1.1 + 1))
  have hrun : IsPolyTime withScalars (fun arg =>
      optionEncoding (finEquivEncoding (scalar (parameter arg.1.1)))
        (run arg (arg.2.getD []))) := by
    apply hreplay.comp_encoded (f := fun arg : Prepared => ⟨arg,
      ((arg.2.getD []).drop (2 * clock arg.1.1)).take (clock arg.1.1 + 1),
      (arg.2.getD []).drop (3 * clock arg.1.1 + 1)⟩)
    exact hargs
  have hpost := hi.sigma_snd.option_bind_getD (fallback := fun _ => []) (cont := run) hrun
  have hc := isPolyTime_fst input wordEncoding
  have hcount := ((isPolyTime_const withCoins (unaryEncoding 4)).unary_mul
    (hclock.comp_encoded hc)).unary_add (isPolyTime_const withCoins (unaryEncoding 2))
  have hsample := isPPT_replicate_sampleFin_equiv (Oracle := Oracle)
    (count := fun a : Input × Word => 4 * clock a.1 + 2)
    (fun a : Input × Word => scalar (parameter a.1))
    ((horder.comp_encoded hp).comp_encoded hc) (hattempts.comp_encoded hc) hcount
  have hresult := hsample.map (output := wordEncoding) hpost
  have h := ((isPPT_sampleBits_of_isPolyTime (Oracle := Oracle) hclock).pair
    (isPolyTime_input input)).bind hresult
  convert h using 1
  funext a
  simp only [dlogReductionWord, map_eq_pure_bind, bind_assoc, pure_bind]
  rfl

end PolynomialTime

end Cslib.Crypto.Schnorr
