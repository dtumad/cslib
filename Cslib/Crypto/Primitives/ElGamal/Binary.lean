/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.PolynomialTime.Oracle
public import Cslib.Crypto.Primitives.ElGamal.Sampling
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Closed

/-!
# ElGamal with bounded binary sampling

All executable sampling uses fair bits and a bounded rejection sampler. The encryption oracle
returns optional ciphertexts, allowing the adversary to continue after an exhausted request.
Only key generation and the challenge can abort the whole CPA experiment. The DDH comparison
uses ideal uniform exponents and an actual uniform polynomial-time reduction.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

open PFunctor Turing.MultiTapePTM Turing.MultiTapeTM MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {G State : Type} [Group G]

/-- The executable chosen-plaintext experiment. Both adversary phases may request fresh public
encryptions. A failed query remains visible in its reply; a failed key or challenge aborts. -/
def cpaWordExperiment (element : Computability.Encoding G Bool) (order attempts : ℕ) (g : G)
    (choose : G → (effects Unit).FreeM (G × G × State))
    (guess : State → G × G → (effects Unit).FreeM Bool) :
    (effects Empty).FreeM (Option Bool) :=
  let sample := FreeM.sampleFin
    ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin (Oracle := Empty))
    order order.size attempts
  let handler pk := oracleHandler (fun _ => encryptWord element sample g pk)
  (cpaExperiment (m := OptionT (effects Empty).FreeM) (OptionT.mk sample)
    (monadLift (coin (Oracle := Empty))) g
    (fun pk => monadLift ((fun out => (out.1, out.2.1, (pk, out.2.2))) <$>
      (choose pk).liftM (handler pk)))
    (fun saved ciphertext => monadLift ((guess saved.2 ciphertext).liftM (handler saved.1)))).run

/- The ideal exponent operation is used only to compare experiments. It is never assigned a
bounded fair-coin machine. The public statements below use ordinary uniform measures. -/
private abbrev Challenge (order : ℕ) : PFunctor :=
  PFunctor.mk Bool (fun | false => Bool | true => Fin order)

private instance (order : ℕ) (op : (Challenge order).A) :
    MeasurableSpace ((Challenge order).B op) := by cases op <;> exact inferInstance

private instance (order : ℕ) (op : (Challenge order).A) :
    DiscreteMeasurableSpace ((Challenge order).B op) := by cases op <;> exact inferInstance

private noncomputable def challengeMeasure (order : ℕ) (op : (Challenge order).A) :
    Measure ((Challenge order).B op) := by
  cases op <;> exact uniformOn Set.univ

private instance (order : ℕ) [NeZero order] (op : (Challenge order).A) :
    IsProbabilityMeasure (challengeMeasure order op) := by
  cases op <;> exact inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

private def embedCoins (order : ℕ) (op : (effects Empty).A) :
    (Challenge order).FreeM ((effects Empty).B op) :=
  match op with
  | .inl _ => FreeM.lift (P := Challenge order) false
  | .inr (port, _) => port.elim

private def implementChallenge (order attempts : ℕ) (op : (Challenge order).A) :
    OptionT (effects Empty).FreeM ((Challenge order).B op) :=
  match op with
  | false => monadLift (coin (Oracle := Empty))
  | true => OptionT.mk (FreeM.sampleFin
    ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin) order order.size attempts)

private theorem liftM_embedCoins {α : Type} (order attempts : ℕ)
    (program : (effects Empty).FreeM α) :
    (program.liftM (embedCoins order)).liftM (implementChallenge order attempts) =
      (monadLift program : OptionT (effects Empty).FreeM α) := by
  induction program with
  | pure value => rfl
  | lift_bind op cont ih =>
    cases op with
    | inl token =>
      cases token
      simp only [FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift, embedCoins,
        implementChallenge, ih]
      rfl
    | inr request => exact request.1.elim

variable [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

private theorem denote_embedCoins {α : Type} [MeasurableSpace α] (order : ℕ)
    (program : (effects Empty).FreeM α) :
    FreeM.denote (challengeMeasure order) (program.liftM (embedCoins order)) =
      FreeM.denote coinMeasure program := by
  rw [FreeM.denote_liftM]
  congr 1
  funext op
  cases op with
  | inl token => exact FreeM.denote_lift (P := Challenge order) _ false
  | inr request => exact request.1.elim

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
private theorem queryBoundP_embedCoins {α : Type} (order : ℕ)
    (program : (effects Empty).FreeM α) :
    FreeM.queryBoundP id (program.liftM (embedCoins order)) = 0 := by
  apply le_zero_iff.mp
  simpa only [FreeM.queryBoundP_false] using FreeM.queryBoundP_liftM_le
    (fun _ => false) id (embedCoins order) (by
      intro op
      cases op with
      | inl _ => simp [embedCoins, FreeM.queryBoundP_lift (P := Challenge order)]
      | inr request => exact request.1.elim) program

private theorem implementChallenge_comap (order attempts : ℕ) (op : (Challenge order).A) :
    (FreeM.denote coinMeasure (implementChallenge order attempts op).run).comap some ≤
      challengeMeasure order op := by
  cases op with
  | false =>
    simp only [implementChallenge, OptionT.run_monadLift, monadLift_self,
      ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete, denote_coin]
    rw [Option.measurableEmbedding_some.comap_map]
    rfl
  | true =>
    exact FreeM.comap_denote_sampleFin_le coinMeasure _ denote_finTwo_coin _ _ _
      (Nat.le_of_lt (Nat.lt_size_self order))

private theorem implementChallenge_failure (order attempts : ℕ) [NeZero order]
    (op : (Challenge order).A) :
    FreeM.denote coinMeasure (implementChallenge order attempts op).run {none} ≤
      if op then (2 : ℝ≥0∞)⁻¹ ^ attempts else 0 := by
  cases op with
  | false =>
    simp only [implementChallenge, OptionT.run_monadLift, monadLift_self,
      ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete, denote_coin]
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
      show (some : Bool → Option Bool) ⁻¹' {none} = ∅ by ext bit; simp]
    simp
  | true =>
    exact FreeM.denote_sampleFin_size_none_le coinMeasure _ denote_finTwo_coin order attempts

variable [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]

/-- Bounded key and challenge sampling adds at most `2 * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` to the concrete DDH bound.
The two phases may already contain arbitrary public encryption simulations. Their internal
sampling is identical in both comparison games and contributes no additional approximation. -/
theorem advantage_binary_le_ddh (order attempts : ℕ) [NeZero order] (g : G)
    (choose : G → (effects Empty).FreeM (G × G × State))
    (guess : State → G × G → (effects Empty).FreeM Bool)
    (hg : Function.Bijective (fun x : Fin order => g ^ x.val)) :
    let sample := FreeM.sampleFin
      ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin (Oracle := Empty))
      order order.size attempts
    let test := ddhReduction coin choose guess
    |(FreeM.denote coinMeasure
      (cpaExperiment (m := OptionT (effects Empty).FreeM) (OptionT.mk sample)
        (monadLift (coin (Oracle := Empty))) g
        (fun pk => monadLift (choose pk))
        (fun saved ciphertext => monadLift (guess saved ciphertext))).run {some true}).toReal -
          1 / 2| ≤
      Game.advantage
        ((uniformOn (Set.univ : Set (Fin order))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin order))).bind (fun r =>
            FreeM.denote coinMeasure (test (g ^ x.val) (g ^ r.val) (g ^ (x.val * r.val))))))
        ((uniformOn (Set.univ : Set (Fin order))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin order))).bind (fun r =>
            (uniformOn (Set.univ : Set (Fin order))).bind (fun z =>
              FreeM.denote coinMeasure (test (g ^ x.val) (g ^ r.val) (g ^ z.val)))))) +
        2 * (2⁻¹ : ℝ) ^ attempts := by
  let : Fintype G := Fintype.ofEquiv (Fin order) (Equiv.ofBijective _ hg)
  let draw := FreeM.lift (P := Challenge order) true
  let bit := (coin (Oracle := Empty)).liftM (embedCoins order)
  let choose' pk := (choose pk).liftM (embedCoins order)
  let guess' saved ciphertext := (guess saved ciphertext).liftM (embedCoins order)
  let ideal := cpaExperiment draw bit g choose' guess'
  have hcost : FreeM.queryBoundP id ideal ≤ (2 : ℕ) := by
    simpa using queryBoundP_cpaExperiment id draw
      (by simp [draw, FreeM.queryBoundP_lift (P := Challenge order)]) bit
      (queryBoundP_embedCoins order _) g choose' guess' 0 0
      (fun _ => (queryBoundP_embedCoins order _).le)
      (fun _ _ => (queryBoundP_embedCoins order _).le)
  have happrox := FreeM.abs_toReal_denote_sub_liftM_option_le
    (challengeMeasure order) coinMeasure (implementChallenge order attempts)
    (implementChallenge_comap order attempts) id ((2 : ℝ≥0∞)⁻¹ ^ attempts) (by finiteness)
    (implementChallenge_failure order attempts) ideal 2 hcost {true}
  have hideal := advantage_eq_ddh (challengeMeasure order) draw bit g choose' guess' hg
    (FreeM.denote_lift (challengeMeasure order) true)
    (denote_embedCoins order coin |>.trans denote_coin)
  have hreal (test : G → G → G → (effects Empty).FreeM Bool) :
      FreeM.denote (challengeMeasure order)
        (ddhReal draw g (fun pk head mask => (test pk head mask).liftM (embedCoins order))) =
        (uniformOn (Set.univ : Set (Fin order))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin order))).bind (fun r =>
            FreeM.denote coinMeasure (test (g ^ x.val) (g ^ r.val) (g ^ (x.val * r.val))))) := by
    simp [ddhReal, draw, FreeM.denote_bind_of_discrete,
      FreeM.denote_lift (challengeMeasure order), challengeMeasure, denote_embedCoins]
  have hrandom (test : G → G → G → (effects Empty).FreeM Bool) :
      FreeM.denote (challengeMeasure order)
        (ddhRandom draw g (fun pk head mask => (test pk head mask).liftM (embedCoins order))) =
        (uniformOn (Set.univ : Set (Fin order))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin order))).bind (fun r =>
            (uniformOn (Set.univ : Set (Fin order))).bind (fun z =>
              FreeM.denote coinMeasure (test (g ^ x.val) (g ^ r.val) (g ^ z.val))))) := by
    simp [ddhRandom, draw, FreeM.denote_bind_of_discrete,
      FreeM.denote_lift (challengeMeasure order), challengeMeasure, denote_embedCoins]
  have hreduce : ddhReduction bit choose' guess' = fun pk head mask =>
      (ddhReduction coin choose guess pk head mask).liftM (embedCoins order) := by
    funext pk head mask
    exact (liftM_ddhReduction _ _ _ _ _ _ _).symm
  rw [hreduce, hreal, hrandom] at hideal
  have htriangle := abs_sub_le
    (FreeM.denote coinMeasure (ideal.liftM (implementChallenge order attempts)).run
      {some true}).toReal
    (Game.winProbability (FreeM.denote (challengeMeasure order) ideal)) (1 / 2)
  rw [show Game.winProbability (FreeM.denote (challengeMeasure order) ideal) =
    (FreeM.denote (challengeMeasure order) ideal {true}).toReal from rfl] at htriangle
  rw [abs_sub_comm] at happrox
  simp only [Set.image_singleton] at happrox
  have hfinal := htriangle.trans (add_le_add happrox (le_of_eq hideal))
  simpa only [ideal, liftM_cpaExperiment, draw,
    FreeM.liftM_lift (implementChallenge order attempts), bit, choose', guess',
    liftM_embedCoins, implementChallenge, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, Nat.cast_ofNat, add_comm] using hfinal

end Cslib.Crypto.ElGamal
