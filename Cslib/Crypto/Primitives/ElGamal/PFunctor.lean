/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal
public import Cslib.Crypto.Game
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Bind
public import Cslib.Foundations.MeasureTheory.Uniform

/-!
# ElGamal over polynomial effects

The same free programs can be interpreted with different sampling and adversary handlers.
The security identity needs only the two sampler laws; it makes no efficiency assumption about
arbitrary Lean functions in an adversary. Computational security additionally requires a
machine certificate for the concrete reduction.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

open PFunctor MeasureTheory ProbabilityTheory

universe uA v

section Naturality

variable {P : PFunctor.{uA, 0}} {m : Type → Type v} [Monad m] [LawfulMonad m]
  {G State : Type} [Group G] {n : ℕ}
  (interp : (op : P.A) → m (P.B op))
  (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
  (choose : G → P.FreeM (G × G × State)) (guess : State → G × G → P.FreeM Bool)

@[simp]
theorem liftM_cpaExperiment :
    (cpaExperiment sample coin g choose guess).liftM interp =
      cpaExperiment (sample.liftM interp) (coin.liftM interp) g
        (fun pk => (choose pk).liftM interp) (fun state ciphertext =>
          (guess state ciphertext).liftM interp) := by
  simp [cpaExperiment, keygen, encrypt, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhReduction (pk head mask : G) :
    (ddhReduction coin choose guess pk head mask).liftM interp =
      ddhReduction (coin.liftM interp) (fun pk => (choose pk).liftM interp)
        (fun state ciphertext => (guess state ciphertext).liftM interp) pk head mask := by
  simp [ddhReduction, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhReal (test : G → G → G → P.FreeM Bool) :
    (ddhReal sample g test).liftM interp =
      ddhReal (sample.liftM interp) g (fun pk head mask => (test pk head mask).liftM interp) := by
  simp [ddhReal, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhRandom (test : G → G → G → P.FreeM Bool) :
    (ddhRandom sample g test).liftM interp =
      ddhRandom (sample.liftM interp) g (fun pk head mask => (test pk head mask).liftM interp) := by
  simp [ddhRandom, FreeM.liftM_bind]

end Naturality

section Measures

variable {P : PFunctor.{uA, 0}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  {G State : Type} [Group G] {n : ℕ}
  [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
  (choose : G → P.FreeM (G × G × State)) (guess : State → G × G → P.FreeM Bool)

omit [∀ op, IsProbabilityMeasure (μ op)] in
/-- Interpreting the real DDH reduction gives exactly the encryption experiment. -/
theorem denote_ddhReal_eq_cpaExperiment [Countable G] :
    FreeM.denote μ (ddhReal sample g (ddhReduction coin choose guess)) =
      FreeM.denote μ (cpaExperiment sample coin g choose guess) := by
  simp only [ddhReal, ddhReduction, cpaExperiment, keygen, encrypt, bind_assoc, pure_bind,
    FreeM.denote_bind_of_discrete, FreeM.denote_pure]
  apply congrArg (Measure.bind (FreeM.denote μ sample))
  funext x
  rw [Measure.bind_comm (μ := FreeM.denote μ sample) (ν := FreeM.denote μ (choose (g ^ x.val)))
    Measurable.of_discrete]
  apply congrArg (Measure.bind (FreeM.denote μ (choose (g ^ x.val))))
  funext messages
  rw [Measure.bind_comm (μ := FreeM.denote μ sample) (ν := FreeM.denote μ coin)
    Measurable.of_discrete]
  simp only [pow_mul]

omit μ sample coin choose guess in
/-- Multiplication by a fixed message preserves a uniform group element. -/
theorem uniform_mask [Finite G]
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val)) (message : G) :
    (uniformOn (Set.univ : Set (Fin n))).map (fun x => message * g ^ x.val) =
      uniformOn Set.univ :=
  map_uniformOn_univ
    ((Equiv.ofBijective (fun x : Fin n => g ^ x.val) hg).trans (Equiv.mulLeft message))

omit μ sample coin choose guess in
private theorem uniform_mask_bind [Finite G]
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    {α : Type} [MeasurableSpace α] (message : G) (f : G → Measure α) :
    (uniformOn (Set.univ : Set (Fin n))).bind (fun x => f (message * g ^ x.val)) =
      (uniformOn (Set.univ : Set G)).bind f := by
  change (uniformOn (Set.univ : Set (Fin n))).bind
    (f ∘ (fun x => message * g ^ x.val)) = _
  rw [← Measure.bind_map _ Measurable.of_discrete Measurable.of_discrete,
    uniform_mask g hg]

private theorem fair_guess (guess : Measure Bool) [IsProbabilityMeasure guess] :
    (uniformOn (Set.univ : Set Bool)).bind (fun bit =>
      guess.bind fun answer => Measure.dirac (bit == answer)) = uniformOn Set.univ := by
  rw [Measure.bind_comm Measurable.of_discrete]
  have h (answer : Bool) :
      (uniformOn (Set.univ : Set Bool)).bind (fun bit => Measure.dirac (bit == answer)) =
        uniformOn Set.univ := by
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
    exact map_uniformOn_univ (Equiv.ofBijective (fun bit => bit == answer)
      (by cases answer <;> decide))
  simp_rw [h]
  rw [Measure.bind_const, measure_univ, one_smul]

/-- The random DDH triple makes the reduction's answer uniform, regardless of the adversary. -/
theorem denote_ddhRandom_eq_uniform [NeZero n]
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (hcoin : FreeM.denote μ coin = uniformOn Set.univ) :
    FreeM.denote μ (ddhRandom sample g (ddhReduction coin choose guess)) =
      uniformOn Set.univ := by
  let : Fintype G := Fintype.ofEquiv (Fin n) (Equiv.ofBijective _ hg)
  have h (pk head : G) :
      (uniformOn (Set.univ : Set (Fin n))).bind (fun z =>
        FreeM.denote μ (ddhReduction coin choose guess pk head (g ^ z.val))) =
          uniformOn Set.univ := by
    simp only [ddhReduction, FreeM.denote_bind_of_discrete, FreeM.denote_pure, hcoin]
    rw [Measure.bind_comm Measurable.of_discrete]
    calc
      _ = (FreeM.denote μ (choose pk)).bind (fun _ => uniformOn Set.univ) := by
        apply congrArg (Measure.bind (FreeM.denote μ (choose pk)))
        funext messages
        rw [Measure.bind_comm Measurable.of_discrete]
        trans (uniformOn (Set.univ : Set Bool)).bind (fun bit =>
          (uniformOn (Set.univ : Set G)).bind fun mask =>
            (FreeM.denote μ (guess messages.2.2 (head, mask))).bind
              fun answer => Measure.dirac (bit == answer))
        · apply congrArg (Measure.bind (uniformOn (Set.univ : Set Bool)))
          funext bit
          exact uniform_mask_bind g hg (if bit then messages.2.1 else messages.1)
            (fun mask => (FreeM.denote μ (guess messages.2.2 (head, mask))).bind
              fun answer => Measure.dirac (bit == answer))
        · rw [Measure.bind_comm Measurable.of_discrete]
          simp_rw [fair_guess]
          rw [Measure.bind_const, measure_univ, one_smul]
      _ = _ := by rw [Measure.bind_const, measure_univ, one_smul]
  simp only [ddhRandom, FreeM.denote_bind_of_discrete, hsample, h]
  rw [Measure.bind_const, measure_univ, one_smul, Measure.bind_const, measure_univ, one_smul]

/-- ElGamal's prediction bias is the distinguishing advantage of its concrete DDH reduction.
The adversary's private state is countable; the operation handlers are arbitrary probability
measures on discrete answer spaces. The bias convention is not doubled. -/
theorem advantage_eq_ddh [NeZero n]
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (hcoin : FreeM.denote μ coin = uniformOn Set.univ) :
    |Game.winProbability (FreeM.denote μ (cpaExperiment sample coin g choose guess)) - 1 / 2| =
      Game.advantage
        (FreeM.denote μ (ddhReal sample g (ddhReduction coin choose guess)))
        (FreeM.denote μ (ddhRandom sample g (ddhReduction coin choose guess))) := by
  let : Fintype G := Fintype.ofEquiv (Fin n) (Equiv.ofBijective _ hg)
  rw [denote_ddhRandom_eq_uniform μ sample coin g choose guess hg hsample hcoin,
    Game.advantage_uniform_bool, denote_ddhReal_eq_cpaExperiment]

end Measures

end Cslib.Crypto.ElGamal
