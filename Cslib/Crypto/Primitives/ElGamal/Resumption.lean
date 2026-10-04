/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Oracle
public import Cslib.Foundations.Data.PFunctor.Resumption.Measure

/-! # ElGamal with possibly unbounded sampler implementations -/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor MeasureTheory ProbabilityTheory

/-- Almost-surely terminating effect implementations preserve the chosen-plaintext reduction,
including all adaptive encryption requests. The implementations may have infinite branches;
their returned measures supply the sampler laws. -/
theorem advantage_oracle_liftM_eq_ddh {P Q : PFunctor.{0, 0}}
    [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
    [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
    (μ : (op : Q.A) → Measure (Q.B op))
    (handler : (op : P.A) → Resumption Q (P.B op))
    [∀ op, IsProbabilityMeasure (Resumption.returnedMeasure μ (handler op))]
    {G State : Type} [Group G] {n : ℕ} [NeZero n]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
    (choose : G → (P + PFunctor.mk G (fun _ => G × G)).FreeM (G × G × State))
    (guess : State → G × G → (P + PFunctor.mk G (fun _ => G × G)).FreeM Bool)
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : Resumption.returnedMeasure μ (sample.liftM handler) = uniformOn Set.univ)
    (hcoin : Resumption.returnedMeasure μ (coin.liftM handler) = uniformOn Set.univ) :
    |Game.winProbability (Resumption.returnedMeasure μ
        ((cpaOracleExperiment sample coin g choose guess).liftM handler)) - 1 / 2| =
      Game.advantage
        (Resumption.returnedMeasure μ
          ((ddhReal sample g (ddhOracleReduction sample coin g choose guess)).liftM handler))
        (Resumption.returnedMeasure μ ((ddhRandom sample g
          (ddhOracleReduction sample coin g choose guess)).liftM handler)) := by
  simp only [Resumption.returnedMeasure_liftM] at hsample hcoin ⊢
  exact advantage_oracle_eq_ddh sample coin g choose guess
    (fun op => Resumption.returnedMeasure μ (handler op)) hg hsample hcoin

end Cslib.Crypto.ElGamal
