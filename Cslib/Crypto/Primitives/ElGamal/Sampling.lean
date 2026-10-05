/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Random.Approximation

/-! # ElGamal's DDH reduction with bounded sampling -/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {P Q : PFunctor.{0, 0}} {G State : Type} [Group G] {n : ℕ} [NeZero n]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  (ν : (op : Q.A) → Measure (Q.B op)) [∀ op, IsProbabilityMeasure (ν op)]
  [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]

/-- Local sampling cutoffs give an explicit advantage bound for the complete implemented
CPA and DDH games. The error pays for both adversary phases and all challenge generation. -/
theorem advantage_oracle_le_ddh_cutoff
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (FreeM.denote ν (handler op).run).comap some ≤ μ op)
    (risk : P.A → Bool) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (hfailure : ∀ op, FreeM.denote ν (handler op).run {none} ≤ if risk op then δ else 0)
    (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
    (choose : G → (P + PFunctor.mk G (fun _ => G × G)).FreeM (G × G × State))
    (guess : State → G × G → (P + PFunctor.mk G (fun _ => G × G)).FreeM Bool)
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (hcoin : FreeM.denote μ coin = uniformOn Set.univ)
    (hdraw : FreeM.queryBoundP risk sample ≤ 1) (hbit : FreeM.queryBoundP risk coin = 0)
    (qChoose qGuess : ℕ)
    (hchoose : ∀ pk, FreeM.queryBoundP (fun op : (P + PFunctor.mk G (fun _ => G × G)).A =>
      match op with | .inl op => risk op | .inr _ => true) (choose pk) ≤ qChoose)
    (hguess : ∀ state ciphertext,
      FreeM.queryBoundP (fun op : (P + PFunctor.mk G (fun _ => G × G)).A =>
        match op with | .inl op => risk op | .inr _ => true) (guess state ciphertext) ≤ qGuess) :
    let cpa := (FreeM.denote ν
      ((cpaOracleExperiment sample coin g choose guess).liftM handler).run {some true}).toReal
    let real := (FreeM.denote ν ((ddhReal sample g
      (ddhOracleReduction sample coin g choose guess)).liftM handler).run {some true}).toReal
    let random := (FreeM.denote ν ((ddhRandom sample g
      (ddhOracleReduction sample coin g choose guess)).liftM handler).run {some true}).toReal
    |cpa - 1 / 2| ≤ |real - random| + (3 * (qChoose + qGuess) + 7) * δ.toReal := by
  let cpa := cpaOracleExperiment sample coin g choose guess
  let real := ddhReal sample g (ddhOracleReduction sample coin g choose guess)
  let random := ddhRandom sample g (ddhOracleReduction sample coin g choose guess)
  have hcpa : FreeM.queryBoundP risk cpa ≤ ((qChoose + qGuess + 2 : ℕ) : ℕ∞) := by
    simpa [cpa] using queryBoundP_cpaOracleExperiment risk sample hdraw coin hbit g choose guess
      qChoose qGuess hchoose hguess
  have hreal : FreeM.queryBoundP risk real ≤ ((qChoose + qGuess + 2 : ℕ) : ℕ∞) := by
    simpa [real] using queryBoundP_ddhReal_oracle risk sample hdraw coin hbit g choose guess
      qChoose qGuess hchoose hguess
  have hrandom : FreeM.queryBoundP risk random ≤ ((qChoose + qGuess + 3 : ℕ) : ℕ∞) := by
    simpa [random] using queryBoundP_ddhRandom_oracle risk sample hdraw coin hbit g choose guess
      qChoose qGuess hchoose hguess
  have happrox := FreeM.abs_toReal_denote_sub_liftM_option_le (α := Bool)
    μ ν handler hstep risk δ hδ hfailure
  have h₁ := happrox cpa _ hcpa {true}
  have h₂ := happrox real _ hreal {true}
  have h₃ := happrox random _ hrandom {true}
  simp only [Set.image_singleton, Nat.cast_add, Nat.cast_ofNat] at h₁ h₂ h₃
  have hsecurity := advantage_oracle_eq_ddh sample coin g choose guess μ hg hsample hcoin
  change |(FreeM.denote μ cpa {true}).toReal - 1 / 2| =
    |(FreeM.denote μ real {true}).toReal - (FreeM.denote μ random {true}).toReal| at hsecurity
  have hhop₁ := abs_sub_le
    (FreeM.denote ν (cpa.liftM handler).run {some true}).toReal
    (FreeM.denote μ cpa {true}).toReal (1 / 2)
  have hhop₂ := abs_sub_le (FreeM.denote μ real {true}).toReal
    (FreeM.denote ν (real.liftM handler).run {some true}).toReal
    (FreeM.denote μ random {true}).toReal
  have hhop₃ := abs_sub_le (FreeM.denote ν (real.liftM handler).run {some true}).toReal
    (FreeM.denote ν (random.liftM handler).run {some true}).toReal
    (FreeM.denote μ random {true}).toReal
  rw [abs_sub_comm (FreeM.denote ν (cpa.liftM handler).run {some true}).toReal
      (FreeM.denote μ cpa {true}).toReal, hsecurity] at hhop₁
  rw [abs_sub_comm (FreeM.denote ν (random.liftM handler).run {some true}).toReal] at hhop₃
  change |(FreeM.denote ν (cpa.liftM handler).run {some true}).toReal - 1 / 2| ≤
    |(FreeM.denote ν (real.liftM handler).run {some true}).toReal -
      (FreeM.denote ν (random.liftM handler).run {some true}).toReal| + _
  nlinarith only [h₁, h₂, h₃, hhop₁, hhop₂, hhop₃]

end Cslib.Crypto.ElGamal
