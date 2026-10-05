/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Sampling
public import Cslib.Crypto.Primitives.ElGamal.PolynomialTime

/-!
# Computational security of ElGamal

DDH hardness against uniform machines implies negligible prediction bias for the two-phase
experiment. The reduction's machine is constructed from the adversary phases and multiplication;
its admissibility is not a hypothesis. Challenge sampling belongs to the experiment's effects,
so ideal uniform exponents need not be implemented by a bounded fair-coin machine.
-/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor MeasureTheory ProbabilityTheory Turing.MultiTapePTM Turing.MultiTapeTM
open scoped ENNReal

variable {G State : ℕ → Type} [∀ n, Group (G n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, MeasurableSingletonClass (G n)]
  [∀ n, MeasurableSpace (State n)] [∀ n, MeasurableSingletonClass (State n)]
  {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  {P : ℕ → PFunctor.{0, 0}}
  [∀ n op, MeasurableSpace ((P n).B op)]
  [∀ n op, DiscreteMeasurableSpace ((P n).B op)]
  (μ : ∀ n op, Measure ((P n).B op)) [∀ n op, IsProbabilityMeasure (μ n op)]
  (ambient : ∀ n op, (P n).FreeM ((effects Oracle).B op))
  {order : ℕ → ℕ} [∀ n, NeZero (order n)]
  (sample : ∀ n, (P n).FreeM (Fin (order n))) (g : ∀ n, G n)
  (element : ∀ n, G n ↪ Word) (state : ∀ n, State n ↪ Word)
  (choose : ∀ n, G n → (effects Oracle).FreeM (G n × G n × State n))
  (guess : ∀ n, State n → G n × G n → (effects Oracle).FreeM Bool)

variable
  (hg : ∀ n, Function.Bijective (fun x : Fin (order n) => g n ^ x.val))
  (hsample : ∀ n, FreeM.denote (μ n) (sample n) = uniformOn Set.univ)
  (hcoin : ∀ n, FreeM.denote (μ n)
    ((coin (Oracle := Oracle)).liftM (ambient n)) = uniformOn Set.univ)
  (hchoose : IsPPT (sigmaEncoding unaryEncoding element) wordEncoding (fun input =>
    pairEncoding (element input.1) (pairEncoding (element input.1) (state input.1)) <$>
      choose input.1 input.2))
  (hguess : IsPPT (sigmaEncoding unaryEncoding (fun n =>
    pairEncoding (state n) (pairEncoding (element n) (element n)))) boolEncoding
      (fun input => guess input.1 input.2.1 input.2.2))
  (hmul : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (element n) (element n)))
    (fun input => element input.1 (input.2.1 * input.2.2)))
  (hddh : Game.Secure
    (fun (test : (Σ n, G n × G n × G n) → (effects Oracle).FreeM Bool) n =>
      FreeM.denote (μ n) (ddhReal (sample n) (g n)
        (fun pk head mask => (test ⟨n, pk, head, mask⟩).liftM (ambient n))))
    (fun test n => FreeM.denote (μ n) (ddhRandom (sample n) (g n)
      (fun pk head mask => (test ⟨n, pk, head, mask⟩).liftM (ambient n))))
    (IsPPT (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (element n) (pairEncoding (element n) (element n)))) boolEncoding))

include hg hsample hcoin hchoose hguess hmul hddh

/-- Uniform DDH hardness implies security of the ordinary ElGamal experiment. The private
state encoding, the two adversary machines, and the reduction machine are fixed before the
security parameter. Only the source phases and group multiplication need certificates. -/
theorem negligible_cpa_of_ddh :
    Negligible (fun n => |Game.winProbability (FreeM.denote (μ n)
      (cpaExperiment (sample n) (coin.liftM (ambient n)) (g n)
        (fun pk => (choose n pk).liftM (ambient n))
        (fun saved ciphertext => (guess n saved ciphertext).liftM (ambient n)))) - 1 / 2|) := by
  have h := hddh (fun input => ddhReduction coin (choose input.1) (guess input.1)
    input.2.1 input.2.2.1 input.2.2.2)
    (isPPT_ddhReduction element state choose guess hchoose hguess hmul)
  have heq (n : ℕ) := by
    let : Countable (State n) := (state n).injective.countable
    exact advantage_eq_ddh (μ n) (sample n) (coin.liftM (ambient n)) (g n)
      (fun pk => (choose n pk).liftM (ambient n))
      (fun saved ciphertext => (guess n saved ciphertext).liftM (ambient n))
      (hg n) (hsample n) (hcoin n)
  simpa only [heq, liftM_ddhReduction] using h

/-- Bounded challenge sampling preserves computational security. The adversary's own effects
are unchanged by the cutoff; only the key and challenge exponents contribute to its error.
For binary rejection sampling, `2⁻ⁿ` is a sufficient negligible per-sample error. -/
theorem negligible_cpa_cutoff_of_ddh {Q : ℕ → PFunctor.{0, 0}}
    [∀ n op, MeasurableSpace ((Q n).B op)]
    [∀ n op, DiscreteMeasurableSpace ((Q n).B op)]
    (ν : ∀ n op, Measure ((Q n).B op)) [∀ n op, IsProbabilityMeasure (ν n op)]
    (handler : ∀ n op, OptionT (Q n).FreeM ((P n).B op))
    (hstep : ∀ n op, (FreeM.denote (ν n) (handler n op).run).comap some ≤ μ n op)
    (risk : ∀ n, (P n).A → Bool) (δ : ℕ → ℝ≥0∞)
    (hδ : ∀ n, δ n ≠ ⊤) (herror : Negligible (fun n => (δ n).toReal))
    (hfailure : ∀ n op,
      FreeM.denote (ν n) (handler n op).run {none} ≤ if risk n op then δ n else 0)
    (hdraw : ∀ n, FreeM.queryBoundP (risk n) (sample n) ≤ 1)
    (hambient : ∀ n op, FreeM.queryBoundP (risk n) (ambient n op) = 0) :
    Negligible (fun n => |(FreeM.denote (ν n)
      ((cpaExperiment (sample n) (coin.liftM (ambient n)) (g n)
        (fun pk => (choose n pk).liftM (ambient n))
        (fun saved ciphertext => (guess n saved ciphertext).liftM (ambient n))).liftM
          (handler n)).run {some true}).toReal - 1 / 2|) := by
  let experiment n := cpaExperiment (sample n) (coin.liftM (ambient n)) (g n)
    (fun pk => (choose n pk).liftM (ambient n))
    (fun saved ciphertext => (guess n saved ciphertext).liftM (ambient n))
  have hideal : Negligible (fun n =>
      |Game.winProbability (FreeM.denote (μ n) (experiment n)) - 1 / 2|) :=
    negligible_cpa_of_ddh μ ambient sample g element state choose guess
      hg hsample hcoin hchoose hguess hmul hddh
  change Negligible (fun n => |(FreeM.denote (ν n)
    ((experiment n).liftM (handler n)).run {some true}).toReal - 1 / 2|)
  apply negligible_of_le (hideal.add (herror.add herror)) (fun _ => abs_nonneg _)
  intro n
  have hbound {α : Type} (program : (effects Oracle).FreeM α) :
      FreeM.queryBoundP (risk n) (program.liftM (ambient n)) = 0 := by
    apply le_zero_iff.mp
    simpa only [FreeM.queryBoundP_false] using
      FreeM.queryBoundP_liftM_le (fun _ => false) (risk n) (ambient n)
        (fun op => by simp [hambient]) program
  have hbudget : FreeM.queryBoundP (risk n) (experiment n) ≤ (2 : ℕ) := by
    simpa using queryBoundP_cpaExperiment (risk n) (sample n) (hdraw n)
      (coin.liftM (ambient n)) (hbound _) (g n)
      (fun pk => (choose n pk).liftM (ambient n))
      (fun saved ciphertext => (guess n saved ciphertext).liftM (ambient n)) 0 0
      (fun _ => by simp [hbound]) (fun _ _ => by simp [hbound])
  have happrox := FreeM.abs_toReal_denote_sub_liftM_option_le
    (μ n) (ν n) (handler n) (hstep n) (risk n) (δ n) (hδ n) (hfailure n) _ 2 hbudget {true}
  simp only [Set.image_singleton] at happrox
  have htriangle := abs_sub_le
    (FreeM.denote (ν n) ((experiment n).liftM (handler n)).run {some true}).toReal
    (Game.winProbability (FreeM.denote (μ n) (experiment n))) (1 / 2)
  rw [abs_sub_comm] at happrox
  simp only [Game.winProbability, measureReal_def, Pi.add_apply] at htriangle ⊢
  norm_num only [Nat.cast_ofNat] at happrox
  linarith only [happrox, htriangle]

end Cslib.Crypto.ElGamal
