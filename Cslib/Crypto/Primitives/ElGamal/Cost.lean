/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Oracle
public import Cslib.Foundations.Data.PFunctor.Free.Cost

/-!
# Sampling budgets for ElGamal experiments

The challenge bit is exact, so only the selected ambient operations and encryption requests
contribute to the finite-sampling budget. The games also pay for generating their challenges.
-/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor

variable {P : PFunctor.{0, 0}} {G State : Type} [Group G] {n : ℕ}

/-- The ordinary experiment uses its two adversary phases and two exponent samples. -/
theorem queryBoundP_cpaExperiment (select : P.A → Bool) (sample : P.FreeM (Fin n))
    (hsample : FreeM.queryBoundP select sample ≤ 1) (coin : P.FreeM Bool)
    (hcoin : FreeM.queryBoundP select coin = 0) (g : G)
    (choose : G → P.FreeM (G × G × State)) (guess : State → G × G → P.FreeM Bool)
    (qChoose qGuess : ℕ)
    (hchoose : ∀ pk, FreeM.queryBoundP select (choose pk) ≤ qChoose)
    (hguess : ∀ state ciphertext, FreeM.queryBoundP select (guess state ciphertext) ≤ qGuess) :
    FreeM.queryBoundP select (cpaExperiment sample coin g choose guess) ≤
      qChoose + qGuess + 2 := by
  simp only [cpaExperiment, keygen, encrypt, bind_assoc, pure_bind]
  apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess + 1) ?_).trans
  · exact (add_le_add hsample le_rfl).trans_eq (by ring)
  · intro secret
    apply (FreeM.queryBoundP_bind_le select _ _ (qGuess + 1) ?_).trans
    · exact (add_le_add (hchoose _) le_rfl).trans_eq (by ring)
    · rintro ⟨m₀, m₁, state⟩
      apply (FreeM.queryBoundP_bind_le select _ _ (qGuess + 1) ?_).trans
      · simp [hcoin]
      · intro bit
        apply (FreeM.queryBoundP_bind_le select _ _ qGuess ?_).trans
        · exact (add_le_add hsample le_rfl).trans_eq (add_comm _ _)
        · intro nonce
          rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
          exact hguess state _

/-- Every encryption request uses one scalar sample. -/
theorem queryBoundP_liftM_encryptHandler_le (select : P.A → Bool) (sample : P.FreeM (Fin n))
    (hsample : FreeM.queryBoundP select sample ≤ 1) (g pk : G) {α : Type}
    (program : (P + PFunctor.mk G (fun _ => G × G)).FreeM α) :
    FreeM.queryBoundP select (program.liftM (encryptHandler sample g pk)) ≤
      FreeM.queryBoundP (fun op : (P + PFunctor.mk G (fun _ => G × G)).A =>
        match op with | .inl op => select op | .inr _ => true) program := by
  apply FreeM.queryBoundP_liftM_le
  rintro (op | message)
  · simp [encryptHandler]
  · simpa only [encryptHandler, encrypt, ← map_eq_pure_bind, FreeM.queryBoundP_map,
      ↓reduceIte] using hsample

variable (select : P.A → Bool) (sample : P.FreeM (Fin n))
  (hsample : FreeM.queryBoundP select sample ≤ 1) (coin : P.FreeM Bool)
  (hcoin : FreeM.queryBoundP select coin = 0) (g : G)
  (choose : G → (P + PFunctor.mk G (fun _ => G × G)).FreeM (G × G × State))
  (guess : State → G × G → (P + PFunctor.mk G (fun _ => G × G)).FreeM Bool)
  (qChoose qGuess : ℕ)
  (hchoose : ∀ pk, FreeM.queryBoundP (fun op : (P + PFunctor.mk G (fun _ => G × G)).A =>
    match op with | .inl op => select op | .inr _ => true) (choose pk) ≤ qChoose)
  (hguess : ∀ state ciphertext,
    FreeM.queryBoundP (fun op : (P + PFunctor.mk G (fun _ => G × G)).A =>
      match op with | .inl op => select op | .inr _ => true) (guess state ciphertext) ≤ qGuess)

include hsample hcoin hchoose hguess

/-- The CPA game pays for both adaptive phases, the key, and the challenge encryption. -/
theorem queryBoundP_cpaOracleExperiment :
    FreeM.queryBoundP select (cpaOracleExperiment sample coin g choose guess) ≤
      qChoose + qGuess + 2 := by
  let choose' pk := (fun out => (out.1, out.2.1, pk, out.2.2)) <$>
    (choose pk).liftM (encryptHandler sample g pk)
  let guess' (saved : G × State) ciphertext :=
    (guess saved.2 ciphertext).liftM (encryptHandler sample g saved.1)
  have h := queryBoundP_cpaExperiment select sample hsample coin hcoin g choose' guess'
    qChoose qGuess
    (fun pk => by
      simpa only [choose', FreeM.queryBoundP_map] using
        (queryBoundP_liftM_encryptHandler_le select sample hsample g pk _).trans (hchoose pk))
    (fun saved ciphertext =>
      (queryBoundP_liftM_encryptHandler_le select sample hsample g saved.1 _).trans
        (hguess saved.2 ciphertext))
  simpa only [cpaExperiment, cpaOracleExperiment, choose', guess', bind_map_left] using h

/-- The reduction needs no scalar samples beyond those used to answer the adversary's calls. -/
theorem queryBoundP_ddhOracleReduction (pk head mask : G) :
    FreeM.queryBoundP select (ddhOracleReduction sample coin g choose guess pk head mask) ≤
      qChoose + qGuess := by
  unfold ddhOracleReduction
  apply (FreeM.queryBoundP_bind_le select _ _ qGuess ?_).trans
  · exact add_le_add
      ((queryBoundP_liftM_encryptHandler_le select sample hsample g pk _).trans (hchoose pk))
      le_rfl
  · rintro ⟨m₀, m₁, state⟩
    apply (FreeM.queryBoundP_bind_le select _ _ qGuess ?_).trans
    · simp [hcoin]
    · intro bit
      rw [← map_eq_pure_bind, FreeM.queryBoundP_map]
      exact (queryBoundP_liftM_encryptHandler_le select sample hsample g pk _).trans (hguess _ _)

/-- The real DDH game additionally draws its two independent exponents. -/
theorem queryBoundP_ddhReal_oracle :
    FreeM.queryBoundP select
      (ddhReal sample g (ddhOracleReduction sample coin g choose guess)) ≤
        qChoose + qGuess + 2 := by
  unfold ddhReal
  apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess + 1) ?_).trans
  · exact (add_le_add hsample le_rfl).trans_eq (by ring)
  · intro secret
    apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess) ?_).trans
    · exact (add_le_add hsample le_rfl).trans_eq (by ring)
    · intro nonce
      exact queryBoundP_ddhOracleReduction select sample hsample coin hcoin g choose guess
        qChoose qGuess hchoose hguess _ _ _

/-- The random DDH game draws a third exponent for its independent mask. -/
theorem queryBoundP_ddhRandom_oracle :
    FreeM.queryBoundP select
      (ddhRandom sample g (ddhOracleReduction sample coin g choose guess)) ≤
        qChoose + qGuess + 3 := by
  unfold ddhRandom
  apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess + 2) ?_).trans
  · exact (add_le_add hsample le_rfl).trans_eq (by ring)
  · intro secret
    apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess + 1) ?_).trans
    · exact (add_le_add hsample le_rfl).trans_eq (by ring)
    · intro nonce
      apply (FreeM.queryBoundP_bind_le select _ _ (qChoose + qGuess) ?_).trans
      · exact (add_le_add hsample le_rfl).trans_eq (by ring)
      · intro mask
        exact queryBoundP_ddhOracleReduction select sample hsample coin hcoin g choose guess
          qChoose qGuess hchoose hguess _ _ _

end Cslib.Crypto.ElGamal
