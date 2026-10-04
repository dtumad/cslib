/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.PFunctor
public import Cslib.Foundations.Data.PFunctor.Basic

/-!
# ElGamal with a chosen-plaintext encryption oracle

The adversary can request fresh encryptions before and after the challenge. Encryption queries
are a summand of an ordinary polynomial functor; `liftM` inlines their public implementation.
The reduction uses the supplied public key throughout, retaining the adversary's private state.

This is the public-encryption oracle elimination from Katz and Lindell (2007), Definition 10.4
and Proposition 10.5, specialized to Construction 10.19. The advantage identity is concrete;
efficient implementation of the inlined handler is a separate computational obligation.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

open PFunctor

universe uA

variable {P : PFunctor.{uA, 0}} {G State : Type} [Group G] {n : ℕ}

/-- Preserve ambient effects and answer every encryption request using fresh sampling. -/
def encryptHandler (sample : P.FreeM (Fin n)) (g pk : G) :
    (op : (P + PFunctor.mk G (fun _ => G × G)).A) →
      P.FreeM ((P + PFunctor.mk G (fun _ => G × G)).B op)
  | .inl op => FreeM.lift op
  | .inr message => encrypt sample g pk message

variable (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
  (choose : G → (P + PFunctor.mk G (fun _ => G × G)).FreeM (G × G × State))
  (guess : State → G × G → (P + PFunctor.mk G (fun _ => G × G)).FreeM Bool)

/-- Chosen-plaintext security with adaptive encryption calls in both adversary phases. -/
def cpaOracleExperiment : P.FreeM Bool := do
  let (pk, _) ← keygen sample g
  let (m₀, m₁, state) ← (choose pk).liftM (encryptHandler sample g pk)
  let bit ← coin
  let ciphertext ← encrypt sample g pk (if bit then m₁ else m₀)
  let answer ← (guess state ciphertext).liftM (encryptHandler sample g pk)
  pure (bit == answer)

/-- The DDH reduction simulates all encryption calls using the challenge public key. -/
def ddhOracleReduction (pk head mask : G) : P.FreeM Bool := do
  let (m₀, m₁, state) ← (choose pk).liftM (encryptHandler sample g pk)
  let bit ← coin
  let answer ← (guess state (head, (if bit then m₁ else m₀) * mask)).liftM
    (encryptHandler sample g pk)
  pure (bit == answer)

/-- Allowing encryption queries before and after the challenge preserves the exact DDH bound. -/
theorem advantage_oracle_eq_ddh [NeZero n] (interp : (op : P.A) → PMF (P.B op))
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : sample.liftM interp = PMF.uniformOfFintype (Fin n))
    (hcoin : coin.liftM interp = PMF.uniformOfFintype Bool) :
    |Game.winProbability ((cpaOracleExperiment sample coin g choose guess).liftM interp) - 1 / 2| =
      Game.advantage
        ((ddhReal sample g (ddhOracleReduction sample coin g choose guess)).liftM interp)
        ((ddhRandom sample g (ddhOracleReduction sample coin g choose guess)).liftM interp) := by
  let choose' (pk : G) : P.FreeM (G × G × (G × State)) := do
    let (m₀, m₁, state) ← (choose pk).liftM (encryptHandler sample g pk)
    pure (m₀, m₁, (pk, state))
  let guess' (state : G × State) (ciphertext : G × G) : P.FreeM Bool :=
    (guess state.2 ciphertext).liftM (encryptHandler sample g state.1)
  have hcpa : cpaExperiment sample coin g choose' guess' =
      cpaOracleExperiment sample coin g choose guess := by
    simp [cpaExperiment, cpaOracleExperiment, choose', guess']
  have hreduce : ddhReduction coin choose' guess' =
      ddhOracleReduction sample coin g choose guess := by
    funext pk head mask
    simp [ddhReduction, ddhOracleReduction, choose', guess']
  simpa only [hcpa, hreduce] using
    advantage_liftM_eq_ddh sample coin g choose' guess' interp hg hsample hcoin

end Cslib.Crypto.ElGamal
