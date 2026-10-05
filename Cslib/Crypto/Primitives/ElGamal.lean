/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# ElGamal encryption and its DDH reduction

The algorithms and two-stage experiment use ordinary monad operations, so they specialize
directly to `PFunctor.FreeM`. Sampling and the two adversary phases are explicit arguments.
The reduction uses only a fair challenge bit in addition to its adversary's randomness.

We use multiplicative notation and exponents in `Fin n`. The security theorem assumes that
`i ↦ g ^ i.val` is a bijection onto the group; prime order is not needed for ElGamal.

References: Katz and Lindell, *Introduction to Modern Cryptography* (2007), Construction 10.19
and Theorem 10.20. Adapted from VCVio's ElGamal development. Measure semantics and the
concrete security reduction are in `ElGamal.PFunctor`.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

variable {G : Type} [Group G] {n : ℕ} {State : Type}

section Programs

variable {m : Type → Type*} [Monad m]

/-- Choose a secret exponent and its public group element. -/
def keygen (sample : m (Fin n)) (g : G) : m (G × Fin n) := do
  let x ← sample
  pure (g ^ x.val, x)

/-- Encrypt a group element with an independently sampled ephemeral exponent. -/
def encrypt (sample : m (Fin n)) (g pk message : G) : m (G × G) := do
  let r ← sample
  pure (g ^ r.val, message * pk ^ r.val)

/-- Remove the Diffie--Hellman mask using the secret exponent. -/
def decrypt (x : Fin n) (ciphertext : G × G) : G :=
  ciphertext.2 / ciphertext.1 ^ x.val

/-- The two-stage chosen-message experiment. The private state connects the adversary's phases. -/
def cpaExperiment (sample : m (Fin n)) (coin : m Bool) (g : G)
    (choose : G → m (G × G × State)) (guess : State → G × G → m Bool) : m Bool := do
  let (pk, _) ← keygen sample g
  let (m₀, m₁, state) ← choose pk
  let bit ← coin
  let ciphertext ← encrypt sample g pk (if bit then m₁ else m₀)
  let answer ← guess state ciphertext
  pure (bit == answer)

/-- The ElGamal reduction applied to a candidate Diffie--Hellman triple. -/
def ddhReduction (coin : m Bool)
    (choose : G → m (G × G × State)) (guess : State → G × G → m Bool)
    (pk head mask : G) : m Bool := do
  let (m₀, m₁, state) ← choose pk
  let bit ← coin
  let answer ← guess state (head, (if bit then m₁ else m₀) * mask)
  pure (bit == answer)

/-- A real Diffie--Hellman triple. -/
def ddhReal (sample : m (Fin n)) (g : G) (test : G → G → G → m Bool) : m Bool := do
  let x ← sample
  let r ← sample
  test (g ^ x.val) (g ^ r.val) (g ^ (x.val * r.val))

/-- The comparison experiment uses an independent uniform group element in the third coordinate. -/
def ddhRandom (sample : m (Fin n)) (g : G) (test : G → G → G → m Bool) : m Bool := do
  let x ← sample
  let r ← sample
  let z ← sample
  test (g ^ x.val) (g ^ r.val) (g ^ z.val)

end Programs

/-- Every pair of key and encryption exponents decrypts correctly. -/
@[simp]
theorem decrypt_encrypt (g message : G) (x r : Fin n) :
    decrypt x (g ^ r.val, message * (g ^ x.val) ^ r.val) = message := by
  simp [decrypt, ← pow_mul, Nat.mul_comm]

/-- Honest key generation, encryption, and decryption return the original message. Both
samples remain in the program, so this also preserves their state, cost, and possible failure. -/
theorem decrypt_keygen_encrypt {m : Type → Type*} [Monad m] [LawfulMonad m]
    (sample : m (Fin n)) (g message : G) :
    (do
      let (pk, secret) ← keygen sample g
      let ciphertext ← encrypt sample g pk message
      pure (decrypt secret ciphertext)) =
    (do
      let _ ← sample
      let _ ← sample
      pure message) := by
  simp [keygen, encrypt]

end Cslib.Crypto.ElGamal
