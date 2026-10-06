/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Assumptions.DDH
public import Mathlib.Algebra.Group.Basic

/-!
# ElGamal encryption

ElGamal encryption in a group `G` with generator `g` and exponents in `Fin n`: the secret key is an
exponent `x` with public key `g ^ x`, and a message `m` is encrypted as `(g ^ r, m * pk ^ r)` for a
fresh exponent `r`. The algorithms and the chosen-plaintext experiment are programs in an arbitrary
monad `m`, given a sampler of exponents and a challenge coin, so they can be run, analysed for
their possible outputs, or given a probabilistic semantics. Decryption is correct as an equation of
programs in every lawful monad (`decrypt_keygen_encrypt`).

`ddhReduction` turns a chosen-plaintext adversary into a DDH test; its analysis is in
`Cslib.Crypto.Primitives.ElGamal.Security`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

variable {m : Type → Type*} [Monad m] {G : Type} [Group G] {n : ℕ} {State : Type}

/-- Sample a secret exponent and return the public key with it. -/
def keygen (sample : m (Fin n)) (g : G) : m (G × Fin n) := do
  let x ← sample
  pure (g ^ x.val, x)

/-- Encrypt a message under a public key with a fresh exponent. -/
def encrypt (sample : m (Fin n)) (g pk message : G) : m (G × G) := do
  let r ← sample
  pure (g ^ r.val, message * pk ^ r.val)

/-- Remove the mask from a ciphertext using the secret exponent. -/
def decrypt (x : Fin n) (ciphertext : G × G) : G :=
  ciphertext.2 / ciphertext.1 ^ x.val

/-- The challenge phase under the public key `pk`: the adversary chooses two messages, sees an
encryption of one of them selected by a fair coin, and wins by guessing which. Its two phases share
a private state. -/
def challenge (coin : m Bool) (choose : G → m (G × G × State))
    (guess : State → G × G → m Bool) (pk : G) (encrypt : G → m (G × G)) : m Bool := do
  let (m₀, m₁, state) ← choose pk
  let bit ← coin
  let answer ← guess state (← encrypt (if bit then m₁ else m₀))
  pure (bit == answer)

/-- The chosen-plaintext experiment: the challenge phase under a fresh public key. -/
def cpaExperiment (sample : m (Fin n)) (coin : m Bool) (g : G)
    (choose : G → m (G × G × State)) (guess : State → G × G → m Bool) : m Bool := do
  let (pk, _) ← keygen sample g
  challenge coin choose guess pk (encrypt sample g pk)

/-- The DDH test built from a chosen-plaintext adversary: given `(pk, head, mask)`, it plays the
challenge phase under `pk`, encrypting a message `m` as `(head, m * mask)`. -/
def ddhReduction (coin : m Bool) (choose : G → m (G × G × State))
    (guess : State → G × G → m Bool) (pk head mask : G) : m Bool :=
  challenge coin choose guess pk fun message => pure (head, message * mask)

@[simp]
theorem decrypt_encrypt (g message : G) (x r : Fin n) :
    decrypt x (g ^ r.val, message * (g ^ x.val) ^ r.val) = message := by
  simp [decrypt, ← pow_mul, Nat.mul_comm]

/-- Decrypting an honest encryption under an honest key returns the message, as an equation of
programs: only the two samples remain, so the equation holds whatever the samples cost, observe,
or fail. -/
theorem decrypt_keygen_encrypt [LawfulMonad m] (sample : m (Fin n)) (g message : G) :
    (do
      let (pk, x) ← keygen sample g
      let ciphertext ← encrypt sample g pk message
      pure (decrypt x ciphertext)) =
    (do
      let _ ← sample
      let _ ← sample
      pure message) := by
  simp [keygen, encrypt]

end Cslib.Crypto.ElGamal
