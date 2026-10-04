/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Field.Basic

/-!
# Schnorr signatures and identification

The scalar field acts on the additive group of public keys. For a prime-order group the
scalars are `ZMod q`. This uses Mathlib's `Module` directly, as in VCVio's Schnorr development.
In multiplicative notation the verification equation is `g^z = R * pk^c`.

Sampling and hashing are explicit monadic arguments. A signature hashes both the message and
commitment. The random-oracle interpretation must retain its cache between signing and
verification; independently sampling each hash call would not implement this scheme.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The response to a verifier's challenge. -/
def respond (secret nonce challenge : F) : F := nonce + challenge * secret

/-- Verify an identification transcript. -/
def Accepts (g pk commitment : G) (challenge response : F) : Prop :=
  response • g = commitment + challenge • pk

instance [DecidableEq G] (g pk commitment : G) (challenge response : F) :
    Decidable (Accepts g pk commitment challenge response) :=
  inferInstanceAs (Decidable (response • g = commitment + challenge • pk))

/-- Extract a witness from responses to two distinct challenges for the same commitment. -/
def extract (challenge₁ response₁ challenge₂ response₂ : F) : F :=
  (response₁ - response₂) / (challenge₁ - challenge₂)

section Programs

variable {m : Type → Type*} [Monad m]

/-- Generate a secret scalar and its public key. -/
def keygen (sample : m F) (g : G) : m (G × F) := do
  let secret ← sample
  pure (secret • g, secret)

/-- Sign using a fresh nonce and the hash of the message and commitment. -/
def sign (sample : m F) (hash : M × G → m F) (g : G) (secret : F)
    (message : M) : m (G × F) := do
  let nonce ← sample
  let commitment := nonce • g
  let challenge ← hash (message, commitment)
  pure (commitment, respond secret nonce challenge)

/-- Verify a signature using the same hash interpretation as the signer. -/
def verify [DecidableEq G] (hash : M × G → m F) (g pk : G)
    (message : M) (signature : G × F) : m Bool := do
  let challenge ← hash (message, signature.1)
  pure (decide (Accepts g pk signature.1 challenge signature.2))

/-- An honest identification transcript with an independent uniform challenge. -/
def realTranscript (sample : m F) (g : G) (secret : F) : m (G × F × F) := do
  let nonce ← sample
  let challenge ← sample
  pure (nonce • g, challenge, respond secret nonce challenge)

/-- Simulate a transcript without the secret key, by choosing its challenge and response. -/
def simulateTranscript (sample : m F) (g pk : G) : m (G × F × F) := do
  let challenge ← sample
  let response ← sample
  pure (response • g - challenge • pk, challenge, response)

end Programs

/-- Honest responses satisfy verification for every nonce and challenge. -/
theorem accepts_respond (g : G) (secret nonce challenge : F) :
    Accepts g (secret • g) (nonce • g) challenge (respond secret nonce challenge) := by
  simp [Accepts, respond, add_smul, mul_smul]

/-- The simulator always produces an accepting transcript. -/
theorem accepts_simulate (g pk : G) (challenge response : F) :
    Accepts g pk (response • g - challenge • pk) challenge response := by
  simp [Accepts]

/-- Special soundness: two accepting transcripts for the same commitment and different
challenges reveal a discrete logarithm of the public key. -/
theorem extract_smul (g pk commitment : G) {challenge₁ challenge₂ response₁ response₂ : F}
    (hne : challenge₁ ≠ challenge₂)
    (h₁ : Accepts g pk commitment challenge₁ response₁)
    (h₂ : Accepts g pk commitment challenge₂ response₂) :
    extract challenge₁ response₁ challenge₂ response₂ • g = pk := by
  have hsub : (response₁ - response₂) • g = (challenge₁ - challenge₂) • pk := by
    simpa only [sub_smul, add_sub_add_left_eq_sub] using congrArg₂ (· - ·) h₁ h₂
  rw [extract, div_eq_mul_inv, mul_comm, mul_smul, hsub, ← mul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]

end Cslib.Crypto.Schnorr
