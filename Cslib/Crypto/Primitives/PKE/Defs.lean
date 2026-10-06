/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.MeasureSemantics
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Public-key encryption

A public-key encryption scheme (`PKE`) generates a key pair for each security parameter, encrypts
messages under a public key, and decrypts ciphertexts with a secret key; its messages and
ciphertexts may depend on the public key. Key generation and encryption are programs in a monad
`m`. The scheme is correct (`PKE.IsCorrect`) if decrypting the encryption of a message under a
generated key pair returns the message, as an equation of programs.

An eavesdropper (`PKE.EavAdversary`) chooses two messages for a public key, then guesses which of
them a ciphertext encrypts; its two phases share a private state. They are programs in a monad
`m₀` lifted into `m`, so that the adversary may use other resources than the scheme. In the
eavesdropping experiment (`PKE.eavExp`), the ciphertext encrypts one of the two messages selected
by a coin flip. The scheme is secure against the eavesdroppers satisfying a predicate
(`PKE.EavSecure`) if each of them guesses the coin with negligible advantage, under a semantics
`sem` of `m`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

open MeasureTheory Filter

namespace Cslib.Crypto

/-- A public-key encryption scheme whose key generation and encryption are programs in `m`. -/
structure PKE (m : Type → Type*) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : PK → Type
  /-- Messages. -/
  Msg : PK → Type
  /-- Ciphertexts. -/
  Ctxt : PK → Type
  /-- Generate a key pair for the security parameter. -/
  gen : ℕ → m (Σ pk, SK pk)
  /-- Encrypt a message. -/
  enc : (pk : PK) → Msg pk → m (Ctxt pk)
  /-- Decrypt a ciphertext, or fail. -/
  dec : (pk : PK) → SK pk → Ctxt pk → Option (Msg pk)

namespace PKE

variable {m : Type → Type*} [Monad m] (S : PKE m)

/-- Decryption recovers encrypted messages: generating a key pair and encrypting a message chosen
for its public key, decryption returns that message on every run. -/
def IsCorrect : Prop :=
  ∀ n (msg : ∀ pk, S.Msg pk),
    (do
      let key ← S.gen n
      let c ← S.enc key.1 (msg key.1)
      pure (⟨key.1, S.dec key.1 key.2 c⟩ : Σ pk, Option (S.Msg pk))) =
    (do
      let key ← S.gen n
      let _ ← S.enc key.1 (msg key.1)
      pure ⟨key.1, some (msg key.1)⟩)

/-- An eavesdropper whose phases are programs in `m₀`: for each security parameter, it chooses two
messages for the public key, then guesses which of them a ciphertext encrypts. The phases share a
countable private state. -/
structure EavAdversary (m₀ : Type → Type*) where
  /-- The private state. -/
  State : Type
  [countable : Countable State]
  /-- Choose two messages for the public key. -/
  choose : ℕ → (pk : S.PK) → m₀ (S.Msg pk × S.Msg pk × State)
  /-- Guess which of the two messages the ciphertext encrypts. -/
  guess : ℕ → State → (pk : S.PK) → S.Ctxt pk → m₀ Bool

namespace EavAdversary

attribute [instance] countable

variable {S} {m₀ : Type → Type*} (A : S.EavAdversary m₀)

instance : MeasurableSpace A.State := ⊤

instance : DiscreteMeasurableSpace A.State := ⟨fun _ => trivial⟩

end EavAdversary

variable (sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α) {m₀ : Type → Type*}
  [MonadLiftT m₀ m] (coin : m₀ Bool)

/-- The eavesdropping experiment at the security parameter `n`: the adversary sees an encryption
of one of its two messages, selected by `coin`, and wins by guessing which. -/
def eavExp (A : S.EavAdversary m₀) (n : ℕ) : m Bool := do
  let key ← S.gen n
  let (msg₀, msg₁, state) ← monadLift (A.choose n key.1)
  let bit ← monadLift coin
  let c ← S.enc key.1 (if bit then msg₁ else msg₀)
  let answer ← monadLift (A.guess n state key.1 c)
  pure (bit == answer)

/-- The advantage of the adversary in guessing the coin at the security parameter `n`. -/
noncomputable def eavAdvantage (A : S.EavAdversary m₀) (n : ℕ) : ℝ :=
  |(sem (S.eavExp coin A n)).real {true} - 1 / 2|

/-- Security against eavesdroppers: every admissible adversary has negligible advantage. -/
def EavSecure (Admissible : S.EavAdversary m₀ → Prop) : Prop :=
  ∀ A, Admissible A →
    Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) (S.eavAdvantage sem coin A)

end PKE

end Cslib.Crypto
