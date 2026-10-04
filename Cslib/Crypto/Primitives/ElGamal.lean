/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Game
public import Cslib.Foundations.Data.PFunctor.Free.Measure.PMF
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# ElGamal encryption and its DDH reduction

The algorithms and two-stage experiment use ordinary monad operations, so they specialize
directly to `PFunctor.FreeM`. Sampling and the two adversary phases are explicit arguments.
The reduction uses only a fair challenge bit in addition to its adversary's randomness.

We use multiplicative notation and exponents in `Fin n`. The security theorem assumes that
`i ↦ g ^ i.val` is a bijection onto the group; prime order is not needed for ElGamal.

References: Katz and Lindell, *Introduction to Modern Cryptography* (2007), Construction 10.19
and Theorem 10.20. Adapted from VCVio's ElGamal development, using Samuel Schlesinger's common
Boolean experiment and advantage definitions.
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

section Distributions

variable (sample : PMF (Fin n)) (coin : PMF Bool) (g : G)
  (choose : G → PMF (G × G × State)) (guess : State → G × G → PMF Bool)

/-- The reduction's real experiment is exactly the encryption experiment. -/
theorem ddhReal_eq_cpaExperiment :
    ddhReal sample g (ddhReduction coin choose guess) =
      cpaExperiment sample coin g choose guess := by
  simp only [ddhReal, ddhReduction, cpaExperiment, keygen, encrypt,
    bind_assoc, pure_bind]
  congr 1
  funext x
  change sample.bind (fun r => (choose (g ^ x.val)).bind (fun messages =>
    coin.bind fun bit => (guess messages.2.2
      (g ^ r.val, (if bit then messages.2.1 else messages.1) * g ^ (x.val * r.val))).bind
        fun answer => PMF.pure (bit == answer))) = _
  rw [PMF.bind_comm sample (choose (g ^ x.val))]
  congr 1
  funext messages
  rw [PMF.bind_comm sample coin]
  simp only [pow_mul]
  rfl

end Distributions

section Security

variable [Fintype G] [NeZero n] (g : G)
  (hg : Function.Bijective (fun x : Fin n => g ^ x.val))

include hg

/-- Multiplying a uniform group element by a fixed message hides that message perfectly. -/
theorem uniform_mask (message : G) :
    (PMF.uniformOfFintype (Fin n)).map (fun x => message * g ^ x.val) =
      PMF.uniformOfFintype G :=
  Probability.PMF.uniformOfFintype_map_equiv
    ((Equiv.ofBijective (fun x : Fin n => g ^ x.val) hg).trans (Equiv.mulLeft message))

private theorem uniform_mask_bind {α : Type} (message : G) (f : G → PMF α) :
    (PMF.uniformOfFintype (Fin n)).bind (fun x => f (message * g ^ x.val)) =
      (PMF.uniformOfFintype G).bind f := by
  change (PMF.uniformOfFintype (Fin n)).bind (f ∘ (fun x => message * g ^ x.val)) = _
  rw [← PMF.bind_map, uniform_mask g hg]

omit hg in
private theorem fair_guess (guess : PMF Bool) :
    (PMF.uniformOfFintype Bool).bind (fun bit =>
      guess.bind fun answer => PMF.pure (bit == answer)) = PMF.uniformOfFintype Bool := by
  rw [PMF.bind_comm]
  have h (answer : Bool) :
      (PMF.uniformOfFintype Bool).bind (fun bit => PMF.pure (bit == answer)) =
        PMF.uniformOfFintype Bool := by
    ext result
    cases answer <;> cases result <;>
      simp [PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  simp_rw [h]
  exact PMF.bind_const _ _

omit [Fintype G] in
/-- On a random triple the reduction's answer is a fair coin, for any two-stage adversary. -/
theorem ddhRandom_eq_uniform
    (choose : G → PMF (G × G × State)) (guess : State → G × G → PMF Bool) :
    ddhRandom (PMF.uniformOfFintype (Fin n)) g
      (ddhReduction (PMF.uniformOfFintype Bool) choose guess) = PMF.uniformOfFintype Bool := by
  have h (pk head : G) :
      (PMF.uniformOfFintype (Fin n)).bind (fun z =>
        ddhReduction (PMF.uniformOfFintype Bool) choose guess pk head (g ^ z.val)) =
          PMF.uniformOfFintype Bool := by
    let : Fintype G := Fintype.ofEquiv (Fin n) (Equiv.ofBijective _ hg)
    change (PMF.uniformOfFintype (Fin n)).bind (fun z => (choose pk).bind (fun messages =>
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (guess messages.2.2
          (head, (if bit then messages.2.1 else messages.1) * g ^ z.val)).bind
            fun answer => PMF.pure (bit == answer))) = _
    rw [PMF.bind_comm]
    calc
      _ = (choose pk).bind (fun _ => PMF.uniformOfFintype Bool) := by
        apply congrArg (PMF.bind (choose pk))
        funext messages
        rw [PMF.bind_comm]
        trans (PMF.uniformOfFintype Bool).bind (fun bit =>
          (PMF.uniformOfFintype G).bind fun mask =>
            (guess messages.2.2 (head, mask)).bind fun answer => PMF.pure (bit == answer))
        · apply congrArg (PMF.bind (PMF.uniformOfFintype Bool))
          funext bit
          exact uniform_mask_bind g hg (if bit then messages.2.1 else messages.1)
            (fun mask => (guess messages.2.2 (head, mask)).bind
              fun answer => PMF.pure (bit == answer))
        · rw [PMF.bind_comm]
          simp_rw [fair_guess]
          exact PMF.bind_const _ _
      _ = _ := PMF.bind_const _ _
  change (PMF.uniformOfFintype (Fin n)).bind (fun x =>
    (PMF.uniformOfFintype (Fin n)).bind (fun r =>
      (PMF.uniformOfFintype (Fin n)).bind (fun z =>
        ddhReduction (PMF.uniformOfFintype Bool) choose guess
          (g ^ x.val) (g ^ r.val) (g ^ z.val)))) = _
  simp_rw [h]
  simp only [PMF.bind_const]

omit [Fintype G] in
/-- The two-stage ElGamal prediction bias is exactly the DDH distinguishing advantage of
its concrete reduction. This uses the textbook's undoubled bias convention. -/
theorem advantage_eq_ddh
    (choose : G → PMF (G × G × State)) (guess : State → G × G → PMF Bool) :
    |Game.winProbability (cpaExperiment (PMF.uniformOfFintype (Fin n))
        (PMF.uniformOfFintype Bool) g choose guess) - 1 / 2| =
      Game.advantage
        (ddhReal (PMF.uniformOfFintype (Fin n)) g
          (ddhReduction (PMF.uniformOfFintype Bool) choose guess))
        (ddhRandom (PMF.uniformOfFintype (Fin n)) g
          (ddhReduction (PMF.uniformOfFintype Bool) choose guess)) := by
  rw [ddhRandom_eq_uniform g hg, Game.advantage_uniform_bool, ddhReal_eq_cpaExperiment]

end Security

end Cslib.Crypto.ElGamal
