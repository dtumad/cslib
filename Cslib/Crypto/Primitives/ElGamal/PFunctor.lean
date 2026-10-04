/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal

/-!
# ElGamal over polynomial effects

The same free programs can be interpreted with different sampling and adversary handlers.
The security identity needs only the two sampler laws; it makes no efficiency assumption about
arbitrary Lean functions in an adversary. Computational security additionally requires a
machine certificate for the concrete reduction.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

open PFunctor

universe uA v

variable {P : PFunctor.{uA, 0}} {m : Type → Type v} [Monad m] [LawfulMonad m]
  {G State : Type} [Group G] {n : ℕ}
  (interp : (op : P.A) → m (P.B op))
  (sample : P.FreeM (Fin n)) (coin : P.FreeM Bool) (g : G)
  (choose : G → P.FreeM (G × G × State)) (guess : State → G × G → P.FreeM Bool)

@[simp]
theorem liftM_cpaExperiment :
    (cpaExperiment sample coin g choose guess).liftM interp =
      cpaExperiment (sample.liftM interp) (coin.liftM interp) g
        (fun pk => (choose pk).liftM interp) (fun state ciphertext =>
          (guess state ciphertext).liftM interp) := by
  simp [cpaExperiment, keygen, encrypt, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhReduction (pk head mask : G) :
    (ddhReduction coin choose guess pk head mask).liftM interp =
      ddhReduction (coin.liftM interp) (fun pk => (choose pk).liftM interp)
        (fun state ciphertext => (guess state ciphertext).liftM interp) pk head mask := by
  simp [ddhReduction, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhReal (test : G → G → G → P.FreeM Bool) :
    (ddhReal sample g test).liftM interp =
      ddhReal (sample.liftM interp) g (fun pk head mask => (test pk head mask).liftM interp) := by
  simp [ddhReal, FreeM.liftM_bind]

@[simp]
theorem liftM_ddhRandom (test : G → G → G → P.FreeM Bool) :
    (ddhRandom sample g test).liftM interp =
      ddhRandom (sample.liftM interp) g (fun pk head mask => (test pk head mask).liftM interp) := by
  simp [ddhRandom, FreeM.liftM_bind]

/-- The concrete DDH reduction applies directly to free programs, with arbitrary effects in
both adversary phases. The sampling assumptions are equations about their interpretation. -/
theorem advantage_liftM_eq_ddh [NeZero n]
    (interp : (op : P.A) → PMF (P.B op))
    (hg : Function.Bijective (fun x : Fin n => g ^ x.val))
    (hsample : sample.liftM interp = PMF.uniformOfFintype (Fin n))
    (hcoin : coin.liftM interp = PMF.uniformOfFintype Bool) :
    |Game.winProbability ((cpaExperiment sample coin g choose guess).liftM interp) - 1 / 2| =
      Game.advantage
        ((ddhReal sample g (ddhReduction coin choose guess)).liftM interp)
        ((ddhRandom sample g (ddhReduction coin choose guess)).liftM interp) := by
  simp only [liftM_cpaExperiment, liftM_ddhReal, liftM_ddhRandom, liftM_ddhReduction,
    hsample, hcoin]
  exact advantage_eq_ddh g hg _ _

end Cslib.Crypto.ElGamal
