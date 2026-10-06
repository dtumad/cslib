/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.HVZK
public import Cslib.Crypto.RandomOracle
public import Cslib.Foundations.Data.PFunctor.Basic

/-!
# Schnorr with a shared random oracle

The adversary can interleave ambient effects, hash queries, and signing queries. Signing and
verification share the same hash cache. The message log enforces ordinary EUF-CMA freshness:
returning a signature on any previously signed message loses, even with a different signature.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq M] [DecidableEq G]

/-- Honest signing followed by verification returns `true`, retaining the signer's final cache.
This is a program equality, so it holds for any sampling interpretation, including resumptions. -/
theorem sign_verify {m : Type → Type*} [Monad m] [LawfulMonad m]
    (sample : m F) (g : G) (secret : F) (message : M) (cache : List ((M × G) × F)) :
    (do
      let signature ← sign (monadLift sample) (RandomOracle.query sample) g secret message
      verify (RandomOracle.query sample) g (secret • g) message signature :
        StateT (List ((M × G) × F)) m Bool).run cache =
    (do
      let (_, cache') ← (sign (monadLift sample) (RandomOracle.query sample)
        g secret message).run cache
      pure (true, cache')) := by
  simp only [sign, verify, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind]
  congr 1
  funext nonce
  cases h : cache.lookup (message, nonce • g) <;>
    simp [RandomOracle.query, StateT.run, h, accepts_respond]

/-- Ambient effects, random-oracle requests, and signing requests. -/
abbrev signatureEffects (P : PFunctor.{0, 0}) (M G F : Type) : PFunctor.{0, 0} :=
  P + (PFunctor.mk (M × G) (fun _ => F) + PFunctor.mk M (fun _ => G × F))

variable {P : PFunctor.{0, 0}}

/-- Whether an operation of a forger is a hash request. -/
def isHashQuery : (signatureEffects P M G F).A → Bool
  | .inr (.inl _) => true
  | _ => false

/-- Whether an operation of a forger is a signing request. -/
def isSignQuery : (signatureEffects P M G F).A → Bool
  | .inr (.inr _) => true
  | _ => false

/-- The concrete handler keeps the signing log and hash cache together throughout the game. -/
def signatureHandler (sample : P.FreeM F) (g : G) (secret : F) :
    (op : (signatureEffects P M G F).A) →
      StateT (List M × List ((M × G) × F)) P.FreeM ((signatureEffects P M G F).B op)
  | .inl op => fun state => do
      let answer ← FreeM.lift op
      pure (answer, state)
  | .inr (.inl input) => fun (messages, cache) => do
      let (answer, cache') ← RandomOracle.query sample input cache
      pure (answer, messages, cache')
  | .inr (.inr message) => fun (messages, cache) => do
      let (signature, cache') ← sign (monadLift sample) (RandomOracle.query sample)
        g secret message cache
      pure (signature, message :: messages, cache')

/-- The EUF-CMA experiment, including a final verifier query to the shared hash oracle. -/
def unforgeabilityExperiment (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) : P.FreeM Bool := do
  let (pk, secret) ← keygen sample g
  let ((message, signature), messages, cache) ←
    ((adversary pk).liftM (signatureHandler sample g secret)) ([], [])
  let (valid, _) ← verify (RandomOracle.query sample) g pk message signature cache
  pure (valid && decide (message ∉ messages))

end Cslib.Crypto.Schnorr
