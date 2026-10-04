/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal
import Cslib.Crypto.Primitives.Schnorr.Oracle
import Cslib.Foundations.Data.PFunctor.Free.Random
import Mathlib.Algebra.Field.ZMod

set_option linter.hashCommand false

/-! Run both honest schemes from individual bits through bounded rejection sampling.
`OptionT` retains sampling failure; `StateT` retains Schnorr's hash cache. -/

open PFunctor Cslib.Crypto

namespace CryptoSampling

abbrev bits : PFunctor := ⟨Unit, fun _ => Fin 2⟩
abbrev F := ZMod 101
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sample (attempts : ℕ) : OptionT bits.FreeM (Fin 101) :=
  OptionT.mk (FreeM.sampleFin (FreeM.lift ()) 101 7 attempts)

def scalar (attempts : ℕ) : OptionT bits.FreeM F :=
  (fun x : Fin 101 => (x.val : F)) <$> sample attempts

def elgamal (attempts : ℕ) : OptionT bits.FreeM (Multiplicative F) := do
  let (pk, secret) ← ElGamal.keygen (sample attempts) (Multiplicative.ofAdd (1 : F))
  let ciphertext ← ElGamal.encrypt (sample attempts) (Multiplicative.ofAdd (1 : F)) pk
    (Multiplicative.ofAdd (42 : F))
  pure (ElGamal.decrypt secret ciphertext)

def schnorr (attempts : ℕ) : OptionT bits.FreeM Bool := do
  let (pk, secret) ← Schnorr.keygen (scalar attempts) (1 : F)
  let (valid, _) ← (do
    let signature ← Schnorr.sign (monadLift (scalar attempts))
      (RandomOracle.query (scalar attempts)) (1 : F) secret "message"
    Schnorr.verify (RandomOracle.query (scalar attempts)) (1 : F) pk "message" signature :
      StateT (List ((String × F) × F)) (OptionT bits.FreeM) Bool).run []
  pure valid

-- Repeated 7-bit blocks with a single set bit are nonzero accepted proposals.
def accepted (_ : bits.A) : StateM ℕ (Fin 2) := fun count =>
  (if count % 7 = 0 then 1 else 0, count + 1)

def rejected (_ : bits.A) : StateM ℕ (Fin 2) := fun count => (1, count + 1)

#guard ((((elgamal 2).run.liftM accepted).run 0).run ==
  (some (Multiplicative.ofAdd (42 : F)), 14))
#guard ((((schnorr 2).run.liftM accepted).run 0).run == (some true, 21))

-- Exhausting the sampler stops key generation in both schemes and keeps the failure visible.
#guard ((((elgamal 2).run.liftM rejected).run 0).run == (none, 14))
#guard ((((schnorr 2).run.liftM rejected).run 0).run == (none, 14))

end CryptoSampling
