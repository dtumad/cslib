/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.Schnorr.Oracle
import Cslib.Foundations.Data.PFunctor.Free.Trace
import Mathlib.Algebra.Field.ZMod

set_option linter.hashCommand false

/-! Integration checks for cached signing, message freshness, and replay. The small field is
only an executable regression instance; the library theorems quantify over arbitrary fields. -/

open Cslib.Crypto PFunctor

namespace SchnorrTests

abbrev F := ZMod 101
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev random : PFunctor := ⟨Unit, fun _ => F⟩

def sample : random.FreeM F := FreeM.lift ()

def counted (op : random.A) : StateM ℕ (random.B op) := fun count =>
  (count, count + 1)

def honest : random.FreeM (Bool × List ((String × F) × F)) :=
  (do
    let signature ← Schnorr.sign (monadLift sample) (RandomOracle.query sample)
      (1 : F) (7 : F) "message"
    Schnorr.verify (RandomOracle.query sample) (1 : F) (7 : F) "message" signature :
      StateT (List ((String × F) × F)) random.FreeM Bool).run []

-- The verifier reuses the signing challenge: just the nonce and first hash query draw randomness.
#guard ((honest.liftM counted).run 3).1.1 = true
#guard ((honest.liftM counted).run 3).1.2.length = 1
#guard ((honest.liftM counted).run 3).2 = 5

def replaySignature (_pk : F) :
    (Schnorr.signatureEffects random String F F).FreeM (String × F × F) := do
  let signature ← FreeM.lift (P := Schnorr.signatureEffects random String F F)
    (.inr (.inr "message"))
  pure ("message", signature)

-- A valid signature obtained from the signing oracle is not a forgery on a fresh message.
#guard (((Schnorr.unforgeabilityExperiment sample (1 : F) replaySignature).liftM counted).run
  3 |>.run) == (false, 6)

example : Schnorr.extract (3 : F) (Schnorr.respond (7 : F) (11 : F) (3 : F))
    (5 : F) (Schnorr.respond (7 : F) (11 : F) (5 : F)) = (7 : F) := by
  norm_num [Schnorr.extract, Schnorr.respond]
  rw [div_eq_iff (by decide : (2 : F) ≠ 0)]
  norm_num

def twoSamples : random.FreeM (F × F) := do
  let first ← sample
  let second ← sample
  pure (first, second)

-- Replaying a prefix leaves the saved first sample in the continuation; only the suffix changes.
example : FreeM.replay [⟨(), (17 : F)⟩] twoSamples =
    some (do let second ← sample; pure ((17 : F), second)) := rfl

example : FreeM.replay [⟨(), (17 : F)⟩, ⟨(), (23 : F)⟩] twoSamples =
    some (pure ((17 : F), (23 : F))) := rfl

end SchnorrTests
