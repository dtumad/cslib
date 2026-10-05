/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.Security.Binary
import Cslib.Computability.PolynomialTime.Sampling.Finite
import Cslib.Computability.PolynomialTime.Finite
import CslibTests.MachineRuntime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Order

/-! Check rejection, canonical messages, and adaptive encryption across the challenge. -/

open PFunctor Cslib.Crypto Turing.MultiTapeTM Turing.MultiTapePTM

namespace ElGamalTests

abbrev G := Multiplicative (ZMod 3)

noncomputable def code : Computability.Encoding G Bool :=
  .finEquiv (ZMod.finEquiv 3).toEquiv.symm

def generator : G := Multiplicative.ofAdd 1

-- Reject the first proposal (3), then accept the second (1).
example : ElGamal.encryptWordFromBits code 3 2 generator (generator ^ 2)
    (code.encode generator) [true, true, false, true] =
      (code.bitPair code).bitOption.encode (some (generator, 1)) := rfl

-- Exhaustion and a noncanonical encoding of zero both produce a valid absent reply.
example : ElGamal.encryptWordFromBits code 3 1 generator generator
    (code.encode generator) [true, true] = [] := rfl

example : ElGamal.encryptWordFromBits code 3 1 generator generator
    [false] [false, true] = [] := rfl

noncomputable def choose (_ : G) : (effects Unit).FreeM (G × G × Bool) := do
  let reply ← query () (code.encode generator)
  pure (1, generator, reply.isEmpty)

noncomputable def guess (firstFailed : Bool) (_ : G × G) : (effects Unit).FreeM Bool := do
  let reply ← query () (code.encode generator)
  pure (firstFailed && !reply.isEmpty)

-- The first oracle nonce fails. Execution continues through the challenge and a second oracle
-- request, retaining the first failure in the adversary's state. All nine supplied bits are used.
example : Id.run (((ElGamal.cpaWordExperiment code 3 1 generator choose guess).liftM
    MachineRuntime.savedBits).run
      [false, true, true, true, true, false, true, true, false]) = (some true, []) := rfl

-- Key-generation exhaustion prevents either adversary phase from running.
example : Id.run (((ElGamal.cpaWordExperiment code 3 1 generator choose guess).liftM
    MachineRuntime.savedBits).run [true, true, false]) = (none, [false]) := rfl

local instance : MeasurableSpace Word := ⊤

-- The parser and encryption arithmetic remain certified for unbounded parameters, requests,
-- and random tapes. Only the fixed test group's multiplication uses a finite lookup table.
example : IsPolyTime
    (pairEncoding (sigmaEncoding unaryEncoding (fun _ => code.toEmbedding))
      (pairEncoding wordEncoding wordEncoding))
    (fun arg => ElGamal.encryptWordFromBits code 3 (arg.1.1 + 1) generator
      arg.1.2 arg.2.1 arg.2.2) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code.encode value).length)
  apply ElGamal.isPolyTime_encryptWordFromBits (G := fun _ => G) (fun _ => code)
    (fun _ => 3) (fun n => n + 1) (fun _ => generator)
    (isPolyTime_const _ _) _ (isPolyTime_const _ _) _ (isPolyTime_const _ _) _
    (size := fun _ => bound) (by fun_prop) (fun _ => hbound)
  · exact (isPolyTime_input unaryEncoding).unary_add (g := fun _ => 1)
      (isPolyTime_const _ [true])
  · exact (isPolyTime_of_finite (pairEncoding code.toEmbedding code.toEmbedding)
      (fun pair => code.encode (pair.1 * pair.2))).comp_encoded
        (isPolyTime_input _).sigma_snd
  · exact IsPolyTime.decode_finEquiv (parameter := Prod.fst)
      (fun _ => (ZMod.finEquiv 3).toEquiv.symm)
      (isPolyTime_const _ _) (isPolyTime_snd _ _)

end ElGamalTests
