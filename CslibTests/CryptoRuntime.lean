/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal.PolynomialTime
import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
import Cslib.Computability.PolynomialTime.Finite
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Order

/-! Instantiate the primitive boundary in a fixed small group, with an unbounded unary retry
budget and binary exponents. Finite tables implement only this fixed group's operations. -/

open Turing.MultiTapeTM Turing.MultiTapePTM PFunctor Cslib.Crypto

namespace CryptoRuntime

abbrev G := Multiplicative (ZMod 2)

noncomputable def code : G ↪ Word := finiteEncoding G

def generator : G := Multiplicative.ofAdd 1

local instance : MeasurableSpace Word := ⊤

theorem mul_poly : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code))
    (fun value => code (value.2.1 * value.2.2)) :=
  (isPolyTime_of_finite (pairEncoding code code) (fun pair => code (pair.1 * pair.2))).comp_encoded
    (isPolyTime_input (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code))).sigma_snd

theorem inv_poly : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => code))
    (fun value => code value.2⁻¹) :=
  (isPolyTime_of_finite code (fun value => code value⁻¹)).comp_encoded
    (isPolyTime_input (sigmaEncoding unaryEncoding (fun _ => code))).sigma_snd

theorem attempts_poly : IsPolyTime unaryEncoding (fun n => unaryEncoding (n + 1)) :=
  (isPolyTime_input unaryEncoding).unary_add (g := fun _ => 1)
    (isPolyTime_const unaryEncoding [true])

example : IsPPT (Oracle := Empty) unaryEncoding wordEncoding (fun parameter =>
    optionEncoding (pairEncoding code (finBinaryEncoding 2)) <$>
      (ElGamal.keygen (m := OptionT (effects Empty).FreeM)
        (OptionT.mk (FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          2 2 (parameter + 1))) generator).run) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPPT_keygen (G := fun _ => G) (fun _ => code) (fun _ => 2)
    (fun parameter => parameter + 1) (fun _ => generator)
    (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    mul_poly (isPolyTime_const _ _) (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

example : IsPPT (Oracle := Empty)
    (sigmaEncoding unaryEncoding (fun _ => pairEncoding code code)) wordEncoding (fun input =>
      optionEncoding (pairEncoding code code) <$>
        (ElGamal.encrypt (m := OptionT (effects Empty).FreeM)
          (OptionT.mk (FreeM.sampleFin
            ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
            2 2 (input.1 + 1))) generator input.2.1 input.2.2).run) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPPT_encrypt (G := fun _ => G) (fun _ => code) (fun _ => 2)
    (fun parameter => parameter + 1) (fun _ => generator)
    (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    mul_poly (isPolyTime_const _ _) (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

example : IsPolyTime (sigmaEncoding unaryEncoding
    (fun _ => pairEncoding (finBinaryEncoding 2) (pairEncoding code code)))
      (fun input => code (ElGamal.decrypt input.2.1 input.2.2)) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le (fun value => (code value).length)
  exact ElGamal.isPolyTime_decrypt (G := fun _ => G) (fun _ => code) (fun _ => 2)
    mul_poly (isPolyTime_const _ _) inv_poly
    (size := fun _ => bound) (by fun_prop) (fun _ => hbound)

abbrev F := ZMod 2

noncomputable def scalar : F ≃ Fin 2 := (ZMod.finEquiv 2).toEquiv.symm

noncomputable def scalarCode : F ↪ Word := finEquivEncoding scalar

theorem fieldOp_poly (op : F → F → F) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun _ => pairEncoding scalarCode scalarCode))
      (fun value => scalarCode (op value.2.1 value.2.2)) :=
  (isPolyTime_of_finite (pairEncoding scalarCode scalarCode)
    (fun pair => scalarCode (op pair.1 pair.2))).comp_encoded
      (isPolyTime_input
        (sigmaEncoding unaryEncoding (fun _ => pairEncoding scalarCode scalarCode))).sigma_snd

example : IsPPT (Oracle := Empty) unaryEncoding wordEncoding (fun parameter =>
    optionEncoding (pairEncoding scalarCode scalarCode) <$>
      (Schnorr.keygen (m := OptionT (effects Empty).FreeM)
        (OptionT.mk (Option.map scalar.symm <$> FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          2 2 (parameter + 1))) (1 : F)).run) :=
  Schnorr.isPPT_keygen (F := fun _ => F) (G := fun _ => F)
    (fun _ => scalarCode) (fun _ => 2) (fun parameter => parameter + 1) (fun _ => scalar)
    (fun _ => 1) (isPolyTime_const _ _) attempts_poly (isPolyTime_const _ _)
    (isPolyTime_const _ _) (fieldOp_poly (· • ·))

example : IsPolyTime (sigmaEncoding unaryEncoding
    (fun _ => pairEncoding scalarCode (pairEncoding scalarCode scalarCode)))
      (fun input => scalarCode (Schnorr.respond input.2.1 input.2.2.1 input.2.2.2)) :=
  Schnorr.isPolyTime_respond (F := fun _ => F) (fun _ => scalarCode)
    (fieldOp_poly (· + ·)) (fieldOp_poly (· * ·))

example : IsPolyTime (sigmaEncoding unaryEncoding (fun _ =>
    pairEncoding (pairEncoding scalarCode scalarCode) (pairEncoding scalarCode scalarCode)))
      (fun input => scalarCode
        (Schnorr.extract input.2.1.1 input.2.1.2 input.2.2.1 input.2.2.2)) :=
  Schnorr.isPolyTime_extract (F := fun _ => F) (fun _ => scalarCode)
    (fieldOp_poly (· - ·)) (fieldOp_poly (· / ·))

example : IsPolyTime (sigmaEncoding unaryEncoding (fun _ =>
    pairEncoding scalarCode (pairEncoding scalarCode
      (pairEncoding scalarCode (pairEncoding scalarCode scalarCode)))))
      (fun input => boolEncoding (decide (Schnorr.Accepts input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2))) :=
  Schnorr.isPolyTime_accepts (F := fun _ => F) (G := fun _ => F)
    (fun _ => scalarCode) (fun _ => scalarCode) (fieldOp_poly (· • ·)) (fieldOp_poly (· + ·))

end CryptoRuntime
