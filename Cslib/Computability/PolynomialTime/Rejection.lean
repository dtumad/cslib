/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Binary
public import Cslib.Computability.PolynomialTime.Option

/-!
# Bounded rejection from a binary random tape

The bound is binary, while the width and attempt budget are unary. Splitting the random tape,
comparing proposals, retaining the first accepted value, and writing its canonical representation
all have uniform machine certificates.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

/-- Read at most `attempts` blocks, returning the first binary value below `bound`.
Missing input bits are zero; callers sampling complete blocks supply `bits * attempts` coins. -/
def selectBelow (bound bits : ℕ) : ℕ → Word → Option ℕ
  | 0, _ => none
  | attempts + 1, coins =>
    let value := Nat.ofBitsList (coins.take bits).reverse
    if value < bound then some value else selectBelow bound bits attempts (coins.drop bits)

private def rejectionStep (bound bits : ℕ) (state : Word × Option ℕ) : Word × Option ℕ :=
  (state.1.drop bits, state.2.orElse (fun _ =>
    let value := Nat.ofBitsList (state.1.take bits).reverse
    if value < bound then some value else none))

private theorem rejectionStep_iterate (bound bits attempts : ℕ)
    (coins : Word) (result : Option ℕ) :
    ((rejectionStep bound bits)^[attempts] (coins, result)).2 =
      result.orElse (fun _ => selectBelow bound bits attempts coins) := by
  induction attempts generalizing coins result with
  | zero => cases result <;> rfl
  | succ attempts ih =>
    rw [Function.iterate_succ_apply]
    change ((rejectionStep bound bits)^[attempts] (_, _)).2 = _
    rw [ih]
    cases result with
    | some value => rfl
    | none =>
      by_cases h : Nat.ofBitsList (coins.take bits).reverse < bound <;>
        simp [selectBelow, h]

/-- Binary rejection is polynomial in the encoded bound, tape length, and unary attempt budget. -/
theorem IsPolyTime.selectBelow {α : Type} {input : α ↪ Word}
    {bound bits attempts : α → ℕ} {coins : α → Word}
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a)))
    (hcoins : IsPolyTime input coins) :
    IsPolyTime input (fun a => optionEncoding binaryEncoding
      (selectBelow (bound a) (bits a) (attempts a) (coins a))) := by
  let stateCode := pairEncoding wordEncoding (optionEncoding binaryEncoding)
  have henv := isPolyTime_fst input stateCode
  have htape := (isPolyTime_snd input stateCode).fst
  have hresult := (isPolyTime_snd input stateCode).snd
  have hwidth := hbits.comp_encoded henv
  have hlimit := hbound.comp_encoded henv
  have hvalue := (htape.take hwidth).reverse.binary_ofBitsList
  have haccept : IsPolyTime (pairEncoding input stateCode) (fun pair =>
      optionEncoding binaryEncoding
        (if Nat.ofBitsList (pair.2.1.take (bits pair.1)).reverse < bound pair.1
          then some (Nat.ofBitsList (pair.2.1.take (bits pair.1)).reverse) else none)) := by
    simpa only [apply_ite, optionEncoding_none, wordEncoding,
      Function.Embedding.refl_apply] using
      (hvalue.binary_lt hlimit).ite hvalue.option_some (isPolyTime_const _ [])
  have hstep : IsPolyTime (pairEncoding input stateCode) (fun pair =>
      stateCode (rejectionStep (bound pair.1) (bits pair.1) pair.2)) :=
    (htape.drop hwidth).pair (hresult.option_orElse haccept)
  have hloop := (hcoins.pair (right := optionEncoding binaryEncoding)
    (g := fun _ => none) (isPolyTime_const input [])).iterate_with_bounded_growth
      (stateEncoding := stateCode) (step := fun a => rejectionStep (bound a) (bits a))
      hattempts hstep (growth := fun _ => 1) (by fun_prop) (by
        rintro a ⟨word, result⟩
        cases result with
        | some value => simp [stateCode, rejectionStep, wordEncoding]; omega
        | none =>
          simp only [stateCode, rejectionStep, Option.orElse_none, length_pairEncoding,
            wordEncoding, Function.Embedding.refl_apply, List.length_drop, optionEncoding_none]
          split
          · simp only [optionEncoding_some, List.length_cons, binaryEncoding_apply]
            have hlength := Nat.length_bits_ofBitsList_le (word.take (bits a)).reverse
            simp only [List.length_reverse, List.length_take] at hlength
            omega
          · simp; omega)
  simpa only [rejectionStep_iterate, Option.orElse_none] using hloop.snd

end Turing.MultiTapeTM
