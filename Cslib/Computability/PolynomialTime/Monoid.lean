/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.PolynomialTime.Binary
public import Mathlib.Algebra.Group.Defs

/-!
# Uniform binary exponentiation

Repeated squaring uses certified multiplication and one binary digit per iteration. The family
parameter is encoded in unary. A polynomial bound on element representations controls intermediate
sizes; merely assuming that multiplication is polynomial time would not supply this bound.
-/

public section

namespace Turing.MultiTapeTM

open Cslib

variable {M : ℕ → Type} [∀ n, Monoid (M n)]

private def powerStep (state : Σ n, M n × M n) (bit : Bool) : Σ n, M n × M n :=
  ⟨state.1, state.2.1, if bit then state.2.2 * state.2.2 * state.2.1 else state.2.2 * state.2.2⟩

private theorem foldl_powerStep (n : ℕ) (base acc : M n) (bits : Word) :
    bits.foldl powerStep ⟨n, base, acc⟩ =
      ⟨n, base, bits.foldl (fun acc bit => if bit then acc * acc * base else acc * acc) acc⟩ := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => exact ih _

private theorem foldr_pow (n : ℕ) (base : M n) (bits : Word) :
    bits.foldr (fun bit acc => if bit then acc * acc * base else acc * acc) 1 =
      base ^ Nat.ofBitsList bits := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
    cases bit <;> simp [ih, Nat.bit, two_mul, pow_add, pow_succ]

/-- Binary exponentiation is uniformly polynomial time in a family with certified multiplication,
an efficiently represented identity, and polynomial-size element representations. -/
theorem isPolyTime_pow (element : ∀ n, M n ↪ Word)
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding (fun n => pairEncoding (element n) (element n)))
      (fun value => element value.1 (value.2.1 * value.2.2)))
    (hone : IsPolyTime unaryEncoding (fun n => element n 1))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ n (value : M n), (element n value).length ≤ size n) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun n => pairEncoding (element n) binaryEncoding))
      (fun value => element value.1 (value.2.1 ^ value.2.2)) := by
  let args := sigmaEncoding unaryEncoding (fun n => pairEncoding (element n) binaryEncoding)
  let accumulator := sigmaEncoding unaryEncoding (fun n => pairEncoding (element n) (element n))
  have hargs := isPolyTime_input args
  have hbase : IsPolyTime args (fun value => element value.1 value.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hargs.sigma_snd.bitPair_fst
  have hexponent : IsPolyTime args (fun value => binaryEncoding value.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hargs.sigma_snd.bitPair_snd
  have hinitial : IsPolyTime args
      (fun value => accumulator ⟨value.1, value.2.1, 1⟩) :=
    hargs.sigma_fst.sigma (element := fun n => pairEncoding (element n) (element n))
      (hbase.pair (left := wordEncoding) (right := wordEncoding)
        (hone.comp_encoded hargs.sigma_fst))
  have hstate := isPolyTime_fst accumulator boolEncoding
  have hparameter := hstate.sigma_fst
  have hg : IsPolyTime (pairEncoding accumulator boolEncoding)
      (fun pair => element pair.1.1 pair.1.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hstate.sigma_snd.bitPair_fst
  have hx : IsPolyTime (pairEncoding accumulator boolEncoding)
      (fun pair => element pair.1.1 pair.1.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hstate.sigma_snd.bitPair_snd
  have hsquare : IsPolyTime (pairEncoding accumulator boolEncoding)
      (fun pair => element pair.1.1 (pair.1.2.2 * pair.1.2.2)) := by
    apply hmul.comp_encoded (f := fun pair : (Σ n, M n × M n) × Bool =>
      ⟨pair.1.1, pair.1.2.2, pair.1.2.2⟩)
    apply hparameter.sigma
    exact hx.pair (left := wordEncoding) (right := wordEncoding) hx
  have hproduct : IsPolyTime (pairEncoding accumulator boolEncoding)
      (fun pair => element pair.1.1 (pair.1.2.2 * pair.1.2.2 * pair.1.2.1)) := by
    apply hmul.comp_encoded (f := fun pair : (Σ n, M n × M n) × Bool =>
      ⟨pair.1.1, pair.1.2.2 * pair.1.2.2, pair.1.2.1⟩)
    apply hparameter.sigma
    exact hsquare.pair (left := wordEncoding) (right := wordEncoding) hg
  have hstep : IsPolyTime (pairEncoding accumulator boolEncoding)
      (fun pair => accumulator (powerStep pair.1 pair.2)) := by
    apply hparameter.sigma
    apply hg.pair (left := wordEncoding) (right := wordEncoding)
    convert (isPolyTime_snd accumulator boolEncoding).cond hproduct hsquare using 1
    funext pair
    cases pair.2 <;> rfl
  obtain ⟨c, d, hbound⟩ := hpoly
  have hfold := hexponent.reverse.foldl_encoded (stateEncoding := accumulator)
    (step := powerStep) hinitial hstep
    (size := fun length => 2 * length + 3 * (c * (length + 1) ^ d) + 2) (by fun_prop) (by
      intro value index _
      rw [foldl_powerStep]
      simp only [accumulator, length_sigmaEncoding, length_pairEncoding,
        unaryEncoding_apply, List.length_replicate]
      have hparam : value.1 ≤ (args value).length := by
        simp only [args, length_sigmaEncoding, length_pairEncoding,
          unaryEncoding_apply, List.length_replicate]
        omega
      have hmono := Nat.mul_le_mul_left c (Nat.pow_le_pow_left
        (Nat.add_le_add_right hparam 1) d)
      have hg := (hsize value.1 value.2.1).trans ((hbound value.1).trans hmono)
      have hx := (hsize value.1 (((binaryEncoding value.2.2).reverse.take index).foldl
        (fun acc bit => if bit then acc * acc * value.2.1 else acc * acc) 1)).trans
          ((hbound value.1).trans hmono)
      omega)
  have hresult := hfold.sigma_snd.bitPair_snd
  have hfinal (value : Σ n, M n × ℕ) :
      (binaryEncoding value.2.2).reverse.foldl powerStep ⟨value.1, value.2.1, 1⟩ =
        ⟨value.1, value.2.1, value.2.1 ^ value.2.2⟩ := by
    rw [foldl_powerStep, List.foldl_reverse, foldr_pow]
    simp [binaryEncoding]
  convert hresult using 1
  funext value
  simp only [pairEncoding_apply, List.BitPair.snd_encode]
  rw [hfinal value]

end Turing.MultiTapeTM
