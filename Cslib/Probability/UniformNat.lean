/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.BitString
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bounded binary indices

Decode a word as a binary natural number, saturating at an explicit bound. Saturation lets
algorithms charge for a unary result even when given an arbitrarily long input word. On a
uniform `k`-bit word, decoding is a uniform index below `2^k`, capped at the supplied bound.
-/

@[expose] public section

namespace Cslib.Probability

/-- The natural number represented by a word, most significant bit first. -/
def binaryValue (word : List Bool) : ℕ :=
  word.foldl (fun value bit => 2 * value + bit.toNat) 0

/-- Decode binary digits with a saturating accumulator. -/
def boundedBinaryValue (bound : ℕ) (word : List Bool) : ℕ :=
  word.foldl (fun value bit => min bound (2 * value + bit.toNat)) 0

private theorem min_binary_step (bound value : ℕ) (bit : Bool) :
    min bound (2 * min bound value + bit.toNat) = min bound (2 * value + bit.toNat) := by
  by_cases h : value ≤ bound
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left (by lia), Nat.min_eq_left (by lia)]

/-- Saturating at each step agrees with capping the final mathematical value. -/
theorem boundedBinaryValue_eq (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word = min bound (binaryValue word) := by
  have h (word : List Bool) (value : ℕ) :
      word.foldl (fun value bit => min bound (2 * value + bit.toNat)) (min bound value) =
        min bound (word.foldl (fun value bit => 2 * value + bit.toNat) value) := by
    induction word generalizing value with
    | nil => rfl
    | cons bit word ih => simp only [List.foldl_cons, min_binary_step, ih]
  simpa only [boundedBinaryValue, binaryValue, Nat.min_zero] using h word 0

/-- The unary result never exceeds the declared bound. -/
theorem boundedBinaryValue_le (bound : ℕ) (word : List Bool) :
    boundedBinaryValue bound word ≤ bound := by
  rw [boundedBinaryValue_eq]
  exact Nat.min_le_left _ _

/-- An all-one binary word represents one less than the corresponding power of two. -/
theorem binaryValue_replicate_true (k : ℕ) :
    binaryValue (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => simp [binaryValue]
  | succ k ih =>
    rw [List.replicate_succ']
    simp only [binaryValue, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Bool.toNat_true] at *
    rw [pow_succ]
    lia

/-- A power-of-two sampling range strictly larger than the supplied bound. -/
def dyadicSize (bound : ℕ) : ℕ := 2 ^ (Nat.log 2 bound + 1)

/-- The sampling range is positive, including at zero. -/
theorem dyadicSize_pos (bound : ℕ) : 0 < dyadicSize bound := by
  unfold dyadicSize
  positivity

instance (bound : ℕ) : NeZero (dyadicSize bound) := ⟨(dyadicSize_pos bound).ne'⟩

/-- Every index at most the original bound lies in the dyadic range. -/
theorem lt_dyadicSize (bound : ℕ) : bound < dyadicSize bound :=
  Nat.lt_pow_succ_log_self (by decide) bound

/-- Rounding up to a power of two increases the range by at most a factor of two. -/
theorem dyadicSize_le (bound : ℕ) : dyadicSize bound ≤ 2 * (bound + 1) := by
  by_cases h : bound = 0
  · simp [h, dyadicSize]
  · have hpow := Nat.pow_log_le_self 2 h
    unfold dyadicSize
    rw [pow_succ]
    lia

/-- The sampling range grows only linearly with its bound. -/
@[fun_prop] theorem dyadicSize_polynomiallyBounded : PolynomiallyBounded dyadicSize :=
  PolynomiallyBounded.mono (g := fun n => 2 * (n + 1)) (by fun_prop) dyadicSize_le

/-- The dyadic range has a bounded unary implementation via the existing binary decoder. -/
theorem dyadicSize_eq_boundedBinaryValue (bound : ℕ) :
    dyadicSize bound =
      boundedBinaryValue (2 * bound + 1) (List.replicate (Nat.log 2 bound + 1) true) + 1 := by
  rw [boundedBinaryValue_eq]
  have h := binaryValue_replicate_true (Nat.log 2 bound + 1)
  have hle := dyadicSize_le bound
  change _ = dyadicSize bound at h
  rw [Nat.min_eq_right (by lia)]
  exact h.symm

/-- Binary decoding identifies fair bit strings with uniform finite indices. -/
theorem uniformBits_binaryValue (k : ℕ) :
    (uniformBits k).map binaryValue = (PMF.uniformOfFintype (Fin (2 ^ k))).map Fin.val := by
  induction k with
  | zero => simp [binaryValue, PMF.map, Function.comp_def]
  | succ k ih =>
    let e : Fin (2 ^ k) × Bool ≃ Fin (2 ^ (k + 1)) :=
      (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
        (finProdFinEquiv.trans (finCongr (pow_succ 2 k).symm))
    have he (i : Fin (2 ^ k)) (bit : Bool) : (e (i, bit)).val = 2 * i.val + bit.toNat := by
      cases bit <;> simp [e, finProdFinEquiv, finTwoEquiv, Nat.add_comm]
    have hsnoc (word : List Bool) (bit : Bool) :
        binaryValue (word ++ [bit]) = 2 * binaryValue word + bit.toNat := by
      simp [binaryValue, List.foldl_append]
    calc
      (uniformBits (k + 1)).map binaryValue =
          ((uniformBits k).map binaryValue).bind (fun value =>
            (PMF.uniformOfFintype Bool).map (fun bit => 2 * value + bit.toNat)) := by
        simp [uniformBits_snoc, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def, hsnoc]
      _ = (PMF.uniformOfFintype (Fin (2 ^ k) × Bool)).map (fun pair => (e pair).val) := by
        rw [ih, PMF.bind_map, PMF.uniformOfFintype_prod, PMF.map_bind]
        simp [PMF.map_comp, Function.comp_def, he]
      _ = ((PMF.uniformOfFintype (Fin (2 ^ k) × Bool)).map e).map Fin.val := by
        rw [PMF.map_comp]; rfl
      _ = _ := by rw [PMF.uniformOfFintype_map_equiv]

/-- A capped uniform index can be sampled using exactly `k` fair bits. -/
theorem uniformBits_boundedBinaryValue (bound k : ℕ) :
    (uniformBits k).map (boundedBinaryValue bound) =
      (PMF.uniformOfFintype (Fin (2 ^ k))).map (fun i => min bound i.val) := by
  rw [show boundedBinaryValue bound = (min bound ·) ∘ binaryValue by
    funext word; exact boundedBinaryValue_eq bound word]
  rw [← PMF.map_comp, uniformBits_binaryValue, PMF.map_comp]
  rfl

/-- Comparing a uniform finite index with a threshold samples the corresponding capped fraction. -/
theorem uniformFin_decide_lt (size threshold : ℕ) [NeZero size] :
    ((PMF.uniformOfFintype (Fin size)).map (fun i => decide (i.val < threshold))) true =
      (↑(min size threshold) : ENNReal) / size := by
  rw [PMF.uniformOfFintype_map_apply]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, decide_eq_true_eq,
    Fin.card_filter_val_lt, Fintype.card_fin]

end Cslib.Probability
