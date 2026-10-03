/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.UniformNat
public import Cslib.Tactic.PPT

/-!
# Sampling bounded indices in strict polynomial time

`sampleBoundedIndex bound` uses `log₂ bound + 1` fair bits. Each index strictly below `bound`
has the same probability; the remaining probability is assigned to the sentinel `bound`.
There is no unbounded rejection loop. Both binary decoding and its unary output are charged.

`sampleDyadicIndex bound` instead samples exactly uniformly below the next power of two.
Its range is at most `2 * (bound + 1)`, so the unary result remains polynomially bounded.
`sampleDyadicCoin bound numerator` compares such an index with `numerator`, sampling the exact
capped fraction `numerator / dyadicSize bound` with the same fixed supply of fair bits.
-/

@[expose] public section

namespace Cslib.Probability

/-- Saturating binary decoding has a polynomial-time unary implementation on all input words. -/
theorem boundedBinaryValue_isPolyTime : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
    (fun input => unaryEncoding (boundedBinaryValue input.1 input.2)) := by
  let advance (state : ℕ × ℕ) (bit : Bool) :=
    (state.1, min state.1 (2 * state.2 + bit.toNat))
  have hstep : IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) boolEncoding)
      (fun input => pairEncoding unaryEncoding unaryEncoding (advance input.1 input.2)) := by
    have hbit : IsPolyTime boolEncoding (fun bit => unaryEncoding bit.toNat) := by
      convert (isPolyTime_input boolEncoding).filter id using 1
      funext bit
      cases bit <;> rfl
    unfold advance
    polytime
  have hinput : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun input => input.2) := by polytime
  have hinitial : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun input => pairEncoding unaryEncoding unaryEncoding (input.1, 0)) := by polytime
  have hfold := hinput.foldl_spec hinitial hstep
    (fun input _ state => state.1 = input.1 ∧ state.2 ≤ input.1)
    (by simp) (by intro input consumed state bit _ h; simp [advance, h.1])
    (size := fun n => 3 * n + 1) (by fun_prop)
    (by
      intro input consumed state _ h
      simp [length_pairEncoding, unaryEncoding, wordEncoding]
      lia)
  have hstate (bound : ℕ) (word : Word) (value : ℕ) :
      word.foldl advance (bound, value) =
        (bound, word.foldl (fun value bit => min bound (2 * value + bit.toNat)) value) := by
    induction word generalizing value with
    | nil => rfl
    | cons bit word ih => simpa only [List.foldl_cons, advance] using ih _
  simpa only [hstate, boundedBinaryValue] using hfold.1.snd

/-- Decode efficiently available binary data under an efficiently available unary cap. -/
theorem IsPolyTime.boundedBinaryValue {α : Type} {input : α ↪ Word}
    {bound : α → ℕ} {word : α → Word}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => unaryEncoding
      (Cslib.Probability.boundedBinaryValue (bound a) (word a))) :=
  boundedBinaryValue_isPolyTime.comp_encoded (hbound.pair hword)

attribute [aesop safe apply (rule_sets := [PolyTime])] IsPolyTime.boundedBinaryValue

/-- The next power of two has an efficient unary implementation; its exponential expression
does not license an exponentially long output. The proved linear bound supplies the cap. -/
theorem IsPolyTime.dyadicSize {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding (Cslib.Probability.dyadicSize (bound a))) := by
  simp only [dyadicSize_eq_boundedBinaryValue]
  polytime

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeDyadicSize : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyUnaryHead #[(``dyadicSize, ``IsPolyTime.dyadicSize)]

-- Also recognize the expanded power-of-two expression in explicitly unfolded client programs.
attribute [aesop safe apply (rule_sets := [PolyTime])] IsPolyTime.dyadicSize

/-- Decode the first coordinate of a rectangular grid with a dyadic row width. -/
theorem IsPolyTime.div_dyadicSize {α : Type} {input : α ↪ Word} {index bound : α → ℕ}
    (hindex : IsPolyTime input (fun a => unaryEncoding (index a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding
      (index a / Cslib.Probability.dyadicSize (bound a))) := by
  unfold Cslib.Probability.dyadicSize
  exact hindex.unary_div_pow_two
    (hbound.unary_log2.unary_add (isPolyTime_const input (unaryEncoding 1)))

/-- Decode the second coordinate of a rectangular grid with a dyadic row width. -/
theorem IsPolyTime.mod_dyadicSize {α : Type} {input : α ↪ Word} {index bound : α → ℕ}
    (hindex : IsPolyTime input (fun a => unaryEncoding (index a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding
      (index a % Cslib.Probability.dyadicSize (bound a))) := by
  simpa only [Nat.mod_eq_sub_mul_div, Nat.mul_comm, unaryEncoding_apply] using
    hindex.unary_sub ((hindex.div_dyadicSize hbound).unary_mul hbound.dyadicSize)

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeDyadicCoordinates : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyUnaryHead
    #[(``HDiv.hDiv, ``IsPolyTime.div_dyadicSize), (``HMod.hMod, ``IsPolyTime.mod_dyadicSize)]

/-- An exact uniform index in a power-of-two range, using a fixed number of fair bits. -/
noncomputable def sampleDyadicIndex (bound : ℕ) : ProbComp ℕ :=
  boundedBinaryValue (dyadicSize bound) <$> OracleComp.sampleBits (Nat.log 2 bound + 1)

/-- The dyadic sampler has no rejection or approximation error. -/
theorem eval_sampleDyadicIndex (bound : ℕ) :
    ProbComp.eval (sampleDyadicIndex bound) =
      (PMF.uniformOfFintype (Fin (dyadicSize bound))).map Fin.val := by
  simp only [sampleDyadicIndex, ProbComp.eval, OracleComp.eval_map,
    OracleComp.eval_sampleBits, uniformBits_boundedBinaryValue]
  congr 1
  funext i
  exact Nat.min_eq_right i.isLt.le

/-- An efficiently supplied unary bound gives a strict PPT exact dyadic sampler. -/
theorem IsPolyTime.sampleDyadicIndex {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPPTOn input unaryEncoding (fun a => Cslib.Probability.sampleDyadicIndex (bound a)) := by
  unfold Cslib.Probability.sampleDyadicIndex
  ppt

/-- An exact dyadic coin, saturated at probability one when the numerator exceeds the range. -/
noncomputable def sampleDyadicCoin (bound numerator : ℕ) : ProbComp Bool := do
  let index ← sampleDyadicIndex bound
  return decide (index < numerator)

/-- The dyadic coin's exact acceptance probability, including the endpoints zero and one. -/
theorem eval_sampleDyadicCoin_true (bound numerator : ℕ) :
    ProbComp.eval (sampleDyadicCoin bound numerator) true =
      (↑(min (dyadicSize bound) numerator) : ENNReal) / dyadicSize bound := by
  simp only [sampleDyadicCoin, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleDyadicIndex, PMF.bind_map]
  exact uniformFin_decide_lt _ _

/-- The real-valued acceptance probability of the exact dyadic sampler. -/
theorem eval_sampleDyadicCoin_true_toReal (bound numerator : ℕ) :
    (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal =
      (↑(min (dyadicSize bound) numerator) : ℝ) / dyadicSize bound := by
  rw [eval_sampleDyadicCoin_true, ENNReal.toReal_div]
  simp

/-- Every positive dyadic acceptance probability is at least one over its sampling range. -/
theorem inv_dyadicSize_le_eval_sampleDyadicCoin (bound numerator : ℕ)
    (hpositive : 0 < (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal) :
    (1 : ℝ) / dyadicSize bound ≤
      (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal := by
  rw [eval_sampleDyadicCoin_true_toReal] at hpositive ⊢
  have hdenominator : (0 : ℝ) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  have hnum : 0 < min (dyadicSize bound) numerator := by
    exact_mod_cast (div_pos_iff_of_pos_right hdenominator).mp hpositive
  apply div_le_div_of_nonneg_right _ hdenominator.le
  exact_mod_cast Nat.succ_le_of_lt hnum

/-- Efficiently supplied unary parameters give a strict PPT dyadic coin. -/
theorem IsPolyTime.sampleDyadicCoin {α : Type} {input : α ↪ Word} {bound numerator : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hnumerator : IsPolyTime input (fun a => unaryEncoding (numerator a))) :
    IsPPTOn input boolEncoding
      (fun a => Cslib.Probability.sampleDyadicCoin (bound a) (numerator a)) := by
  unfold Cslib.Probability.sampleDyadicCoin
  ppt

/-- A capped fair-bit index, with `bound` denoting rejection. -/
noncomputable def sampleBoundedIndex (bound : ℕ) : ProbComp ℕ :=
  boundedBinaryValue bound <$> OracleComp.sampleBits (Nat.log 2 bound + 1)

/-- The sampler's exact distribution, including its rejection mass. -/
theorem eval_sampleBoundedIndex (bound : ℕ) :
    ProbComp.eval (sampleBoundedIndex bound) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 bound + 1)))).map (fun i => min bound i.val) := by
  simp [sampleBoundedIndex, ProbComp.eval, uniformBits_boundedBinaryValue]

/-- An efficiently supplied unary bound gives a uniform PPT index sampler. -/
theorem IsPolyTime.sampleBoundedIndex {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPPTOn input unaryEncoding (fun a => Cslib.Probability.sampleBoundedIndex (bound a)) := by
  have hdecode := boundedBinaryValue_isPolyTime
  unfold Cslib.Probability.sampleBoundedIndex
  ppt

-- Select the actual sampler before unification. Their implementations are deliberately similar,
-- but unfolding one while trying to certify the other needlessly expands arithmetic and encodings.
@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptIndex : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[
    (``sampleBoundedIndex, ``IsPolyTime.sampleBoundedIndex),
    (``sampleDyadicIndex, ``IsPolyTime.sampleDyadicIndex),
    (``sampleDyadicCoin, ``IsPolyTime.sampleDyadicCoin)]

end Cslib.Probability
