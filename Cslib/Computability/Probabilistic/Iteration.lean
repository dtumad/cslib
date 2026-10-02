/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.Iteration
public import Cslib.Computability.Probabilistic.PolynomialTime

/-!
# Polynomial-time bounded iteration

The public iteration rule combines efficient initialization, an efficient unary iteration count,
and an efficient step function, together with a polynomial bound on intermediate word lengths.
Machine construction and simulation proofs live in
`Cslib.Computability.Probabilistic.Realization.Iteration`.
Algorithm-level efficiency proofs use the closure theorems without unpacking their witnesses.

`IsPolyTime.iterate_spec` is the invariant rule: prove initialization, preservation, and an
intermediate-size bound locally. It returns both the loop's efficiency certificate and its final
invariant. `IsPolyTime.iterate_of_length_le` handles length-nonincreasing bodies automatically.
-/

@[expose] public section

namespace Cslib.Probability

/-- A Hoare-style rule for bounded iteration. The same invariant proves the final postcondition
and controls intermediate sizes, so polynomial-time certification needs no execution traces. -/
theorem IsPolyTime.iterate_encoded_spec {α State : Type} {encode : α → Word}
    {stateEncoding : State → Word} {initial : α → State} {count : α → ℕ} {step : State → State}
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stateEncoding (fun state => stateEncoding (step state)))
    (invariant : α → ℕ → State → Prop)
    (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a index state, index < count a → invariant a index state →
      invariant a (index + 1) (step state))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a index state, index ≤ count a → invariant a index state →
      (stateEncoding state).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding (step^[count a] (initial a))) ∧
      ∀ a, invariant a (count a) (step^[count a] (initial a)) := by
  have htrace (a : α) (index : ℕ) (hindex : index ≤ count a) :
      invariant a index (step^[index] (initial a)) := by
    induction index with
    | zero => exact hinit a
    | succ index ih =>
      simpa only [Function.iterate_succ_apply'] using
        hpreserve a index _ (by lia) (ih (by lia))
  exact ⟨hinitial.iterate_encoded (stateEncoding := stateEncoding) hcount hstep hsize
    (fun a index hi => hbound a index _ hi (htrace a index hi)),
    fun a => htrace a (count a) le_rfl⟩

/-- The invariant rule specialized to ordinary word state. -/
theorem IsPolyTime.iterate_spec {α : Type} {encode : α → Word}
    {initial : α → Word} {count : α → ℕ} {step : Word → Word}
    (hinitial : IsPolyTime encode initial)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime wordEncoding step)
    (invariant : α → ℕ → Word → Prop)
    (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a index word, index < count a → invariant a index word →
      invariant a (index + 1) (step word))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a index word, index ≤ count a → invariant a index word →
      word.length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => step^[count a] (initial a)) ∧
      ∀ a, invariant a (count a) (step^[count a] (initial a)) :=
  hinitial.iterate_encoded_spec (stateEncoding := wordEncoding)
    hcount hstep invariant hinit hpreserve hsize hbound

/-- A loop whose encoded state never grows inherits its initializer's polynomial size bound. -/
theorem IsPolyTime.iterate_encoded_of_length_le {α State : Type} {encode : α → Word}
    {stateEncoding : State → Word} {initial : α → State} {count : α → ℕ} {step : State → State}
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stateEncoding (fun state => stateEncoding (step state)))
    (hshrink : ∀ state, (stateEncoding (step state)).length ≤ (stateEncoding state).length) :
    IsPolyTime encode (fun a => stateEncoding (step^[count a] (initial a))) := by
  obtain ⟨c, d, hlength⟩ := hinitial.length_le
  exact (hinitial.iterate_encoded_spec hcount hstep
    (fun a _ state => (stateEncoding state).length ≤ (stateEncoding (initial a)).length)
    (fun _ => le_rfl) (fun _ _ state _ h => (hshrink state).trans h)
    (size := fun length => c * (length + 1) ^ d) ⟨c, d, fun _ => le_rfl⟩
    (fun a _ _ _ h => h.trans (hlength a))).1

/-- An efficiently bounded word loop with a length-nonincreasing body is polynomial time. -/
theorem IsPolyTime.iterate_of_length_le {α : Type} {encode : α → Word}
    {initial : α → Word} {count : α → ℕ} {step : Word → Word}
    (hinitial : IsPolyTime encode initial)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime wordEncoding step)
    (hshrink : ∀ word, (step word).length ≤ word.length) :
    IsPolyTime encode (fun a => step^[count a] (initial a)) :=
  hinitial.iterate_encoded_of_length_le (stateEncoding := wordEncoding) hcount hstep hshrink

end Cslib.Probability
