/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.Iteration
public import Cslib.Computability.Probabilistic.Encoding

/-!
# Polynomial-time bounded iteration

The public iteration rule combines efficient initialization, an efficient unary iteration count,
and an efficient step function, together with a polynomial bound on intermediate word lengths.
Machine construction and simulation proofs live in
`Cslib.Computability.Probabilistic.Realization.Iteration`.
Algorithm-level efficiency proofs use the closure theorems without unpacking their witnesses.

`IsPolyTime.iterate_spec` is the invariant rule: prove initialization, preservation, and an
intermediate-size bound locally. It returns both the loop's efficiency certificate and its final
invariant. `iterate_with_spec` allows the body to capture the original input, and
`iterate_with_bounded_growth` derives the invariant from a polynomial per-step growth bound.
`IsPolyTime.iterate_of_length_le` handles length-nonincreasing bodies automatically.
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

/-- A deterministic loop may capture its input. The invariant and size bound describe only
the changing state; the closure rule accounts for preserving the captured value. -/
theorem IsPolyTime.iterate_with_spec {α State : Type}
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : α → State → State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPolyTime (pairEncoding input stateEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    (invariant : α → ℕ → State → Prop) (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      invariant a (i + 1) (step a state))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size (input a).length) :
    IsPolyTime input (fun a => stateEncoding ((step a)^[count a] (initial a))) ∧
      ∀ a, invariant a (count a) ((step a)^[count a] (initial a)) := by
  let packed (pair : α × State) := (pair.1, step pair.1 pair.2)
  have htrace (a : α) (i : ℕ) :
      packed^[i] (a, initial a) = (a, (step a)^[i] (initial a)) := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [Function.iterate_succ_apply', ih, packed]
  have h := ((isPolyTime_input input).pair hinitial).iterate_encoded_spec (step := packed) hcount
    ((isPolyTime_fst input stateEncoding).pair hstep)
    (fun a i pair => pair.1 = a ∧ invariant a i pair.2)
    (fun a => ⟨rfl, hinit a⟩)
    (by rintro a i ⟨captured, state⟩ hi ⟨rfl, hs⟩; exact ⟨rfl, hpreserve captured i state hi hs⟩)
    (size := fun n => 2 * n + size n + 1) (by fun_prop)
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hs⟩
      simp only [length_pairEncoding]
      have := hbound captured i state hi hs
      lia)
  exact ⟨by simpa only [htrace] using h.1.snd, fun a => by simpa only [htrace] using (h.2 a).2⟩

/-- A captured loop with polynomially bounded per-step growth needs no explicit invariant.
The growth bound may depend on the size of the captured input. -/
theorem IsPolyTime.iterate_with_bounded_growth {α State : Type}
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : α → State → State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPolyTime (pairEncoding input stateEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    {growth : ℕ → ℕ} (hgrowth : PolynomiallyBounded growth)
    (hstepLength : ∀ a state, (stateEncoding (step a state)).length ≤
      (stateEncoding state).length + growth (input a).length) :
    IsPolyTime input (fun a => stateEncoding ((step a)^[count a] (initial a))) := by
  obtain ⟨ci, di, hi⟩ := hinitial.length_le
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hc
  exact (hinitial.iterate_with_spec hcount hstep
    (fun a i state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + i * growth (input a).length)
    (fun _ => by simp)
    (by intro a i state _ hs; have := hstepLength a state; nlinarith)
    (size := fun n => ci * (n + 1) ^ di + cc * (n + 1) ^ dc * growth n) (by fun_prop)
    (fun a i state hiCount hs => hs.trans
      (Nat.add_le_add (hi a) (Nat.mul_le_mul_right _ (hiCount.trans (hc a)))))).1

/-- A bounded loop may grow its encoded state by a fixed number of cells per iteration.
The initializer and unary iteration count supply the overall polynomial size bound. -/
theorem IsPolyTime.iterate_encoded_of_bounded_growth {α State : Type} {encode : α → Word}
    {stateEncoding : State → Word} {initial : α → State} {count : α → ℕ} {step : State → State}
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stateEncoding (fun state => stateEncoding (step state)))
    {growth : ℕ} (hgrowth : ∀ state,
      (stateEncoding (step state)).length ≤ (stateEncoding state).length + growth) :
    IsPolyTime encode (fun a => stateEncoding (step^[count a] (initial a))) := by
  obtain ⟨ci, di, hi⟩ := hinitial.length_le
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  simp only [List.length_replicate] at hc
  exact (hinitial.iterate_encoded_spec hcount hstep
    (fun a index state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + index * growth)
    (fun _ => by simp)
    (by intro a index state _ h; have := hgrowth state; nlinarith)
    (size := fun n => ci * (n + 1) ^ di + cc * (n + 1) ^ dc * growth) (by fun_prop)
    (fun a index state hindex h => h.trans
      (Nat.add_le_add (hi a) (Nat.mul_le_mul_right growth (hindex.trans (hc a)))))).1

/-- A loop whose encoded state never grows is the zero-growth special case. -/
theorem IsPolyTime.iterate_encoded_of_length_le {α State : Type} {encode : α → Word}
    {stateEncoding : State → Word} {initial : α → State} {count : α → ℕ} {step : State → State}
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stateEncoding (fun state => stateEncoding (step state)))
    (hshrink : ∀ state, (stateEncoding (step state)).length ≤ (stateEncoding state).length) :
    IsPolyTime encode (fun a => stateEncoding (step^[count a] (initial a))) :=
  hinitial.iterate_encoded_of_bounded_growth hcount hstep (growth := 0)
    (by simpa using hshrink)

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
