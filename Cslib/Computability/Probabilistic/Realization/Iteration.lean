/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.PolynomialTime
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Iteration

/-!
# Polynomial-time bounded iteration

`IsPolyTime.iterate` packages the machine construction for a loop over words. Initialization,
the unary iteration count, and the step function must be polynomial time. A polynomial bound
on every intermediate word then gives one uniform polynomial-time machine for the complete loop.

The size hypothesis is essential: polynomially many applications of a polynomial-time function
can produce exponentially long words. The theorem accounts for initialization, computing the
count, every subroutine call, transfer of changing-length words, and writing the final result.
-/

@[expose] public section

namespace Cslib.Probability

open Turing Turing.MultiTapeTM

private theorem extend_restoring {k k' : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (hk : k ≤ k') (input result : Word) (cost : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result) :
    (tm.extendTapes (Fin.castLEEmb hk)).runFrom
      (wordsCfg input (some (tm.extendTapes (Fin.castLEEmb hk)).q₀) (fun _ => []) []) cost =
      wordsCfg input none (fun _ => []) result := by
  apply runFrom_extendTapes_words
  · exact h
  · intro i _
    rfl

/-- Compile a bounded trajectory whose subroutine accepts encoded values. Only reached words
need valid encodings. This internal rule supports both word iteration and typed composition. -/
theorem Realization.isPolyTime_of_trajectory {α β : Type} {encode : α → Word}
    {stepEncoding : β → Word} {values : α → ℕ → Word} {arguments : α → ℕ → β}
    {count : α → ℕ} {step : β → Word}
    (hinitial : IsPolyTime encode (fun a => values a 0))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stepEncoding step)
    (hargument : ∀ a index, index < count a → stepEncoding (arguments a index) = values a index)
    (hresult : ∀ a index, index < count a → step (arguments a index) = values a (index + 1))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hintermediate : ∀ a index, index ≤ count a →
      (values a index).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => values a (count a)) := by
  obtain ⟨ki, InitState, hfi, initMachine, ci, di, hi⟩ := hinitial.exists_restoring_machine
  obtain ⟨kc, CountState, hfc, countMachine, cc, dc, hc⟩ := hcount.exists_restoring_machine
  obtain ⟨ks, StepState, hfs, stepMachine, cs, ds, hs⟩ := hstep.exists_restoring_machine
  let : Finite InitState := hfi
  let : Finite CountState := hfc
  let : Finite StepState := hfs
  let k := ki + kc + ks
  let initializer := initMachine.extendTapes (Fin.castLEEmb (show ki ≤ k by dsimp [k]; lia))
  let counter := countMachine.extendTapes (Fin.castLEEmb (show kc ≤ k by dsimp [k]; lia))
  let body := stepMachine.extendTapes (Fin.castLEEmb (show ks ≤ k by dsimp [k]; lia))
  let initialTime := fun length => ci * (length + 1) ^ di
  let countTime := fun length => cc * (length + 1) ^ dc
  let stepTime := fun length => cs * (size length + 1) ^ ds
  have hinit (a : α) : initializer.runFrom
      (wordsCfg (encode a) (some initializer.q₀) (fun _ => []) []) (initialTime (encode a).length) =
      wordsCfg (encode a) none (fun _ => []) (values a 0) := by
    apply extend_restoring
    simpa using hi a []
  have hcounter (a : α) : counter.runFrom
      (wordsCfg (encode a) (some counter.q₀) (fun _ => []) []) (countTime (encode a).length) =
      wordsCfg (encode a) none (fun _ => []) (List.replicate (count a) true) := by
    apply extend_restoring
    simpa using hc a []
  have hbody (argument : β) : body.runFrom
      (wordsCfg (stepEncoding argument) (some body.q₀) (fun _ => []) [])
        (cs * ((stepEncoding argument).length + 1) ^ ds) =
      wordsCfg (stepEncoding argument) none (fun _ => []) (step argument) := by
    apply extend_restoring
    simpa only [List.nil_append] using hs argument []
  have hcountBound (a : α) : count a ≤ countTime (encode a).length := by
    have h := counter.length_output_runFrom_le
      (wordsCfg (encode a) (some counter.q₀) (fun _ => []) []) (countTime (encode a).length)
    rw [hcounter] at h
    simpa using h
  have hpoly : PolynomiallyBounded (fun length => initialTime length + countTime length +
      2 * size length + countTime length * (stepTime length + 3 * size length + 11) +
      countTime length + 7) := by fun_prop
  obtain ⟨coefficient, degree, hbound⟩ := hpoly
  let compiled := Iteration.machine initializer counter body
  apply isPolyTime_of_finite_machine compiled coefficient degree
  intro a
  have hsteps (index : ℕ) (hindex : index < count a) :
      body.runFrom (wordsCfg (values a index) (some body.q₀) (fun _ => []) [])
        (stepTime (encode a).length) =
        wordsCfg (values a index) none (fun _ => []) (values a (index + 1)) := by
    have hrun := hbody (arguments a index)
    rw [hargument a index hindex, hresult a index hindex] at hrun
    have htime : cs * ((values a index).length + 1) ^ ds ≤ stepTime (encode a).length :=
      Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
        (Nat.add_le_add_right (hintermediate a index (by lia)) 1) ds)
    rw [runFrom_eq_of_halt _ _ htime (by rw [hrun]; rfl)]
    exact hrun
  have hrun := Iteration.machine_spec initializer counter body
    (values a)
    (count a) (initialTime (encode a).length) (countTime (encode a).length)
    (stepTime (encode a).length) (size (encode a).length) (hinit a) (hcounter a) hsteps
    (hintermediate a)
  have htime :
      initialTime (encode a).length + countTime (encode a).length + 2 * size (encode a).length +
        count a * (stepTime (encode a).length + 3 * size (encode a).length + 11) + count a + 7 ≤
        coefficient * ((encode a).length + 1) ^ degree := by
    apply le_trans _ (hbound (encode a).length)
    have hmul := Nat.mul_le_mul_right
      (stepTime (encode a).length + 3 * size (encode a).length + 11) (hcountBound a)
    have := hcountBound a
    lia
  rw [runFrom_eq_of_halt _ _ htime hrun.1]
  exact hrun

/-- Iterate a certified transformation of encoded state. The loop compiler only supplies valid
encodings to the body; clients reason about ordinary values, including structured accumulators. -/
theorem IsPolyTime.iterate_encoded {α State : Type} {encode : α → Word}
    {stateEncoding : State → Word} {initial : α → State} {count : α → ℕ}
    {step : State → State}
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime stateEncoding (fun state => stateEncoding (step state)))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hintermediate : ∀ a index, index ≤ count a →
      (stateEncoding (step^[index] (initial a))).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding (step^[count a] (initial a))) :=
  Realization.isPolyTime_of_trajectory
    (values := fun a index => stateEncoding (step^[index] (initial a)))
    (arguments := fun a index => step^[index] (initial a))
    hinitial hcount hstep (fun _ _ _ => rfl)
    (fun _ _ _ => congrArg stateEncoding (Function.iterate_succ_apply' ..).symm)
    hsize hintermediate

/-- Iterate an efficient word transformation an efficiently computed number of times.
A polynomial bound on all intermediate words supplies a common polynomial step bound. -/
theorem IsPolyTime.iterate {α : Type} {encode : α → Word}
    {initial : α → Word} {count : α → ℕ} {step : Word → Word}
    (hinitial : IsPolyTime encode initial)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    (hstep : IsPolyTime wordEncoding step)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hintermediate : ∀ a index, index ≤ count a →
      (step^[index] (initial a)).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => step^[count a] (initial a)) :=
  hinitial.iterate_encoded (stateEncoding := wordEncoding) hcount hstep hsize hintermediate

end Cslib.Probability
