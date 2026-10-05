/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Measure

/-!
# Repeating an operation until acceptance

A rejected response performs another visible operation. Thus this construction represents
rejection sampling without requiring a proof that every sequence of responses terminates.
-/

@[expose] public section

namespace PFunctor.Resumption

universe uA uB v

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- Repeatedly perform `op` until `accept` returns a value. Each attempt is one operation. -/
def repeatUntil (op : P.A) (accept : P.B op → Option α) : Resumption P α :=
  corec (fun
    | none => .inr ⟨op, accept⟩
    | some a => .inl a) none

/-- An accepted response returns immediately; a rejected response starts the next attempt. -/
theorem repeatUntil_eq_query (op : P.A) (accept : P.B op → Option α) :
    repeatUntil op accept = query op (fun b => (accept b).elim (repeatUntil op accept) pure) := by
  apply dest_injective
  rw [repeatUntil, dest_corec, dest_query]
  apply congrArg Sum.inr
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext b
  change corec _ (accept b) = (accept b).elim _ pure
  cases hb : accept b with
  | none => rfl
  | some a =>
    apply dest_injective
    simp [dest_corec]

variable [∀ op, MeasurableSpace (P.B op)]
  [MeasurableSpace α] (μ : (op : P.A) → MeasureTheory.Measure (P.B op))

@[simp]
theorem outputMeasure_repeatUntil_zero (op : P.A) (accept : P.B op → Option α) :
    outputMeasure μ 0 (repeatUntil op accept) = 0 := by
  rw [repeatUntil_eq_query, outputMeasure_query_zero]

theorem outputMeasure_repeatUntil_succ (k : ℕ) (op : P.A) (accept : P.B op → Option α) :
    outputMeasure μ (k + 1) (repeatUntil op accept) = (μ op).bind (fun b =>
      (accept b).elim (outputMeasure μ k (repeatUntil op accept)) MeasureTheory.Measure.dirac) := by
  conv_lhs => rw [repeatUntil_eq_query]
  rw [outputMeasure_query_succ]
  apply MeasureTheory.Measure.bind_congr_right
  filter_upwards [] with b
  cases accept b <;> simp

/-- An operation that is always rejected never returns any value. -/
@[simp]
theorem returnedMeasure_repeatUntil_none (op : P.A) :
    returnedMeasure μ (repeatUntil op (fun _ => (none : Option α))) = 0 := by
  have h (k : ℕ) : outputMeasure μ k (repeatUntil op (fun _ => (none : Option α))) = 0 := by
    induction k with
    | zero => simp
    | succ k ih => simp [outputMeasure_repeatUntil_succ, ih]
  simp [returnedMeasure, h]

end PFunctor.Resumption
