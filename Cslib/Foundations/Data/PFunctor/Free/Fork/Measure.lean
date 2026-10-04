/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Option
public import Cslib.Foundations.MeasureTheory.Sigma

/-! # Measure semantics of adaptive forking -/

public section

namespace PFunctor.FreeM

open MeasureTheory

universe u

variable {P : PFunctor.{u, u}} {α : Type u}
  [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- Forking preserves the law of the first execution. Losslessness matters: the optional
second execution must not discard mass from the already completed first one. -/
theorem denote_fork_map_fst (select : P.A → Bool) (choose : α → Option ℕ) (x : P.FreeM α) :
    (denote μ (fork select choose x)).map Prod.fst = denote μ x := by
  induction x generalizing choose with
  | pure a =>
    rw [fork_pure, denote_pure, denote_pure, Measure.map_dirac' measurable_fst]
  | lift_bind op cont ih =>
    rw [← denote_map _ _ _ measurable_fst]
    change denote μ ((fun out : α × Option ((op : P.A) × P.B op × P.B op × α) => out.1) <$>
      (do
      let answer ← lift op
      let first ← fork select (if select op then
        fun a => match choose a with | some (n + 1) => some n | _ => none
        else choose) (cont answer)
      if select op && (choose first.1 == some 0) then
        let answer' ← lift op
        let second ← cont answer'
        pure (first.1, some ⟨op, answer, answer', second⟩)
      else pure first)) = denote μ (lift op >>= cont)
    simp only [_root_.map_bind, denote_bind_of_discrete, denote_lift]
    congr 1
    funext answer
    have hfinish (first : α × Option ((op : P.A) × P.B op × P.B op × α)) :
        denote μ ((fun out : α × Option ((op : P.A) × P.B op × P.B op × α) => out.1) <$>
        (if select op && (choose first.1 == some 0) then do
          let answer' ← lift op
          let second ← cont answer'
          pure (first.1, some ⟨op, answer, answer', second⟩)
        else pure first)) = Measure.dirac first.1 := by
      split
      · simp only [_root_.map_bind, LawfulApplicative.map_pure, denote_bind_of_discrete,
          denote_pure, denote_lift]
        simp_rw [Measure.bind_const, measure_univ, one_smul]
        rw [Measure.bind_const, measure_univ, one_smul]
      · exact rfl
    simp_rw [hfinish]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
    exact ih answer _

end PFunctor.FreeM
