/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered
public import Cslib.Foundations.MeasureTheory.Option

/-!
# Finite answer tapes

For operations with one common answer type, a finite list can supply the answers in order.
Exhaustion is explicit. Sampling a tape long enough for every path preserves the entire result
measure, including when requests depend on earlier answers and some tape entries go unused.
-/

@[expose] public section

namespace PFunctor.FreeM

open MeasureTheory

universe u

variable {Operation Answer α : Type u}

/-- Consume the next saved answer, failing if the tape is exhausted. -/
def readAnswer : StateT (List Answer) Option Answer
  | [] => none
  | answer :: rest => some (answer, rest)

/-- Interpret each request using the next tape entry. Unused entries are discarded on return. -/
def runFromAnswers (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) : Option α :=
  ((program.liftM (m := StateT (List Answer) Option) (fun _ => readAnswer)).run answers).map
    Prod.fst

@[simp] theorem runFromAnswers_pure (value : α) (answers : List Answer) :
    runFromAnswers (Operation := Operation) (pure value) answers = some value := rfl

@[simp] theorem runFromAnswers_lift_bind_nil (op : Operation)
    (cont : Answer → (PFunctor.mk Operation (fun _ => Answer)).FreeM α) :
    runFromAnswers (lift op >>= cont) [] = none := rfl

@[simp] theorem runFromAnswers_lift_bind_cons (op : Operation)
    (cont : Answer → (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answer : Answer) (rest : List Answer) :
    runFromAnswers (lift op >>= cont) (answer :: rest) = runFromAnswers (cont answer) rest := rfl

/-- Supplying answers cannot create a result absent from the source program. -/
theorem canReturn_of_runFromAnswers
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) {value : α} (h : runFromAnswers program answers = some value) :
    MonadAttach.CanReturn program value := by
  induction program generalizing answers with
  | pure result => simpa using h.symm
  | lift_bind op cont ih =>
    cases answers with
    | nil => cases h
    | cons answer rest => exact ⟨answer, ih answer rest h⟩

/-- Every tape at least as long as the worst-case query count suffices, regardless of its
contents. This is independent of any sampling distribution. -/
theorem runFromAnswers_isSome
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) (h : queryBound program ≤ answers.length) :
    (runFromAnswers program answers).isSome := by
  induction program generalizing answers with
  | pure value => rfl
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le (fun _ => true) op cont answers.length (by simpa using h)
    cases answers with
    | nil => simp at hcost
    | cons answer rest =>
      exact ih answer rest (by simpa using hcost.2 answer)

variable {P : PFunctor.{u, u}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- Presampling independent answers preserves the whole output measure of an adaptive
program. The pathwise bound ensures that tape exhaustion has zero probability. -/
theorem denote_runFromAnswers (sample : P.FreeM Answer)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (count : ℕ) (hcount : queryBound program ≤ count) :
    denote μ (runFromAnswers program <$> (List.replicate count ()).mapM (fun _ => sample)) =
      (denote (P := PFunctor.mk Operation (fun _ => Answer))
        (fun _ => denote μ sample) program).map some := by
  let : MeasurableSpace (List Answer) := ⊤
  induction program generalizing count with
  | pure value =>
    change denote μ ((fun _ : List Answer => some value) <$>
      (List.replicate count ()).mapM (fun _ => sample)) = _
    rw [← map_eq_map, denote_map μ _ _ Measurable.of_discrete, Measure.map_const]
    simp
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le (fun _ => true) op cont count (by simpa using hcount)
    cases count with
    | zero => simp at hcost
    | succ count =>
      have hrun : runFromAnswers (lift op >>= cont) <$>
          (List.replicate (count + 1) ()).mapM (fun _ => sample) =
            sample >>= fun answer => runFromAnswers (cont answer) <$>
              (List.replicate count ()).mapM (fun _ => sample) := by
        simp only [List.replicate_succ, List.mapM_cons, map_eq_pure_bind,
          LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
        rfl
      rw [bind_eq_bind, hrun, denote_bind_of_discrete]
      apply Measure.ext
      intro event hevent
      rw [Measure.bind_apply hevent Measurable.of_discrete.aemeasurable,
        Measure.map_apply Measurable.of_discrete hevent,
        denote_bind_of_discrete, denote_lift,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      apply lintegral_congr
      intro answer
      rw [ih answer count (by simpa using hcost.2 answer),
        Measure.map_apply Measurable.of_discrete hevent]

end PFunctor.FreeM
