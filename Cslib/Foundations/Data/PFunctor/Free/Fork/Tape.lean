/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork.Replay
public import Cslib.Foundations.Data.PFunctor.Free.Measure.Support
public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape
public import Cslib.Foundations.MeasureTheory.Sigma
import Cslib.Foundations.MeasureTheory.Bind

/-!
# Forking with finite answer tapes

For a common answer type, replay needs only the recorded answers. Splicing the first run's
prefix onto a fresh tape executes the exact forked continuation from the original program.
Private randomness supplied as program input is consequently shared across both runs.
-/

@[expose] public section

namespace PFunctor.FreeM

universe u

open MeasureTheory

variable {Operation Answer α : Type u} [DecidableEq Operation]

/-- Restart from the beginning using the old answer prefix followed by a fresh tape.
An absent fork point is a successful execution without a second result; tape exhaustion fails. -/
def restartFromAnswers (select : Operation → Bool) (index : ℕ)
    (events : List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B))
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α) (answers : List Answer) :
    Option (Option ((_ : Operation) × Answer × Answer × α)) :=
  (forkPrefix select index events).elim (some none) fun (before, ⟨op, answer⟩) => do
    let answer' ← answers.head?
    let second ← runFromAnswers program (before.map (fun event => event.2) ++ answers)
    pure (some ⟨op, answer, answer', second⟩)

/-- Replaying a recorded prefix through a tape gives exactly the semantic fork's second run,
including its operation, old and new answers, output, and any exhaustion. -/
theorem restartFromAnswers_eq (select : Operation → Bool) (index : ℕ)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    {value : α} {events : List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)}
    (h : MonadAttach.CanReturn (trace program) (value, events)) (answers : List Answer) :
    restartFromAnswers select index events program answers =
      runFromAnswers (restartAtTrace select index events program) answers := by
  induction program generalizing index value events with
  | pure result =>
    have heq : (value, events) = (result, []) := h
    cases heq
    rfl
  | lift_bind op cont ih =>
    obtain ⟨answer, after, hafter, rfl⟩ := (canReturn_trace_lift_bind op cont value events).mp h
    change restartFromAnswers select index (⟨op, answer⟩ :: after) (.liftBind op cont) answers = _
    cases hs : select op with
    | false =>
      simp only [restartFromAnswers, restartAtTrace, forkPrefix, hs, Bool.false_eq_true,
        ↓reduceIte]
      cases hp : forkPrefix select index after with
      | none => rfl
      | some focus =>
        rcases focus with ⟨before, event⟩
        simpa only [restartFromAnswers, restartAtTrace, hp, Option.map_some, Option.elim_some,
          List.map_cons, List.cons_append, liftBind_eq, bind_eq_bind,
          runFromAnswers_lift_bind_cons (Operation := Operation),
          runWithReplay_lift_bind_cons (P := PFunctor.mk Operation (fun _ => Answer))] using
            ih answer index hafter
    | true =>
      cases index with
      | zero =>
        cases answers with
        | nil =>
          simp only [restartFromAnswers, restartAtTrace, forkPrefix, hs, ↓reduceIte,
            Option.elim_some]
          rfl
        | cons answer' rest =>
          simp only [restartFromAnswers, restartAtTrace, forkPrefix, hs, ↓reduceIte,
            Option.elim_some, liftBind_eq, bind_eq_bind, List.map_nil, List.nil_append,
            runWithReplay_lift_bind_cons (P := PFunctor.mk Operation (fun _ => Answer)),
            runWithReplay_nil (P := PFunctor.mk Operation (fun _ => Answer)),
            ← map_eq_pure_bind, runFromAnswers_map,
            runFromAnswers_lift_bind_cons (Operation := Operation)]
          simp [Option.map_map, Function.comp_def]
      | succ index =>
        simp only [restartFromAnswers, restartAtTrace, forkPrefix, hs, ↓reduceIte]
        cases hp : forkPrefix select index after with
        | none => rfl
        | some focus =>
          rcases focus with ⟨before, event⟩
          simpa only [restartFromAnswers, restartAtTrace, hp, Option.map_some, Option.elim_some,
            List.map_cons, List.cons_append, liftBind_eq, bind_eq_bind,
            runFromAnswers_lift_bind_cons (Operation := Operation),
            runWithReplay_lift_bind_cons (P := PFunctor.mk Operation (fun _ => Answer))] using
              ih answer index hafter

/-- Run once on the first tape, then replay its selected prefix with fresh answers. Both
results are retained. The outer option distinguishes tape exhaustion from an absent fork. -/
def forkFromAnswers (select : Operation → Bool) (choose : α → Option ℕ)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers fresh : List Answer) :
    Option (α × Option ((_ : Operation) × Answer × Answer × α)) := do
  let (first, events) ← runFromAnswers (trace program) answers
  let second ← (choose first).elim (some none)
    (fun index => restartFromAnswers select index events program fresh)
  pure (first, second)

variable {P : PFunctor.{u, u}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [Countable Operation] [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [Countable Answer] [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- A source-length fresh tape implements the semantic restart exactly. In particular, unused
answers do not change its law and there is no conditioning on successful sampling. -/
theorem denote_restartFromAnswers (sample : P.FreeM Answer) (select : Operation → Bool)
    (index : ℕ) (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    {value : α} {events : List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)}
    (h : MonadAttach.CanReturn (trace program) (value, events))
    (count : ℕ) (hcount : queryBound program ≤ count) :
    denote μ (restartFromAnswers select index events program <$>
      (List.replicate count ()).mapM (fun _ => sample)) =
        (denote (P := PFunctor.mk Operation (fun _ => Answer))
          (fun _ => denote μ sample) (restartAtTrace select index events program)).map some := by
  have heq : restartFromAnswers select index events program =
      runFromAnswers (restartAtTrace select index events program) :=
    funext (restartFromAnswers_eq select index program h)
  rw [heq]
  apply denote_runFromAnswers
  have hbound := queryBoundP_restartAtTrace_le (fun _ => true) select index program h
  simp only [queryBoundP_true] at hbound
  exact hbound.trans hcount

omit [DecidableEq Operation] in
/-- Two independently sampled source-length tapes realize the entire adaptive fork. The
equality retains both outputs and the selected operation and answers, even when the selector
declines to fork or the fresh suffix follows a different path. -/
theorem denote_forkFromAnswers (sample : P.FreeM Answer) (select : Operation → Bool)
    (choose : α → Option ℕ)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (count : ℕ) (hcount : queryBound program ≤ count) :
    denote μ (do
      let answers ← (List.replicate count ()).mapM (fun _ => sample)
      let fresh ← (List.replicate count ()).mapM (fun _ => sample)
      pure (forkFromAnswers select choose program answers fresh)) =
        (denote (P := PFunctor.mk Operation (fun _ => Answer))
          (fun _ => denote μ sample) (fork select choose program)).map some := by
  classical
  let : MeasurableSpace (List Answer) := ⊤
  let : MeasurableSpace (List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) := ⊤
  let tape := (List.replicate count ()).mapM (fun _ => sample)
  let law := fun _ : Operation => denote μ sample
  let finish (first : Option (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))
      (fresh : List Answer) := do
    let (value, events) ← first
    let second ← (choose value).elim (some none)
      (fun index => restartFromAnswers select index events program fresh)
    pure (value, second)
  simp only [← map_eq_pure_bind]
  change denote μ (tape >>= fun answers =>
    finish (runFromAnswers (trace program) answers) <$> tape) = _
  have hfirst := denote_runFromAnswers μ sample (trace program) count (by
    rwa [← queryBoundP_true (trace program), queryBoundP_trace,
      queryBoundP_true])
  have hsplit : denote μ (tape >>= fun answers =>
      finish (runFromAnswers (trace program) answers) <$> tape) =
      (denote μ (runFromAnswers (trace program) <$> tape)).bind
        (fun first => denote μ (finish first <$> tape)) := by
    simp only [← map_eq_map]
    rw [denote_map μ _ _ Measurable.of_discrete,
      Measure.bind_map _ Measurable.of_discrete Measurable.of_discrete,
      denote_bind_of_discrete]
    rfl
  rw [hsplit, hfirst, Measure.bind_map _ Measurable.of_discrete Measurable.of_discrete,
    fork_eq_forkWithReplay]
  conv_rhs => rw [← denote_map _ _ some Measurable.of_discrete]
  simp only [forkWithReplay, map_eq_map, _root_.map_bind,
    denote_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [ae_canReturn law (trace program)] with first hfirst
  rcases first with ⟨value, events⟩
  change denote μ ((fun fresh => do
    let second ← (choose value).elim (some none)
      (fun index => restartFromAnswers select index events program fresh)
    pure (value, second)) <$> tape) = _
  cases hc : choose value with
  | none =>
    simp only [Option.elim_none, ← map_eq_map]
    rw [denote_map μ _ _ Measurable.of_discrete, Measure.map_const]
    simp [tape, Measure.dirac_bind Measurable.of_discrete]
  | some index =>
    simp only [Option.elim_some]
    have hrestart := denote_restartFromAnswers μ sample select index program hfirst count hcount
    have hmap : (fun fresh => do
        let second ← restartFromAnswers select index events program fresh
        pure (value, second)) =
        (fun out => out.map (Prod.mk value)) ∘
          restartFromAnswers select index events program := by
      funext fresh
      dsimp only [Function.comp_apply]
      cases restartFromAnswers select index events program fresh <;> rfl
    rw [hmap]
    rw [Function.comp_def,
      ← Functor.map_map (restartFromAnswers select index events program)]
    simp only [← map_eq_map] at hrestart ⊢
    rw [denote_map μ _ _ Measurable.of_discrete, hrestart,
      Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    simp only [map_eq_map, LawfulApplicative.map_pure, denote_pure]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
    rfl

end PFunctor.FreeM
