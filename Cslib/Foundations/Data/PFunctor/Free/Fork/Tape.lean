/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork.Replay
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape
public import Cslib.Foundations.MeasureTheory.Sigma
import Cslib.Foundations.MeasureTheory.Bind
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability

/-!
# Forking with finite answer tapes

For a common answer type, replay needs only the recorded answers. Splicing the first run's
prefix onto a fresh tape executes the exact forked continuation from the original program.
Private randomness supplied as program input is consequently shared across both runs.
The measure laws cover total and aborting interpreters, including averaging over a shared seed.
-/

@[expose] public section

namespace PFunctor.FreeM

section Replay

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

end Replay

section Probability

open MeasureTheory
open scoped ENNReal

universe u

variable {P : PFunctor.{u, u}} {Operation Answer α : Type u}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [Countable Operation] [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [Countable Answer] [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- The concrete forking inequality holds for two finite answer tapes. The outer `none`
means exhaustion and contributes no success; a source-length tape never exhausts. -/
theorem le_denote_forkFromAnswers (sample : P.FreeM Answer) (select : Operation → Bool)
    (choose : α → Option ℕ)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (count q : ℕ) (r : ℝ≥0∞) (hcount : queryBound program ≤ count)
    (hanswer : ∀ answer, denote μ sample {answer} ≤ r)
    (hvalid : ∀ a events, MonadAttach.CanReturn (trace program) (a, events) →
      ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let tape := (List.replicate count ()).mapM (fun _ => sample)
    let ε := denote μ (runFromAnswers program <$> tape)
      {out | ∃ value, out = some value ∧ ∃ n < q, choose value = some n}
    ε * (ε / q - r) ≤ denote μ (do
      let answers ← tape
      let fresh ← tape
      pure (forkFromAnswers select choose program answers fresh))
        {out | ∃ value, out = some value ∧ value ∈ ⋃ n,
          forkSuccess (P := PFunctor.mk Operation (fun _ => Answer)) choose n} := by
  dsimp only
  rw [denote_runFromAnswers μ sample program count hcount,
    denote_forkFromAnswers μ sample select choose program count hcount,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  simp only [Set.preimage_ofPred_eq, Option.some.injEq, exists_eq_left', Set.ofPred_mem_eq]
  exact le_denote_fork (fun _ => denote μ sample) select choose program q r
    (fun _ _ => hanswer) hvalid

/-- A private seed is sampled once and supplied to both executions. Averaging the conditional
finite-tape bounds preserves the usual quadratic loss in the overall first-run success rate. -/
theorem le_denote_forkFromAnswers_bind {Seed : Type u} [MeasurableSpace Seed]
    [DiscreteMeasurableSpace Seed]
    (seed : P.FreeM Seed) (sample : P.FreeM Answer)
    (program : Seed → (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (select : Operation → Bool) (choose : α → Option ℕ) (count q : ℕ) (r : ℝ≥0∞)
    (hcount : ∀ saved, MonadAttach.CanReturn seed saved → queryBound (program saved) ≤ count)
    (hanswer : ∀ answer, denote μ sample {answer} ≤ r)
    (hvalid : ∀ saved, MonadAttach.CanReturn seed saved →
      ∀ a events, MonadAttach.CanReturn (trace (program saved)) (a, events) →
        ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let tape := (List.replicate count ()).mapM (fun _ => sample)
    let ε := denote μ (seed >>= fun saved => runFromAnswers (program saved) <$> tape)
      {out | ∃ value, out = some value ∧ ∃ n < q, choose value = some n}
    ε * (ε / q - r) ≤ denote μ (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (forkFromAnswers select choose (program saved) answers fresh))
        {out | ∃ value, out = some value ∧ value ∈ ⋃ n,
          forkSuccess (P := PFunctor.mk Operation (fun _ => Answer)) choose n} := by
  let : MeasurableSpace (List Answer) := ⊤
  dsimp only
  rw [denote_bind_of_discrete, denote_bind_of_discrete]
  simp only [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  refine (ENNReal.mul_sub_lintegral_le Measurable.of_discrete.aemeasurable
    (fun _ => prob_le_one) q r).trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_canReturn μ seed] with saved hsaved
  exact le_denote_forkFromAnswers μ sample select choose (program saved) count q r
    (hcount saved hsaved) hanswer (hvalid saved hsaved)

end Probability

section Aborting

universe u

variable {Operation Answer α : Type u}

/-- Fork a partial traced interpreter by copying the selected answer prefix. Both executions
receive the same interpreter, which can close over a saved private seed. A failed execution,
absent selection, missing event, or empty fresh tape rejects the fork. -/
def forkFromTracedAnswers
    (run : List Answer → Option (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))
    (choose : α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) → Option ℕ)
    (answers fresh : List Answer) :
    Option ((α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) ×
      ((_ : Operation) × Answer × Answer ×
        (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))) := do
  let first ← run answers
  (choose first).elim none fun index => do
    let ⟨op, answer⟩ ← first.2[index]?
    let answer' ← fresh.head?
    let second ← run ((first.2.take index).map (fun event => event.2) ++ fresh)
    pure (first, ⟨op, answer, answer', second⟩)

/-- Discarding the logs of rejected runs commutes with replay, after rejecting any fork
whose first or second result failed. This is a pointwise equality for arbitrary tapes. -/
theorem forkFromTracedAnswers_eq
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (choose : α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) → Option ℕ)
    (answers fresh : List Answer) :
    forkFromTracedAnswers (fun tape => (runFromAnswers (trace program) tape).bind
      (fun out => out.1.map (fun value => (value, out.2)))) choose answers fresh =
      (forkFromAnswers (fun _ => true)
        (fun out => out.1.bind (fun value => choose (value, out.2)))
        (trace program) answers fresh).bind (fun out => do
          let first ← out.1.1
          let ⟨op, answer, answer', second, events⟩ ← out.2
          let second ← second
          pure ((first, out.1.2), ⟨op, answer, answer', second, events⟩)) := by
  classical
  unfold forkFromAnswers forkFromTracedAnswers
  rw [trace_trace, runFromAnswers_map]
  dsimp +instances only [Bind.bind, Option.bind]
  cases hfirst : runFromAnswers (trace program) answers with
  | none => rfl
  | some first =>
    rcases first with ⟨first, events⟩
    cases first with
    | none => rfl
    | some first =>
      simp only [Option.map_some]
      cases choose (first, events) with
      | none => rfl
      | some index =>
        simp only [Option.elim_some, restartFromAnswers, forkPrefix_true]
        cases events[index]? with
        | none => rfl
        | some event =>
          rcases event with ⟨op, answer⟩
          simp only [Option.map_some, Option.elim_some]
          dsimp +instances only [Bind.bind, Option.bind]
          cases fresh.head? with
          | none => rfl
          | some answer' =>
            cases runFromAnswers (trace program)
              ((events.take index).map (fun event => event.2) ++ fresh) with
            | none => rfl
            | some second =>
              rcases second with ⟨second, events'⟩
              cases second <;> rfl

open MeasureTheory

variable {P : PFunctor.{u, u}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [Countable Operation] [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [Countable Answer] [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  [MeasurableSpace (List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B))]
  [DiscreteMeasurableSpace (List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B))]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- A partial interpreter with the source program's successful traces implements the full
semantic fork measure. Rejected runs retain their mass at `none`; no conditional law is used. -/
theorem denote_forkFromTracedAnswers (sample : P.FreeM Answer)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (run : List Answer → Option (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))
    (hrun : ∀ tape, run tape = (runFromAnswers (trace program) tape).bind
      (fun out => out.1.map (fun value => (value, out.2))))
    (choose : α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) → Option ℕ)
    (count : ℕ) (hcount : queryBound program ≤ count) :
    denote μ (do
      let answers ← (List.replicate count ()).mapM (fun _ => sample)
      let fresh ← (List.replicate count ()).mapM (fun _ => sample)
      pure (forkFromTracedAnswers run choose answers fresh)) =
        (denote (P := PFunctor.mk Operation (fun _ => Answer)) (fun _ => denote μ sample)
          (fork (fun _ => true)
            (fun out => out.1.bind (fun value => choose (value, out.2))) (trace program))).map
              (fun out => do
                let first ← out.1.1
                let ⟨op, answer, answer', second, events⟩ ← out.2
                let second ← second
                pure ((first, out.1.2), ⟨op, answer, answer', second, events⟩)) := by
  let finish := fun out : (Option α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) ×
      Option ((_ : Operation) × Answer × Answer ×
        (Option α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B))) => do
    let first ← out.1.1
    let ⟨op, answer, answer', second, events⟩ ← out.2
    let second ← second
    pure ((first, out.1.2), (⟨op, answer, answer', second, events⟩ :
      (_ : Operation) × Answer × Answer ×
        (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B))))
  have heq := funext hrun
  rw [heq]
  simp only [forkFromTracedAnswers_eq]
  have hmap : (do
      let answers ← (List.replicate count ()).mapM (fun _ => sample)
      let fresh ← (List.replicate count ()).mapM (fun _ => sample)
      pure ((forkFromAnswers (fun _ => true)
        (fun out : Option α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) =>
          out.1.bind (fun value => choose (value, out.2)))
        (trace program) answers fresh).bind finish)) =
      (fun out => Option.bind out finish) <$> (do
        let answers ← (List.replicate count ()).mapM (fun _ => sample)
        let fresh ← (List.replicate count ()).mapM (fun _ => sample)
        pure (forkFromAnswers (fun _ => true)
          (fun out : Option α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) =>
            out.1.bind (fun value => choose (value, out.2)))
          (trace program) answers fresh)) := by
    simp only [map_eq_pure_bind, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  rw [hmap, ← map_eq_map, denote_map μ _ _ Measurable.of_discrete,
    denote_forkFromAnswers μ sample _ _ _ count (by
      rwa [← queryBoundP_true (trace program), queryBoundP_trace, queryBoundP_true]),
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

open scoped ENNReal

/-- The general forking inequality holds for a checked interpreter that discards failed-run
logs. Success requires two selected results at the same position and distinct answers. -/
theorem le_denote_forkFromTracedAnswers (sample : P.FreeM Answer)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (run : List Answer → Option (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))
    (hrun : ∀ tape, run tape = (runFromAnswers (trace program) tape).bind
      (fun out => out.1.map (fun value => (value, out.2))))
    (choose : α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) → Option ℕ)
    (count q : ℕ) (r : ℝ≥0∞) (hcount : queryBound program ≤ count)
    (hanswer : ∀ answer, denote μ sample {answer} ≤ r)
    (hvalid : ∀ out, MonadAttach.CanReturn (trace program) (some out.1, out.2) →
      ∀ n, choose out = some n → n < out.2.length) :
    let tape := (List.replicate count ()).mapM (fun _ => sample)
    let ε := denote μ (run <$> tape)
      {out | ∃ value, out = some value ∧ ∃ n < q, choose value = some n}
    ε * (ε / q - r) ≤ denote μ (do
      let answers ← tape
      let fresh ← tape
      pure (forkFromTracedAnswers run choose answers fresh))
        {out | ∃ value, out = some value ∧ (value.1, some value.2) ∈ ⋃ n,
          forkSuccess (P := PFunctor.mk Operation (fun _ => Answer)) choose n} := by
  let select := fun out : Option α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) =>
    out.1.bind (fun value => choose (value, out.2))
  let law := fun _ : Operation => denote μ sample
  have hfirst : denote μ (run <$> (List.replicate count ()).mapM (fun _ => sample))
      {out | ∃ value, out = some value ∧ ∃ n < q, choose value = some n} =
      denote law (trace program) {out | ∃ n < q, select out = some n} := by
    rw [funext hrun]
    let collapse := fun out : Option (Option α ×
        List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) =>
      out.bind (fun out => out.1.map (fun value => (value, out.2)))
    rw [← Functor.map_map (runFromAnswers (trace program)) collapse]
    have htape := denote_runFromAnswers μ sample (trace program) count (by
      rwa [← queryBoundP_true (trace program), queryBoundP_trace, queryBoundP_true])
    simp only [← map_eq_map] at htape
    simp only [← map_eq_map]
    rw [denote_map μ _ _ Measurable.of_discrete, htape,
      Measure.map_map Measurable.of_discrete Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    congr 1
    ext out
    rcases out with ⟨value, events⟩
    cases value <;> simp [select, collapse]
  dsimp only
  rw [hfirst, denote_forkFromTracedAnswers μ sample program run hrun choose count hcount,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  refine (le_denote_fork_trace law (fun _ => true) select program q r
    (fun _ _ => hanswer) ?_).trans (measure_mono ?_)
  · rintro ⟨value, events⟩ hreturn n hchoose
    obtain ⟨value, hvalue, hchoose⟩ := Option.bind_eq_some_iff.mp hchoose
    subst hvalue
    simpa using hvalid (value, events) hreturn n hchoose
  · rintro ⟨⟨first, events⟩, second⟩ hsuccess
    obtain ⟨n, ⟨op, old, fresh, second', events'⟩, hsecond, hfirst, hsecond', hne⟩ :=
      Set.mem_iUnion.mp hsuccess
    cases hsecond
    obtain ⟨first, hfirst, hchoose⟩ := Option.bind_eq_some_iff.mp hfirst
    obtain ⟨second, hsecond, hchoose'⟩ := Option.bind_eq_some_iff.mp hsecond'
    subst hfirst hsecond
    refine ⟨((first, events), ⟨op, old, fresh, second, events'⟩), rfl, ?_⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨_, rfl, hchoose, hchoose', hne⟩⟩

/-- Sampling a private seed once and sharing it across the two executions preserves the
quadratic bound in the overall success probability of the checked first run. -/
theorem le_denote_forkFromTracedAnswers_bind {Seed : Type u} [MeasurableSpace Seed]
    [DiscreteMeasurableSpace Seed]
    (seed : P.FreeM Seed) (sample : P.FreeM Answer)
    (program : Seed → (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (run : Seed → List Answer →
      Option (α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)))
    (hrun : ∀ saved, MonadAttach.CanReturn seed saved → ∀ tape,
      run saved tape = (runFromAnswers (trace (program saved)) tape).bind
        (fun out => out.1.map (fun value => (value, out.2))))
    (choose : α × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B) → Option ℕ)
    (count q : ℕ) (r : ℝ≥0∞)
    (hcount : ∀ saved, MonadAttach.CanReturn seed saved → queryBound (program saved) ≤ count)
    (hanswer : ∀ answer, denote μ sample {answer} ≤ r)
    (hvalid : ∀ saved, MonadAttach.CanReturn seed saved →
      ∀ out, MonadAttach.CanReturn (trace (program saved)) (some out.1, out.2) →
        ∀ n, choose out = some n → n < out.2.length) :
    let tape := (List.replicate count ()).mapM (fun _ => sample)
    let ε := denote μ (seed >>= fun saved => run saved <$> tape)
      {out | ∃ value, out = some value ∧ ∃ n < q, choose value = some n}
    ε * (ε / q - r) ≤ denote μ (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (forkFromTracedAnswers (run saved) choose answers fresh))
        {out | ∃ value, out = some value ∧ (value.1, some value.2) ∈ ⋃ n,
          forkSuccess (P := PFunctor.mk Operation (fun _ => Answer)) choose n} := by
  dsimp only
  rw [denote_bind_of_discrete, denote_bind_of_discrete]
  simp only [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  refine (ENNReal.mul_sub_lintegral_le Measurable.of_discrete.aemeasurable
    (fun _ => prob_le_one) q r).trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_canReturn μ seed] with saved hsaved
  exact le_denote_forkFromTracedAnswers μ sample (program saved) (run saved)
    (hrun saved hsaved) choose count q r (hcount saved hsaved) hanswer (hvalid saved hsaved)

end Aborting

end PFunctor.FreeM
