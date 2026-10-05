/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability

/-!
# Answer-tape replay with an aborting interpreter

A checked interpreter need only retain the traces of successful executions. Failed first runs
are never forked, and failed second runs reject the fork. The full result measure agrees with
semantic forking followed by these checks, including the probability of rejection.
-/

@[expose] public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
