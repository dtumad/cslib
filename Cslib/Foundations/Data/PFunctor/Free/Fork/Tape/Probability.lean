/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape

/-! # The general forking bound for finite answer tapes -/

public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
