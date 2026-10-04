/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork.Measure
public import Cslib.Foundations.Data.PFunctor.Free.Measure.Support
public import Cslib.Foundations.MeasureTheory.Collision

/-! # Probability bounds for adaptive forking -/

public section

namespace PFunctor.FreeM

open MeasureTheory
open scoped ENNReal

universe u

variable {P : PFunctor.{u, u}} {α : Type u}
  [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op))

private theorem pred_eq_some (choice : Option ℕ) (n : ℕ) :
    (match choice with | some (k + 1) => some k | _ => none) = some n ↔
      choice = some (n + 1) := by
  cases choice with
  | none => simp
  | some k => cases k <;> simp

/-- An unselected operation extends the shared prefix without consuming a fork position. -/
theorem denote_forkSuccess_lift_bind_of_not_select (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = false) (n : ℕ) :
    denote μ (fork select choose (lift op >>= cont)) (forkSuccess choose n) =
      ∫⁻ answer, denote μ (fork select choose (cont answer)) (forkSuccess choose n) ∂μ op := by
  change denote μ (fork select choose (.liftBind op cont)) _ = _
  rw [fork]
  simp only [hselect, Bool.false_eq_true, ↓reduceIte, Bool.false_and, _root_.bind_pure,
    denote_bind_of_discrete, denote_lift]
  exact Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable

/-- At a selected operation, later fork positions are counted relative to its continuation. -/
theorem denote_forkSuccess_lift_bind_succ (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = true) (n : ℕ) :
    denote μ (fork select choose (lift op >>= cont)) (forkSuccess choose (n + 1)) =
      ∫⁻ answer, denote μ (fork select
        (fun a => match choose a with | some (k + 1) => some k | _ => none) (cont answer))
        (forkSuccess (fun a => match choose a with | some (k + 1) => some k | _ => none) n)
        ∂μ op := by
  classical
  change denote μ (fork select choose (.liftBind op cont)) _ = _
  rw [fork]
  simp only [hselect, ↓reduceIte, Bool.true_and, beq_iff_eq,
    denote_bind_of_discrete, denote_lift,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro answer
  rw [← lintegral_indicator_one MeasurableSet.of_discrete]
  apply lintegral_congr
  intro out
  by_cases hzero : choose out.1 = some 0
  · simp only [hzero, ↓reduceIte, denote_bind_of_discrete, denote_lift, denote_pure,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, hzero, Set.indicator, forkSuccess]
  · rw [ite_eq_right hzero, denote_pure, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    congr 1
    ext x
    apply exists_congr
    intro event
    apply and_congr_right
    intro _
    exact and_congr (pred_eq_some (choose x.1) n).symm
      (and_congr_left' (pred_eq_some (choose event.2.2.2) n).symm)

variable [∀ op, IsProbabilityMeasure (μ op)]

/-- Forking at the current operation samples two independent answer/continuation pairs.
Earlier operations, already represented by this continuation, are shared. -/
theorem denote_forkSuccess_lift_bind_zero (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = true) :
    let ν := (μ op).bind fun answer => (denote μ (cont answer)).map (Prod.mk answer)
    denote μ (fork select choose (lift op >>= cont)) (forkSuccess choose 0) =
      (ν.prod ν) {p | choose p.1.2 = some 0 ∧ choose p.2.2 = some 0 ∧ p.1.1 ≠ p.2.1} := by
  classical
  dsimp only
  let good : P.B op × α → P.B op × α → ℝ≥0∞ := fun first second =>
    if choose first.2 = some 0 ∧ choose second.2 = some 0 ∧ first.1 ≠ second.1 then 1 else 0
  have hleft : denote μ (fork select choose (lift op >>= cont)) (forkSuccess choose 0) =
      ∫⁻ answer, ∫⁻ a, ∫⁻ answer', ∫⁻ a', good (answer, a) (answer', a')
        ∂denote μ (cont answer') ∂μ op ∂denote μ (cont answer) ∂μ op := by
    change denote μ (fork select choose (.liftBind op cont)) _ = _
    rw [fork]
    simp only [hselect, ↓reduceIte, Bool.true_and, beq_iff_eq,
      denote_bind_of_discrete, denote_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro answer
    have hfinish (out : α × Option ((op : P.A) × P.B op × P.B op × α)) :
        denote μ (if choose out.1 = some 0 then do
          let answer' ← lift op
          let second ← cont answer'
          pure (out.1, some ⟨op, answer, answer', second⟩)
        else pure out) (forkSuccess choose 0) =
          ∫⁻ answer', ∫⁻ a', good (answer, out.1) (answer', a')
            ∂denote μ (cont answer') ∂μ op := by
      by_cases hzero : choose out.1 = some 0
      · simp only [hzero, ↓reduceIte, denote_bind_of_discrete, denote_lift, denote_pure,
          Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        apply lintegral_congr
        intro answer'
        apply lintegral_congr
        intro a'
        simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator, good, hzero]
      · simp [hzero, denote_pure, Measure.dirac_apply' _ MeasurableSet.of_discrete,
          forkSuccess, Set.indicator, good]
    simp_rw [hfinish]
    rw [← denote_fork_map_fst μ select
      (fun a => match choose a with | some (k + 1) => some k | _ => none) (cont answer)]
    symm
    exact lintegral_map Measurable.of_discrete Measurable.of_discrete
  rw [hleft]
  rw [Measure.prod_apply MeasurableSet.of_discrete,
    Measure.lintegral_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro answer
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  apply lintegral_congr
  intro a
  rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro answer'
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  apply lintegral_congr
  intro a'
  simp [good, Set.indicator]

/-- The quadratic forking bound for one selector fiber. Every selected result must point to
an operation on its own execution, and each answer at a selected operation has mass at most `r`.
The shared prefix can be adaptive and contain arbitrarily many unselected operations. -/
theorem sq_sub_mul_le_denote_forkSuccess (select : P.A → Bool) (choose : α → Option ℕ)
    (x : P.FreeM α) (n : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ a events, MonadAttach.CanReturn (trace x) (a, events) →
      choose a = some n → n < events.countP (fun event => select event.1)) :
    (denote μ x {a | choose a = some n}) ^ 2 - denote μ x {a | choose a = some n} * r ≤
      denote μ (fork select choose x) (forkSuccess choose n) := by
  classical
  induction x generalizing choose n with
  | pure value =>
    have hchoose : choose value ≠ some n := by
      intro h
      exact Nat.not_lt_zero n (hvalid value [] rfl h)
    simp [hchoose, Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator]
  | lift_bind op cont ih =>
    simp only [bind_eq_bind] at hvalid ⊢
    cases hselect : select op with
    | false =>
      rw [denote_forkSuccess_lift_bind_of_not_select μ select choose op cont hselect,
        denote_bind_of_discrete, denote_lift,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      apply (ENNReal.sq_lintegral_sub_mul_le Measurable.of_discrete.aemeasurable r).trans
      apply lintegral_mono
      intro answer
      apply ih answer choose n
      intro a events htrace hchoose
      have h := hvalid a (⟨op, answer⟩ :: events)
        ((canReturn_trace_lift_bind _ _ _ _).mpr ⟨answer, events, htrace, rfl⟩) hchoose
      simpa [hselect] using h
    | true =>
      cases n with
      | zero =>
        rw [denote_forkSuccess_lift_bind_zero μ select choose op cont hselect]
        let ν := (μ op).bind fun answer => (denote μ (cont answer)).map (Prod.mk answer)
        have hmass : ν {pair | choose pair.2 = some 0} =
            denote μ (lift op >>= cont) {a | choose a = some 0} := by
          simp only [ν, denote_bind_of_discrete, denote_lift,
            Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
            Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
          rfl
        rw [← hmass]
        apply Measure.sq_sub_mul_le_prod ν Prod.fst _ r
        intro answer
        calc
          _ = μ op {answer} := by
            rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
              ← lintegral_indicator_one (measurableSet_singleton answer)]
            apply lintegral_congr
            intro b
            rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
            by_cases hb : b = answer <;> simp [hb, Set.indicator]
          _ ≤ r := hanswer op hselect answer
      | succ n =>
        let next : α → Option ℕ := fun a => match choose a with
          | some (k + 1) => some k
          | _ => none
        have hnext (a : α) : next a = some n ↔ choose a = some (n + 1) :=
          pred_eq_some (choose a) n
        rw [denote_forkSuccess_lift_bind_succ μ select choose op cont hselect,
          denote_bind_of_discrete, denote_lift,
          Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        have hset : {a | choose a = some (n + 1)} = {a | next a = some n} :=
          Set.ext fun a => (hnext a).symm
        rw [hset]
        apply (ENNReal.sq_lintegral_sub_mul_le Measurable.of_discrete.aemeasurable r).trans
        apply lintegral_mono
        intro answer
        apply ih answer next n
        intro a events htrace hchoose
        have h := hvalid a (⟨op, answer⟩ :: events)
          ((canReturn_trace_lift_bind _ _ _ _).mpr ⟨answer, events, htrace, rfl⟩)
          ((hnext a).mp hchoose)
        simpa [hselect] using h

/-- Adaptive forking with at most `q` eligible positions has success probability at least
`ε * (ε / q - r)`. Here `ε` counts results selecting one of those positions, and `r` bounds
the mass of each challenge. The selector may inspect the entire first result.

This is the general forking inequality of Bellare and Neven, *Multi-signatures in the plain
public-key model and a general forking lemma* (2006), Lemma 1. -/
theorem le_denote_fork (select : P.A → Bool) (choose : α → Option ℕ) (x : P.FreeM α)
    (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ a events, MonadAttach.CanReturn (trace x) (a, events) →
      ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let ε := denote μ x {a | ∃ n < q, choose a = some n}
    ε * (ε / q - r) ≤ denote μ (fork select choose x) (⋃ n, forkSuccess choose n) := by
  classical
  dsimp only
  let p := fun n => denote μ x {a | choose a = some n}
  have hdisjoint : Pairwise (fun i j => Disjoint {a | choose a = some i}
      {a | choose a = some j}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (Option.some.inj (hi.symm.trans hj))
  have hsum : (∑ n ∈ Finset.range q, p n) = denote μ x {a | ∃ n < q, choose a = some n} := by
    rw [← measure_biUnion_finset (hdisjoint.set_pairwise _) (fun _ _ => MeasurableSet.of_discrete)]
    congr 1
    ext a
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, exists_prop]
  have hfinite : (∑ n ∈ Finset.range q, p n) ≠ ⊤ := by
    rw [hsum]
    exact measure_ne_top _ _
  have hfork : Pairwise (fun i j => Disjoint (forkSuccess (P := P) choose i)
      (forkSuccess choose j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro out ⟨_, _, hi, _⟩ ⟨_, _, hj, _⟩
    exact hij (Option.some.inj (hi.symm.trans hj))
  calc
    _ = (∑ n ∈ Finset.range q, p n) *
        ((∑ n ∈ Finset.range q, p n) / (Finset.range q).card - r) := by
      rw [Finset.card_range, hsum]
    _ ≤ ∑ n ∈ Finset.range q, (p n ^ 2 - p n * r) :=
      ENNReal.mul_sub_le_sum_sq_sub_mul _ p r hfinite
    _ ≤ ∑ n ∈ Finset.range q, denote μ (fork select choose x) (forkSuccess choose n) := by
      apply Finset.sum_le_sum
      intro n _
      exact sq_sub_mul_le_denote_forkSuccess μ select choose x n r hanswer
        (fun a events htrace => hvalid a events htrace n)
    _ = denote μ (fork select choose x) (⋃ n ∈ Finset.range q, forkSuccess choose n) :=
      (measure_biUnion_finset (hfork.set_pairwise _) (fun _ _ => MeasurableSet.of_discrete)).symm
    _ ≤ _ := measure_mono (by
      intro out hout
      obtain ⟨n, _, hn⟩ := Set.mem_iUnion₂.mp hout
      exact Set.mem_iUnion.mpr ⟨n, hn⟩)

/-- The forking inequality when the selector inspects a recorded execution. -/
theorem le_denote_fork_trace [MeasurableSpace (List (Sigma P.B))]
    [DiscreteMeasurableSpace (List (Sigma P.B))] (select : P.A → Bool)
    (choose : α × List (Sigma P.B) → Option ℕ) (x : P.FreeM α) (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ out, MonadAttach.CanReturn (trace x) out →
      ∀ n, choose out = some n → n < out.2.countP (fun event => select event.1)) :
    let ε := denote μ (trace x) {out | ∃ n < q, choose out = some n}
    ε * (ε / q - r) ≤ denote μ (fork select choose (trace x)) (⋃ n, forkSuccess choose n) := by
  apply le_denote_fork μ select choose (trace x) q r hanswer
  intro out events htrace n hchoose
  rw [trace_trace] at htrace
  obtain ⟨original, horiginal, heq⟩ := (canReturn_map _ _ _).mp htrace
  rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
  exact hvalid original horiginal n hchoose

/-- Sample the entire private state once, then share it between both executions. Averaging
the conditional forking bound preserves the same quadratic loss. Only reachable private states
need a valid selector. In particular, the state may contain a fixed finite random tape. -/
theorem le_denote_fork_bind {Seed : Type u} [MeasurableSpace Seed]
    [MeasurableSingletonClass Seed] [Countable Seed]
    (seed : P.FreeM Seed) (program : Seed → P.FreeM α)
    (select : P.A → Bool) (choose : α → Option ℕ) (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ saved, MonadAttach.CanReturn seed saved →
      ∀ a events, MonadAttach.CanReturn (trace (program saved)) (a, events) →
        ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let ε := denote μ (seed >>= program) {a | ∃ n < q, choose a = some n}
    ε * (ε / q - r) ≤
      denote μ (seed >>= fun saved => fork select choose (program saved))
        (⋃ n, forkSuccess choose n) := by
  dsimp only
  simp only [denote_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  refine (ENNReal.mul_sub_lintegral_le Measurable.of_discrete.aemeasurable
    (fun _ => prob_le_one) q r).trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_canReturn μ seed] with saved hsaved
  exact le_denote_fork μ select choose (program saved) q r hanswer (hvalid saved hsaved)

end PFunctor.FreeM
