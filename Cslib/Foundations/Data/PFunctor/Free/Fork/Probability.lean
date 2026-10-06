/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fork
public import Cslib.Foundations.Data.PFunctor.Free.Measure.Support
public import Cslib.Foundations.MeasureTheory.Option
public import Cslib.Foundations.MeasureTheory.Sigma
public import Cslib.Foundations.MeasureTheory.Collision

/-!
# Measure semantics and the general forking inequality

Forking preserves the first execution's marginal. The two-run success bound accounts for an
adaptively selected position and the probability of receiving the same answer twice.
-/

public section

namespace PFunctor.FreeM

section FirstRun

open MeasureTheory

universe u

variable {P : PFunctor.{u, u}} {α : Type u}
  [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- Forking preserves the law of the first execution. Losslessness matters: the optional
second execution must not discard mass from the already completed first one. -/
theorem toMeasure_fork_map_fst (select : P.A → Bool) (choose : α → Option ℕ) (x : P.FreeM α) :
    (toMeasure (fork select choose x) μ).map Prod.fst = toMeasure x μ := by
  induction x generalizing choose with
  | pure a =>
    rw [fork_pure, toMeasure_pure, toMeasure_pure, Measure.map_dirac' measurable_fst]
  | lift_bind op cont ih =>
    rw [← toMeasure_map _ _ measurable_fst]
    change toMeasure ((fun out : α × Option ((op : P.A) × P.B op × P.B op × α) => out.1) <$>
      (do
      let answer ← lift op
      let first ← fork select (if select op then
        fun a => (choose a).bind Nat.ppred
        else choose) (cont answer)
      if select op && (choose first.1 == some 0) then
        let answer' ← lift op
        let second ← cont answer'
        pure (first.1, some ⟨op, answer, answer', second⟩)
      else pure first)) μ = toMeasure (lift op >>= cont) μ
    simp only [_root_.map_bind, toMeasure_bind_of_discrete', toMeasure_lift]
    congr 1
    funext answer
    have hfinish (first : α × Option ((op : P.A) × P.B op × P.B op × α)) :
        toMeasure ((fun out : α × Option ((op : P.A) × P.B op × P.B op × α) => out.1) <$>
        (if select op && (choose first.1 == some 0) then do
          let answer' ← lift op
          let second ← cont answer'
          pure (first.1, some ⟨op, answer, answer', second⟩)
        else pure first)) μ = Measure.dirac first.1 := by
      split
      · simp only [_root_.map_bind, LawfulApplicative.map_pure, toMeasure_bind_of_discrete',
          toMeasure_pure, toMeasure_lift]
        simp_rw [Measure.bind_const, measure_univ, one_smul]
        rw [Measure.bind_const, measure_univ, one_smul]
      · exact rfl
    simp_rw [hfinish]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
    exact ih answer _

end FirstRun

section Forking

open MeasureTheory
open scoped ENNReal

universe u

variable {P : PFunctor.{u, u}} {α : Type u}
  [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op))

/-- An unselected operation extends the shared prefix without consuming a fork position. -/
theorem toMeasure_forkSuccess_lift_bind_of_not_select (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = false) (n : ℕ) :
    toMeasure (fork select choose (lift op >>= cont)) μ (forkSuccess choose n) =
      ∫⁻ answer, toMeasure (fork select choose (cont answer)) μ (forkSuccess choose n) ∂μ op := by
  change toMeasure (fork select choose (.liftBind op cont)) μ _ = _
  rw [fork]
  simp only [hselect, Bool.false_eq_true, ↓reduceIte, Bool.false_and, _root_.bind_pure,
    toMeasure_bind_of_discrete', toMeasure_lift]
  exact Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable

/-- At a selected operation, later fork positions are counted relative to its continuation. -/
theorem toMeasure_forkSuccess_lift_bind_succ (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = true) (n : ℕ) :
    toMeasure (fork select choose (lift op >>= cont)) μ (forkSuccess choose (n + 1)) =
      ∫⁻ answer, toMeasure (fork select
        (fun a => (choose a).bind Nat.ppred) (cont answer)) μ
        (forkSuccess (fun a => (choose a).bind Nat.ppred) n)
        ∂μ op := by
  classical
  change toMeasure (fork select choose (.liftBind op cont)) μ _ = _
  rw [fork]
  simp only [hselect, ↓reduceIte, Bool.true_and, beq_iff_eq,
    toMeasure_bind_of_discrete', toMeasure_lift,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro answer
  rw [← lintegral_indicator_one MeasurableSet.of_discrete]
  apply lintegral_congr
  intro out
  by_cases hzero : choose out.1 = some 0
  · simp only [hzero, ↓reduceIte, toMeasure_bind_of_discrete', toMeasure_lift, toMeasure_pure,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, hzero, Set.indicator, forkSuccess]
  · rw [ite_eq_right hzero, toMeasure_pure, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    congr 1
    ext x
    apply exists_congr
    intro event
    apply and_congr_right
    intro _
    exact and_congr Option.bind_ppred_eq_some.symm
      (and_congr_left' Option.bind_ppred_eq_some.symm)

variable [∀ op, IsProbabilityMeasure (μ op)]

/-- Forking at the current operation samples two independent answer/continuation pairs.
Earlier operations, already represented by this continuation, are shared. -/
theorem toMeasure_forkSuccess_lift_bind_zero (select : P.A → Bool)
    (choose : α → Option ℕ) (op : P.A) (cont : P.B op → P.FreeM α)
    (hselect : select op = true) :
    let ν := (μ op).bind fun answer => (toMeasure (cont answer) μ).map (Prod.mk answer)
    toMeasure (fork select choose (lift op >>= cont)) μ (forkSuccess choose 0) =
      (ν.prod ν) {p | choose p.1.2 = some 0 ∧ choose p.2.2 = some 0 ∧ p.1.1 ≠ p.2.1} := by
  classical
  dsimp only
  let good : P.B op × α → P.B op × α → ℝ≥0∞ := fun first second =>
    if choose first.2 = some 0 ∧ choose second.2 = some 0 ∧ first.1 ≠ second.1 then 1 else 0
  have hleft : toMeasure (fork select choose (lift op >>= cont)) μ (forkSuccess choose 0) =
      ∫⁻ answer, ∫⁻ a, ∫⁻ answer', ∫⁻ a', good (answer, a) (answer', a')
        ∂toMeasure (cont answer') μ ∂μ op ∂toMeasure (cont answer) μ ∂μ op := by
    change toMeasure (fork select choose (.liftBind op cont)) μ _ = _
    rw [fork]
    simp only [hselect, ↓reduceIte, Bool.true_and, beq_iff_eq,
      toMeasure_bind_of_discrete', toMeasure_lift,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro answer
    have hfinish (out : α × Option ((op : P.A) × P.B op × P.B op × α)) :
        toMeasure (if choose out.1 = some 0 then do
          let answer' ← lift op
          let second ← cont answer'
          pure (out.1, some ⟨op, answer, answer', second⟩)
        else pure out) μ (forkSuccess choose 0) =
          ∫⁻ answer', ∫⁻ a', good (answer, out.1) (answer', a')
            ∂toMeasure (cont answer') μ ∂μ op := by
      by_cases hzero : choose out.1 = some 0
      · simp only [hzero, ↓reduceIte, toMeasure_bind_of_discrete', toMeasure_lift, toMeasure_pure,
          Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        apply lintegral_congr
        intro answer'
        apply lintegral_congr
        intro a'
        simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator, good, hzero]
      · simp [hzero, toMeasure_pure, Measure.dirac_apply' _ MeasurableSet.of_discrete,
          forkSuccess, Set.indicator, good]
    simp_rw [hfinish]
    rw [← toMeasure_fork_map_fst μ select
      (fun a => (choose a).bind Nat.ppred) (cont answer)]
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
theorem sq_sub_mul_le_toMeasure_forkSuccess (select : P.A → Bool) (choose : α → Option ℕ)
    (x : P.FreeM α) (n : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ a events, MonadAttach.CanReturn (trace x) (a, events) →
      choose a = some n → n < events.countP (fun event => select event.1)) :
    (toMeasure x μ {a | choose a = some n}) ^ 2 - toMeasure x μ {a | choose a = some n} * r ≤
      toMeasure (fork select choose x) μ (forkSuccess choose n) := by
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
      rw [toMeasure_forkSuccess_lift_bind_of_not_select μ select choose op cont hselect,
        toMeasure_bind_of_discrete', toMeasure_lift,
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
        rw [toMeasure_forkSuccess_lift_bind_zero μ select choose op cont hselect]
        let ν := (μ op).bind fun answer => (toMeasure (cont answer) μ).map (Prod.mk answer)
        have hmass : ν {pair | choose pair.2 = some 0} =
            toMeasure (lift op >>= cont) μ {a | choose a = some 0} := by
          simp only [ν, toMeasure_bind_of_discrete', toMeasure_lift,
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
        let next : α → Option ℕ := fun a => (choose a).bind Nat.ppred
        have hnext (a : α) : next a = some n ↔ choose a = some (n + 1) :=
          Option.bind_ppred_eq_some
        rw [toMeasure_forkSuccess_lift_bind_succ μ select choose op cont hselect,
          toMeasure_bind_of_discrete', toMeasure_lift,
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
theorem le_toMeasure_fork (select : P.A → Bool) (choose : α → Option ℕ) (x : P.FreeM α)
    (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ a events, MonadAttach.CanReturn (trace x) (a, events) →
      ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let ε := toMeasure x μ {a | ∃ n < q, choose a = some n}
    ε * (ε / q - r) ≤ toMeasure (fork select choose x) μ (⋃ n, forkSuccess choose n) := by
  classical
  dsimp only
  let p := fun n => toMeasure x μ {a | choose a = some n}
  have hdisjoint : Pairwise (fun i j => Disjoint {a | choose a = some i}
      {a | choose a = some j}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (Option.some.inj (hi.symm.trans hj))
  have hsum : (∑ n ∈ Finset.range q, p n) = toMeasure x μ {a | ∃ n < q, choose a = some n} := by
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
    _ ≤ ∑ n ∈ Finset.range q, toMeasure (fork select choose x) μ (forkSuccess choose n) := by
      apply Finset.sum_le_sum
      intro n _
      exact sq_sub_mul_le_toMeasure_forkSuccess μ select choose x n r hanswer
        (fun a events htrace => hvalid a events htrace n)
    _ = toMeasure (fork select choose x) μ (⋃ n ∈ Finset.range q, forkSuccess choose n) :=
      (measure_biUnion_finset (hfork.set_pairwise _) (fun _ _ => MeasurableSet.of_discrete)).symm
    _ ≤ _ := measure_mono (by
      intro out hout
      obtain ⟨n, _, hn⟩ := Set.mem_iUnion₂.mp hout
      exact Set.mem_iUnion.mpr ⟨n, hn⟩)

/-- The forking inequality when the selector inspects a recorded execution. -/
theorem le_toMeasure_fork_trace [MeasurableSpace (List (Sigma P.B))]
    [DiscreteMeasurableSpace (List (Sigma P.B))] (select : P.A → Bool)
    (choose : α × List (Sigma P.B) → Option ℕ) (x : P.FreeM α) (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ out, MonadAttach.CanReturn (trace x) out →
      ∀ n, choose out = some n → n < out.2.countP (fun event => select event.1)) :
    let ε := toMeasure (trace x) μ {out | ∃ n < q, choose out = some n}
    ε * (ε / q - r) ≤ toMeasure (fork select choose (trace x)) μ (⋃ n, forkSuccess choose n) := by
  apply le_toMeasure_fork μ select choose (trace x) q r hanswer
  intro out events htrace n hchoose
  rw [trace_trace] at htrace
  obtain ⟨original, horiginal, heq⟩ := (canReturn_map _ _ _).mp htrace
  rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
  exact hvalid original horiginal n hchoose

/-- Sample the entire private state once, then share it between both executions. Averaging
the conditional forking bound preserves the same quadratic loss. Only reachable private states
need a valid selector. In particular, the state may contain a fixed finite random tape. -/
theorem le_toMeasure_fork_bind {Seed : Type u} [MeasurableSpace Seed]
    [MeasurableSingletonClass Seed] [Countable Seed]
    (seed : P.FreeM Seed) (program : Seed → P.FreeM α)
    (select : P.A → Bool) (choose : α → Option ℕ) (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ op, select op = true → ∀ answer, μ op {answer} ≤ r)
    (hvalid : ∀ saved, MonadAttach.CanReturn seed saved →
      ∀ a events, MonadAttach.CanReturn (trace (program saved)) (a, events) →
        ∀ n, choose a = some n → n < events.countP (fun event => select event.1)) :
    let ε := toMeasure (seed >>= program) μ {a | ∃ n < q, choose a = some n}
    ε * (ε / q - r) ≤
      toMeasure (seed >>= fun saved => fork select choose (program saved)) μ
        (⋃ n, forkSuccess choose n) := by
  dsimp only
  simp only [toMeasure_bind_of_discrete',
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  refine (ENNReal.mul_sub_lintegral_le Measurable.of_discrete.aemeasurable
    (fun _ => prob_le_one) q r).trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_canReturn μ seed] with saved hsaved
  exact le_toMeasure_fork μ select choose (program saved) q r hanswer (hvalid saved hsaved)

end Forking

end PFunctor.FreeM
