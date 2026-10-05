/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost.Filtered
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Abort
public import Init.Control.Option

/-!
# Accumulating implementation errors

Each selected operation may lose a bounded amount of probability when implemented by a
fallible program. The bound composes through adaptive calls and arbitrary bounded observations.
Inlining stateful handlers before applying this theorem also accounts for their internal draws.
-/

public section

namespace PFunctor.FreeM

open MeasureTheory
open scoped ENNReal

universe uP uQ v

variable {P : PFunctor.{uP, v}} {Q : PFunctor.{uQ, v}} {α : Type v}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  (ν : (op : Q.A) → Measure (Q.B op)) [∀ op, IsProbabilityMeasure (ν op)]

omit [∀ op, IsProbabilityMeasure (μ op)] [∀ op, IsProbabilityMeasure (ν op)] in
/-- Implementations that only remove successful mass cannot increase any nonnegative payoff.
This also holds for adaptive programs and for measures that lose mass. -/
theorem lintegral_liftM_option_le
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (denote ν (handler op).run).comap some ≤ μ op)
    (x : P.FreeM α) (post : α → ℝ≥0∞) :
    ∫⁻ out, out.elim 0 post ∂denote ν (x.liftM handler).run ≤
      ∫⁻ value, post value ∂denote μ x := by
  induction x with
  | pure value =>
    change (∫⁻ out, out.elim 0 post ∂Measure.dirac (some value)) ≤
      ∫⁻ value, post value ∂Measure.dirac value
    simp only [lintegral_dirac' _ Measurable.of_discrete, Option.elim_some, le_refl]
  | lift_bind op cont ih =>
    rw [denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    simp only [bind_eq_bind, liftM_lift_bind]
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk]
    rw [denote_bind ν _ _ Measurable.of_discrete,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    let f := fun value : P.B op => ∫⁻ out, post out ∂denote μ (cont value)
    calc
      _ ≤ ∫⁻ out, out.elim 0 f ∂denote ν (handler op).run := by
        apply lintegral_mono
        intro out
        cases out with
        | none => simp
        | some value => exact ih value
      _ = ∫⁻ value, f value ∂(denote ν (handler op).run).comap some :=
        (lintegral_comap_some _ f).symm
      _ ≤ _ := lintegral_mono' (hstep op) le_rfl

/-- Errors add over selected calls, including when future calls depend on earlier answers.
Explicit failure has zero payoff; the rest of the experiment is left unchanged. -/
theorem lintegral_denote_le_liftM_option_add
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (risk : P.A → Bool) (δ : ℝ≥0∞)
    (hstep : ∀ op, ∀ f : P.B op → ℝ≥0∞, (∀ value, f value ≤ 1) →
      ∫⁻ value, f value ∂μ op ≤
        (∫⁻ out, out.elim 0 f ∂denote ν (handler op).run) + if risk op then δ else 0)
    (x : P.FreeM α) (n : ℕ) (hcount : queryBoundP risk x ≤ n)
    (post : α → ℝ≥0∞) (hpost : ∀ value, post value ≤ 1) :
    ∫⁻ value, post value ∂denote μ x ≤
      (∫⁻ out, out.elim 0 post ∂denote ν (x.liftM handler).run) + n * δ := by
  induction x generalizing n with
  | pure value =>
    change (∫⁻ value, post value ∂Measure.dirac value) ≤
      (∫⁻ out, out.elim 0 post ∂Measure.dirac (some value)) + n * δ
    simp only [lintegral_dirac' _ Measurable.of_discrete, Option.elim_some]
    exact le_self_add
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le risk op cont n hcount
    let remaining := n - (risk op).toNat
    let f := fun value : P.B op =>
      ∫⁻ out, out.elim 0 post ∂denote ν ((cont value).liftM handler).run
    have hf (value) : f value ≤ 1 := by
      apply lintegral_le_const
      exact Filter.Eventually.of_forall fun out => by
        cases out with
        | none => exact zero_le
        | some out => exact hpost out
    have hlocal := hstep op f hf
    rw [denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    simp only [bind_eq_bind, liftM_lift_bind]
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk]
    rw [denote_bind ν _ _ Measurable.of_discrete,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    calc
      _ ≤ ∫⁻ value, f value + remaining * δ ∂μ op :=
        lintegral_mono fun value => ih value remaining (hcost.2 value)
      _ = (∫⁻ value, f value ∂μ op) + remaining * δ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ((∫⁻ out, out.elim 0 f ∂denote ν (handler op).run) +
          if risk op then δ else 0) + remaining * δ := add_le_add hlocal le_rfl
      _ = (∫⁻ out, out.elim 0 f ∂denote ν (handler op).run) + n * δ := by
        rw [add_assoc]
        congr 1
        cases h : risk op with
        | false => simp [remaining, h]
        | true =>
          have hn : 1 ≤ n := by simpa [h] using hcost.1
          simp only [↓reduceIte]
          rw [← one_add_mul]
          congr 1
          dsimp only [remaining]
          simp only [h, Bool.toNat_true]
          exact_mod_cast Nat.add_sub_of_le hn
      _ = _ := by
        congr 1
        apply lintegral_congr
        intro out
        cases out <;> simp [f, OptionT.run]

omit [∀ op, IsProbabilityMeasure (μ op)] [∀ op, IsProbabilityMeasure (ν op)] in
/-- Successful implemented outcomes are dominated by the ideal experiment's measure. -/
theorem denote_liftM_option_le
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (denote ν (handler op).run).comap some ≤ μ op)
    (x : P.FreeM α) (event : Set α) :
    denote ν (x.liftM handler).run (some '' event) ≤ denote μ x event := by
  have h := lintegral_liftM_option_le μ ν handler hstep x (event.indicator (fun _ => 1))
  rwa [← lintegral_comap_some, lintegral_indicator_const MeasurableSet.of_discrete,
    lintegral_indicator_const MeasurableSet.of_discrete, one_mul, one_mul,
    Option.measurableEmbedding_some.comap_apply] at h

/-- Event probabilities inherit the accumulated cutoff error without conditioning on success. -/
theorem denote_le_liftM_option_add
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (risk : P.A → Bool) (δ : ℝ≥0∞)
    (hstep : ∀ op, ∀ f : P.B op → ℝ≥0∞, (∀ value, f value ≤ 1) →
      ∫⁻ value, f value ∂μ op ≤
        (∫⁻ out, out.elim 0 f ∂denote ν (handler op).run) + if risk op then δ else 0)
    (x : P.FreeM α) (n : ℕ) (hcount : queryBoundP risk x ≤ n) (event : Set α) :
    denote μ x event ≤ denote ν (x.liftM handler).run (some '' event) + n * δ := by
  have h := lintegral_denote_le_liftM_option_add μ ν handler risk δ hstep x n hcount
    (event.indicator (fun _ => 1)) (fun value => by
      by_cases h : value ∈ event <;> simp [h])
  rwa [← lintegral_comap_some, lintegral_indicator_const MeasurableSet.of_discrete,
    lintegral_indicator_const MeasurableSet.of_discrete, one_mul, one_mul,
    Option.measurableEmbedding_some.comap_apply] at h

/-- A local sampler certificate gives an event bound for the whole adaptive experiment.
Successful draws are dominated by the ideal law; exhaustion accounts for the missing mass. -/
theorem denote_le_liftM_option_add_of_le
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (denote ν (handler op).run).comap some ≤ μ op)
    (risk : P.A → Bool) (δ : ℝ≥0∞)
    (hfailure : ∀ op, denote ν (handler op).run {none} ≤ if risk op then δ else 0)
    (x : P.FreeM α) (n : ℕ) (hcount : queryBoundP risk x ≤ n) (event : Set α) :
    denote μ x event ≤ denote ν (x.liftM handler).run (some '' event) + n * δ := by
  apply denote_le_liftM_option_add μ ν handler risk δ _ x n hcount event
  intro op f hf
  exact (lintegral_le_lintegral_option_add _ _ (hstep op) f hf).trans
    (add_le_add le_rfl (hfailure op))

/-- A two-sided real-valued error bound for any event of the implemented experiment. -/
theorem abs_toReal_denote_sub_liftM_option_le
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (denote ν (handler op).run).comap some ≤ μ op)
    (risk : P.A → Bool) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (hfailure : ∀ op, denote ν (handler op).run {none} ≤ if risk op then δ else 0)
    (x : P.FreeM α) (n : ℕ) (hcount : queryBoundP risk x ≤ n) (event : Set α) :
    |(denote μ x event).toReal -
      (denote ν (x.liftM handler).run (some '' event)).toReal| ≤ n * δ.toReal := by
  have hle := ENNReal.toReal_mono (measure_ne_top _ _)
    (denote_liftM_option_le μ ν handler hstep x event)
  have hupper := ENNReal.toReal_mono (by finiteness)
    (denote_le_liftM_option_add_of_le μ ν handler hstep risk δ hfailure x n hcount event)
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hupper
  linarith

end PFunctor.FreeM
