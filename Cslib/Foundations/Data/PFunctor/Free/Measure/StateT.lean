/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Init.Control.Option

/-! # Accumulating local simulation errors in stateful programs -/

public section

namespace PFunctor.FreeM

open MeasureTheory MonadAttach
open scoped ENNReal

universe u

variable {P Q : PFunctor.{u, u}} {α State : Type u}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [∀ op, Countable (P.B op)]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
  [MeasurableSpace State] [DiscreteMeasurableSpace State] [Countable State]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : Q.A) → Measure (Q.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- Local errors accumulate only at selected operations. The state-size bound allows an
operation's error estimate to depend on earlier queries, as with random-oracle programming.
Both handlers and their continuations may depend on every previous answer. -/
theorem lintegral_liftM_stateT_le_add
    (handler : (op : P.A) → StateT State Q.FreeM (P.B op))
    (simulator : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (risk grow : P.A → Bool) (size : State → ℕ) (bound : ℕ) (δ : ℝ≥0∞)
    (hsize : ∀ op state out, CanReturn ((handler op).run state) out →
      size out.2 ≤ size state + (grow op).toNat)
    (hstep : ∀ op state, size state ≤ bound →
      ∀ f : P.B op × State → ℝ≥0∞, (∀ out, f out ≤ 1) →
        ∫⁻ out, f out ∂denote μ ((handler op).run state) ≤
          (∫⁻ out, out.elim 0 f ∂denote μ ((simulator op).run state).run) +
            if risk op then δ else 0)
    (x : P.FreeM α) (state : State) (n : ℕ)
    (hbudget : (size state : ℕ∞) + queryBoundP grow x ≤ bound)
    (hrisk : queryBoundP risk x ≤ n)
    (post : α × State → ℝ≥0∞) (hpost : ∀ out, post out ≤ 1) :
    ∫⁻ out, post out ∂denote μ ((x.liftM handler).run state) ≤
      (∫⁻ out, out.elim 0 post ∂denote μ ((x.liftM simulator).run state).run) + n * δ := by
  induction x generalizing state n with
  | pure a =>
    change (∫⁻ out, post out ∂denote μ (pure (a, state))) ≤
      (∫⁻ out, out.elim 0 post ∂denote μ (pure (some (a, state)))) + n * δ
    simp only [denote_pure,
      lintegral_dirac' _ Measurable.of_discrete, Option.elim_some]
    exact le_self_add
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le risk op cont n hrisk
    let remaining := n - (risk op).toNat
    let f := fun out : P.B op × State =>
      ∫⁻ result, result.elim 0 post ∂denote μ (((cont out.1).liftM simulator).run out.2).run
    have hf (out) : f out ≤ 1 := by
      apply lintegral_le_const
      exact Filter.Eventually.of_forall fun result => by
        cases result with
        | none => exact zero_le
        | some result => exact hpost result
    have hstate : size state ≤ bound := by
      exact_mod_cast (le_self_add.trans hbudget)
    have hnext (out) (hout : CanReturn ((handler op).run state) out) :
        (size out.2 : ℕ∞) + queryBoundP grow (cont out.1) ≤ bound := by
      calc
        _ ≤ ((size state + (grow op).toNat : ℕ) : ℕ∞) +
            queryBoundP grow (cont out.1) :=
          add_le_add (by exact_mod_cast hsize op state out hout) le_rfl
        _ ≤ (size state : ℕ∞) + queryBoundP grow (lift op >>= cont) := by
          simp only [Nat.cast_add, queryBoundP_lift_bind, add_assoc]
          gcongr
          · cases grow op <;> simp
          · exact le_iSup (fun b => queryBoundP grow (cont b)) out.1
        _ ≤ bound := hbudget
    have hlocal := hstep op state hstate f hf
    simp only [bind_eq_bind, liftM_lift_bind, StateT.run_bind]
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk]
    simp only [denote_bind _ _ _ Measurable.of_discrete,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    calc
      _ ≤ ∫⁻ out, f out + remaining * δ ∂denote μ ((handler op).run state) := by
        apply lintegral_mono_ae
        filter_upwards [ae_canReturn μ ((handler op).run state)] with out hout
        exact ih out.1 out.2 remaining (hnext out hout) (hcost.2 out.1)
      _ = (∫⁻ out, f out ∂denote μ ((handler op).run state)) + remaining * δ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ((∫⁻ out, out.elim 0 f ∂denote μ ((simulator op).run state).run) +
          if risk op then δ else 0) + remaining * δ := add_le_add hlocal le_rfl
      _ = (∫⁻ out, out.elim 0 f ∂denote μ ((simulator op).run state).run) + n * δ := by
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
          exact_mod_cast (Nat.add_sub_of_le hn)
      _ = _ := by
        congr 1
        apply lintegral_congr
        intro out
        cases out <;> simp [f, OptionT.run]

end PFunctor.FreeM
