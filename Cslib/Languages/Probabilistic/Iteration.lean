/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Basic
public import Cslib.Probability.PMF
public import Mathlib.Data.List.OfFn

/-!
# Bounded adaptive probabilistic iteration

`OracleComp.iterate count step initial` runs a bounded loop whose next state is sampled from
`step` at the current state. The invariant rule talks only about supported transitions.
When each reachable transition has a uniform-seed evaluator, the complete loop is a deterministic
fold over independent seeds. State types need not be finite.

Approximate invariants compose by adding their per-step failure probabilities, even when
later steps depend on earlier outcomes. The error rule requires no independence assumption.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {Query : Type u} {Response : Query → Type u} {State : Type v}

/-- Execute a state-dependent probabilistic step a bounded number of times. -/
def iterate : ℕ → (State → OracleComp Query Response State) → State →
    OracleComp Query Response State
  | 0, _, initial => pure initial
  | count + 1, step, initial => iterate count step initial >>= step

@[simp] theorem iterate_zero (step : State → OracleComp Query Response State) (initial : State) :
    iterate 0 step initial = pure initial := rfl

theorem iterate_succ (count : ℕ) (step : State → OracleComp Query Response State)
    (initial : State) :
    iterate (count + 1) step initial = iterate count step initial >>= step := rfl

/-- A state representation that commutes with one step commutes with the complete loop. -/
theorem iterate_map {Other : Type v} (count : ℕ)
    (step : State → OracleComp Query Response State)
    (next : Other → OracleComp Query Response Other) (f : State → Other)
    (hstep : ∀ state, next (f state) = f <$> step state) (initial : State) :
    iterate count next (f initial) = f <$> iterate count step initial := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [iterate_succ, ih, bind_map_left, map_bind, hstep]

end OracleComp

namespace ProbComp

variable {State Seed : Type*}

/-- An invariant preserved by every supported transition holds on every possible final state. -/
theorem iterate_invariant (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next) :
    ∀ state ∈ (eval (OracleComp.iterate count step initial)).support, invariant count state := by
  have htrace (i : ℕ) (hi : i ≤ count) :
      ∀ state ∈ (eval (OracleComp.iterate i step initial)).support, invariant i state := by
    induction i with
    | zero => simpa using hinit
    | succ i ih =>
      intro next hnext
      rw [OracleComp.iterate_succ, eval_bind, PMF.mem_support_bind_iff] at hnext
      obtain ⟨state, hstate, hnext⟩ := hnext
      exact hpreserve i (by lia) state (ih (by lia) state hstate) next hnext
  exact htrace count le_rfl

/-- Per-step failures of an invariant accumulate additively across an adaptive loop.
The local bound is needed only at states where the preceding invariant holds. -/
theorem iterate_failure_le (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial) (error : ℕ → ENNReal)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      (eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next} ≤ error i) :
    (eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state} ≤ ∑ i ∈ Finset.range count, error i := by
  classical
  have htrace (i : ℕ) (hi : i ≤ count) :
      (eval (OracleComp.iterate i step initial)).toOuterMeasure
        {state | ¬ invariant i state} ≤ ∑ j ∈ Finset.range i, error j := by
    induction i with
    | zero => simp [eval_pure, PMF.toOuterMeasure_pure_apply, hinit]
    | succ i ih =>
      rw [OracleComp.iterate_succ, eval_bind, Finset.sum_range_succ]
      exact (Probability.PMF.toOuterMeasure_bind_failure_le _ _
        {state | invariant i state} _ (error i)
        (fun state _ hinvariant => hstep i (by lia) state hinvariant)).trans
          (add_le_add (ih (by lia)) le_rfl)
  exact htrace count le_rfl

/-- The real-valued form of the adaptive error rule. -/
theorem iterate_failure_toReal_le (count : ℕ) (step : State → ProbComp State) (initial : State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial) (error : ℕ → ℝ)
    (herror : ∀ i < count, 0 ≤ error i)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      ((eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next}).toReal ≤ error i) :
    ((eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state}).toReal ≤ ∑ i ∈ Finset.range count, error i := by
  have h := iterate_failure_le count step initial invariant hinit
    (fun i => ENNReal.ofReal (error i)) (fun i hi state hinvariant =>
      (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _)
        (herror i hi)).mpr (hstep i hi state hinvariant))
  have hnonneg := fun i hi => herror i (Finset.mem_range.mp hi)
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg] at h
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg hnonneg) h

/-- A uniform per-round error `ε` gives total error at most `count * ε`, including adaptive
rounds and state spaces that are not finite. -/
theorem iterate_failure_toReal_le_mul (count : ℕ) (step : State → ProbComp State)
    (initial : State) (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    {error : ℝ} (herror : 0 ≤ error)
    (hstep : ∀ i < count, ∀ state, invariant i state →
      ((eval (step state)).toOuterMeasure {next | ¬ invariant (i + 1) next}).toReal ≤ error) :
    ((eval (OracleComp.iterate count step initial)).toOuterMeasure
      {state | ¬ invariant count state}).toReal ≤ count * error := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    iterate_failure_toReal_le count step initial invariant hinit (fun _ => error)
      (fun _ _ => herror) hstep

/-- A common finite seed realizes an adaptive loop exactly when it realizes each reachable
step. The law is a fold over independently uniform seeds; no enumeration of states is needed. -/
theorem eval_iterate_of_uniform [Fintype Seed] [Nonempty Seed]
    (count : ℕ) (step : State → ProbComp State) (initial : State) (evaluate : State → Seed → State)
    (invariant : ℕ → State → Prop) (hinit : invariant 0 initial)
    (hpreserve : ∀ i < count, ∀ state, invariant i state →
      ∀ next ∈ (eval (step state)).support, invariant (i + 1) next)
    (hlaw : ∀ i < count, ∀ state, invariant i state →
      eval (step state) = (PMF.uniformOfFintype Seed).map (evaluate state)) :
    eval (OracleComp.iterate count step initial) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
  have htrace (i : ℕ) (hi : i ≤ count) : eval (OracleComp.iterate i step initial) =
      (PMF.uniformOfFintype (Fin i → Seed)).map
        (fun seeds => (List.ofFn seeds).foldl evaluate initial) := by
    induction i with
    | zero =>
      rw [OracleComp.iterate_zero, eval_pure]
      simp only [List.ofFn_zero, List.foldl_nil, Function.const_def, PMF.map_const]
    | succ i ih =>
      rw [OracleComp.iterate_succ, eval_bind]
      trans (eval (OracleComp.iterate i step initial)).bind
        (fun state => (PMF.uniformOfFintype Seed).map (evaluate state))
      · apply Probability.PMF.bind_congr_on_support
        intro state hstate
        exact hlaw i (by lia) state (iterate_invariant i step initial invariant hinit
          (fun j hj => hpreserve j (by lia)) state hstate)
      · rw [ih (by lia), ← Probability.PMF.uniformOfFintype_map_equiv
          ((Equiv.prodComm (Fin i → Seed) Seed).trans (Fin.snocEquiv (fun _ => Seed))),
          PMF.map_comp, Probability.PMF.uniformOfFintype_prod]
        simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
          Fin.snocEquiv, Equiv.prodComm, Equiv.trans_apply, Equiv.coe_fn_mk,
          List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, Prod.swap,
          List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact htrace count le_rfl

end ProbComp

end Cslib
