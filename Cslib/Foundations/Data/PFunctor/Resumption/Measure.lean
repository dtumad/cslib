/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Resumption.Truncate
public import Cslib.Foundations.MeasureTheory.Monotone

/-!
# Returned values of possibly infinite computations

`outputMeasure μ k x` observes returns after at most `k` operations. Its increasing supremum
`returnedMeasure μ x` records nontermination as missing mass. Almost-sure termination is exactly
`IsProbabilityMeasure (returnedMeasure μ x)` when the operations are lossless.

`x.toMeasure μ` accepts the same explicit `PFunctor.OutputMeasure` bundle as `FreeM.toMeasure`.
Probability responses bound its mass by one; normalization still requires termination.

This extends VCVio's finite-fuel semantics. Agreement with `FreeM` needs no uniform bound on
branch depth: well-founded, infinitely branching programs are included.
-/

@[expose] public section

open MeasureTheory

universe uA uB v w

namespace PFunctor.Resumption

section Interpretation

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  {α : Type v} [MeasurableSpace α]

/-- The measure of values returned within the given number of operations. Returns cost no fuel. -/
noncomputable def outputMeasure (μ : (op : P.A) → Measure (P.B op)) :
    ℕ → Resumption P α → Measure α
  | 0, x => match dest x with
    | .inl a => Measure.dirac a
    | .inr _ => 0
  | k + 1, x => match dest x with
    | .inl a => Measure.dirac a
    | .inr ⟨op, cont⟩ => (μ op).bind fun b => outputMeasure μ k (cont b)

variable (μ : (op : P.A) → Measure (P.B op))

@[simp]
theorem outputMeasure_pure (k : ℕ) (a : α) :
    outputMeasure μ k (pure a) = Measure.dirac a := by cases k <;> rfl

@[simp]
theorem outputMeasure_query_zero (op : P.A) (cont : P.B op → Resumption P α) :
    outputMeasure μ 0 (query op cont) = 0 := rfl

@[simp]
theorem outputMeasure_query_succ (k : ℕ) (op : P.A) (cont : P.B op → Resumption P α) :
    outputMeasure μ (k + 1) (query op cont) =
      (μ op).bind fun b => outputMeasure μ k (cont b) := rfl

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

/-- More fuel can only increase the measure of returned values. -/
theorem outputMeasure_le_succ (k : ℕ) (x : Resumption P α) :
    outputMeasure μ k x ≤ outputMeasure μ (k + 1) x := by
  induction k generalizing x with
  | zero =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      exact bot_le
  | succ k ih =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      exact Measure.bind_mono_right Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable (Filter.Eventually.of_forall fun b => ih (cont b))

theorem monotone_outputMeasure (x : Resumption P α) : Monotone (outputMeasure μ · x) :=
  monotone_nat_of_le_succ fun k => outputMeasure_le_succ μ k x

/-- The measure of all returned values, with divergence represented by missing mass. -/
noncomputable def returnedMeasure (x : Resumption P α) : Measure α :=
  ⨆ k, outputMeasure μ k x

theorem returnedMeasure_apply (x : Resumption P α) (s : Set α) (hs : MeasurableSet s) :
    returnedMeasure μ x s = ⨆ k, outputMeasure μ k x s :=
  Measure.iSup_apply_of_monotone _ (monotone_outputMeasure μ x) s hs

omit [∀ op, DiscreteMeasurableSpace (P.B op)] in
@[simp]
theorem returnedMeasure_pure (a : α) : returnedMeasure μ (pure a) = Measure.dirac a := by
  simp [returnedMeasure]

/-- Unfolding one operation commutes with the returned-output limit. -/
theorem returnedMeasure_query (op : P.A) (cont : P.B op → Resumption P α) :
    returnedMeasure μ (query op cont) = (μ op).bind fun b => returnedMeasure μ (cont b) := by
  rw [returnedMeasure, ← (monotone_outputMeasure μ (query op cont)).iSup_nat_add 1]
  simp only [outputMeasure_query_succ, returnedMeasure]
  exact (Measure.bind_iSup_of_monotone (fun _ => Measurable.of_discrete.aemeasurable)
    Measurable.of_discrete.aemeasurable (fun b => monotone_outputMeasure μ (cont b))).symm

/-- Every finite approximation is a subprobability measure when operations are lossless. -/
theorem outputMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)]
    (k : ℕ) (x : Resumption P α) : outputMeasure μ k x Set.univ ≤ 1 := by
  induction k generalizing x with
  | zero =>
    rcases hx : dest x with a | node <;> simp [outputMeasure, hx]
  | succ k ih =>
    rcases hx : dest x with a | ⟨op, cont⟩
    · simp [outputMeasure, hx]
    · simp only [outputMeasure, hx]
      rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
      calc
        _ ≤ ∫⁻ _b, 1 ∂μ op := lintegral_mono fun b => ih (cont b)
        _ = 1 := by simp

theorem returnedMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)]
    (x : Resumption P α) : returnedMeasure μ x Set.univ ≤ 1 := by
  rw [returnedMeasure_apply μ x Set.univ MeasurableSet.univ]
  exact iSup_le fun k => outputMeasure_apply_univ_le_one μ k x

instance [∀ op, IsProbabilityMeasure (μ op)] (x : Resumption P α) :
    IsFiniteMeasure (returnedMeasure μ x) :=
  ⟨(returnedMeasure_apply_univ_le_one μ x).trans_lt ENNReal.one_lt_top⟩

/-- Every well-founded free program has exactly its original denotation in the resumption model. -/
@[simp]
theorem returnedMeasure_toResumption (x : P.FreeM α) :
    returnedMeasure μ x.toResumption = FreeM.denote μ x := by
  induction x with
  | pure a => exact returnedMeasure_pure μ a
  | lift_bind op cont ih =>
    change returnedMeasure μ (query op (fun b => (cont b).toResumption)) = _
    rw [returnedMeasure_query, FreeM.denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

variable {β : Type w} [MeasurableSpace β]

/-- Sequential substitution agrees with Giry bind, including missing mass from divergence. -/
theorem returnedMeasure_bind (x : Resumption P α) (f : α → Resumption P β)
    (hf : Measurable fun a => returnedMeasure μ (f a)) :
    returnedMeasure μ (x.bind f) =
      (returnedMeasure μ x).bind (fun a => returnedMeasure μ (f a)) := by
  have upper (k : ℕ) (x : Resumption P α) :
      outputMeasure μ k (x.bind f) ≤ (returnedMeasure μ x).bind
        (fun a => returnedMeasure μ (f a)) := by
    induction k generalizing x with
    | zero =>
      rcases hx : dest x with a | ⟨op, cont⟩
      · have heq : x = pure a := dest_injective (by simpa using hx)
        rw [heq, bind_pure_left, returnedMeasure_pure, Measure.dirac_bind hf]
        exact le_iSup (outputMeasure μ · (f a)) 0
      · simp only [outputMeasure, dest_bind, hx]
        exact bot_le
    | succ k ih =>
      rcases hx : dest x with a | ⟨op, cont⟩
      · have heq : x = pure a := dest_injective (by simpa using hx)
        rw [heq, bind_pure_left, returnedMeasure_pure, Measure.dirac_bind hf]
        exact le_iSup (outputMeasure μ · (f a)) (k + 1)
      · have heq : x = query op cont := dest_injective (by rw [dest_query]; exact hx)
        rw [heq, bind_query, outputMeasure_query_succ, returnedMeasure_query,
          Measure.bind_bind Measurable.of_discrete.aemeasurable hf.aemeasurable]
        exact Measure.bind_mono_right_of_forall Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable fun b => ih (cont b)
  have lower (k : ℕ) (x : Resumption P α) :
      (outputMeasure μ k x).bind (fun a => returnedMeasure μ (f a)) ≤
        returnedMeasure μ (x.bind f) := by
    induction k generalizing x with
    | zero =>
      rcases hx : dest x with a | ⟨op, cont⟩
      · have heq : x = pure a := dest_injective (by simpa using hx)
        simp [heq, Measure.dirac_bind hf]
      · simp only [outputMeasure, hx, Measure.bind_zero_left]
        exact bot_le
    | succ k ih =>
      rcases hx : dest x with a | ⟨op, cont⟩
      · have heq : x = pure a := dest_injective (by simpa using hx)
        simp [heq, Measure.dirac_bind hf]
      · have heq : x = query op cont := dest_injective (by rw [dest_query]; exact hx)
        rw [heq, outputMeasure_query_succ, bind_query, returnedMeasure_query,
          Measure.bind_bind Measurable.of_discrete.aemeasurable hf.aemeasurable]
        exact Measure.bind_mono_right_of_forall Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable fun b => ih (cont b)
  apply le_antisymm (iSup_le fun k => upper k x)
  rw [returnedMeasure, Measure.iSup_bind_of_monotone _ (monotone_outputMeasure μ x) _ hf]
  exact iSup_le fun k => lower k x

/-- On a discrete intermediate space, every resumption continuation is measurable. -/
theorem returnedMeasure_bind_of_discrete [DiscreteMeasurableSpace α]
    (x : Resumption P α) (f : α → Resumption P β) :
    returnedMeasure μ (x.bind f) = (returnedMeasure μ x).bind
      (fun a => returnedMeasure μ (f a)) :=
  returnedMeasure_bind μ x f Measurable.of_discrete

/-- Measurable postprocessing commutes with the returned-output interpretation. -/
theorem returnedMeasure_map (x : Resumption P α) (f : α → β) (hf : Measurable f) :
    returnedMeasure μ (map f x) = (returnedMeasure μ x).map f := by
  rw [map, returnedMeasure_bind]
  · simp only [returnedMeasure_pure]
    exact Measure.bind_dirac_eq_map _ hf
  · simpa only [returnedMeasure_pure, Function.comp_def] using Measure.measurable_dirac.comp hf

universe uQ

/-- Inlining possibly infinite handlers into a free program preserves measure semantics. -/
theorem returnedMeasure_liftM {Q : PFunctor.{uQ, v}}
    [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
    (handler : (op : Q.A) → Resumption P (Q.B op)) (x : Q.FreeM α) :
    returnedMeasure μ (x.liftM handler) =
      FreeM.denote (fun op => returnedMeasure μ (handler op)) x := by
  induction x with
  | pure a => exact returnedMeasure_pure μ a
  | lift_bind op cont ih =>
    change returnedMeasure μ ((handler op).bind fun b => (cont b).liftM handler) = _
    rw [returnedMeasure_bind μ _ _ Measurable.of_discrete,
      FreeM.denote_lift_bind _ _ _ Measurable.of_discrete.aemeasurable]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall ih)

end Interpretation

section Bundled

universe uQ

variable {P : PFunctor.{uA, uB}} {mP : ∀ op, MeasurableSpace (P.B op)}
  {α : Type v} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]

/-- Interpret a possibly infinite program using explicitly chosen response measures.
Divergence is represented by missing mass. -/
noncomputable def toMeasure (x : Resumption P α) (μ : OutputMeasure P) : Measure α :=
  returnedMeasure μ x

theorem toMeasure_ofMeasure (x : Resumption P α) (μ : (op : P.A) → Measure (P.B op)) :
    x.toMeasure (.ofMeasure μ) = returnedMeasure μ x := rfl

variable (μ : OutputMeasure P)

@[simp]
theorem toMeasure_pure (a : α) : (pure a : Resumption P α).toMeasure μ = Measure.dirac a :=
  returnedMeasure_pure μ a

variable [∀ op, DiscreteMeasurableSpace (P.B op)]

theorem toMeasure_query (op : P.A) (cont : P.B op → Resumption P α) :
    (query op cont).toMeasure μ = (μ op).bind fun b => (cont b).toMeasure μ :=
  returnedMeasure_query μ op cont

@[simp]
theorem toMeasure_toResumption (x : P.FreeM α) :
    x.toResumption.toMeasure μ = x.toMeasure μ := returnedMeasure_toResumption μ x

theorem toMeasure_apply_univ_le_one [∀ op, IsProbabilityMeasure (μ op)] (x : Resumption P α) :
    x.toMeasure μ Set.univ ≤ 1 := returnedMeasure_apply_univ_le_one μ x

instance [∀ op, IsProbabilityMeasure (μ op)] (x : Resumption P α) :
    IsFiniteMeasure (x.toMeasure μ) :=
  inferInstanceAs (IsFiniteMeasure (returnedMeasure μ x))

theorem toMeasure_bind (x : Resumption P α) (f : α → Resumption P β)
    (hf : Measurable fun a => (f a).toMeasure μ) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  returnedMeasure_bind μ x f hf

theorem toMeasure_bind_of_discrete [DiscreteMeasurableSpace α]
    (x : Resumption P α) (f : α → Resumption P β) :
    (x.bind f).toMeasure μ = (x.toMeasure μ).bind fun a => (f a).toMeasure μ :=
  toMeasure_bind μ x f Measurable.of_discrete

theorem toMeasure_map (x : Resumption P α) (f : α → β) (hf : Measurable f) :
    (map f x).toMeasure μ = (x.toMeasure μ).map f := returnedMeasure_map μ x f hf

/-- Possibly infinite handlers preserve a free program's chosen interpretation when their
returned measures implement the specified operation laws. -/
theorem toMeasure_liftM {Q : PFunctor.{uQ, v}} {mQ : ∀ op, MeasurableSpace (Q.B op)}
    [∀ op, DiscreteMeasurableSpace (Q.B op)] (ν : OutputMeasure Q)
    (handler : (op : Q.A) → Resumption P (Q.B op))
    (hhandler : ∀ op, (handler op).toMeasure μ = ν op) (x : Q.FreeM α) :
    (x.liftM handler).toMeasure μ = x.toMeasure ν := by
  change returnedMeasure μ (x.liftM handler) = FreeM.denote ν x
  rw [returnedMeasure_liftM]
  congr 1
  funext op
  exact hhandler op

end Bundled

end PFunctor.Resumption
