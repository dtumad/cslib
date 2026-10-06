/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Measure
public import Mathlib.Probability.ConditionalProbability

/-!
# Guarded iteration and rejection sampling

`iterate body s` runs a loop from the state `s`. Each round `body s` is an operation followed by a
free program, which returns either the state for the next round or the result of the loop
(`iterate_eq`, and for output measures `toMeasure_iterate`). Since every round begins with an
operation, the resumption is productive, even when the loop runs forever.

Rejection sampling (`repeatUntil x s`) repeats a computation `x` that begins with an operation,
until `x` returns a value in `s`. When the operations are answered by probability measures and `x`
returns a value in `s` with positive probability, rejection sampling returns the law of `x`
conditioned on `s` (`toMeasure_repeatUntil`), and so returns almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe uA uB u

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, uB}} {σ α : Type u}

section Iterate

variable (body : σ → P.Obj (P.FreeM (σ ⊕ α)))

/-- One step of guarded iteration within a round: start the round of a state, return a result,
or perform the next operation of the round. -/
def iterateStep : P.FreeM (σ ⊕ α) → α ⊕ P.Obj (P.FreeM (σ ⊕ α))
  | .pure (.inl s) => .inr (body s)
  | .pure (.inr a) => .inl a
  | .liftBind b k => .inr (.mk b k)

@[simp]
theorem iterateStep_pure_inl (s : σ) : iterateStep body (pure (.inl s)) = .inr (body s) := rfl

@[simp]
theorem iterateStep_pure_inr (a : α) : iterateStep body (pure (.inr a)) = .inl a := rfl

@[simp]
theorem iterateStep_lift_bind (b : P.A) (k : P.B b → P.FreeM (σ ⊕ α)) :
    iterateStep body ((FreeM.lift b).bind k) = .inr (.mk b k) := rfl

/-- Guarded iteration from the state `s`: run the round `body s`, an operation followed by a free
program, then continue from the state it returns, or return its result. -/
def iterate (s : σ) : Resumption P α :=
  corec (iterateStep body) (pure (.inl s))

/-- Finishing a round of guarded iteration, then continuing the iteration. -/
theorem corec_iterateStep (x : P.FreeM (σ ⊕ α)) :
    corec (iterateStep body) x = x.toResumption.bind (Sum.elim (iterate body) pure) := by
  induction x with
  | pure r =>
    rcases r with s | a
    · simp only [FreeM.toResumption_pure, Resumption.pure_bind, Sum.elim_inl]
      rfl
    · exact dest_injective (by simp [dest_corec])
  | lift_bind b k ih =>
    exact dest_injective (by simp [dest_corec, Resumption.bind_assoc, ← ih, Function.comp_def])

/-- Guarded iteration runs a round, then continues from the state it returns, or returns its
result. -/
theorem iterate_eq (s : σ) :
    iterate body s = (lift (body s).fst).bind fun b =>
      ((body s).snd b).toResumption.bind (Sum.elim (iterate body) pure) := by
  refine dest_injective ?_
  rw [iterate, dest_corec, iterateStep_pure_inl, dest_lift_bind]
  simp [PFunctor.map, Function.comp_def, corec_iterateStep]

variable [∀ b, MeasurableSpace (P.B b)] [∀ b, DiscreteMeasurableSpace (P.B b)] [MeasurableSpace σ]
  [MeasurableSpace α] [DiscreteMeasurableSpace (σ ⊕ α)] (μ : (b : P.A) → Measure (P.B b))

/-- The output measure of guarded iteration is that of a round, followed by the output measure of
the iteration from the state it returns, or by the Dirac measure at its result. -/
theorem toMeasure_iterate (s : σ) :
    (iterate body s).toMeasure μ =
      (((FreeM.lift (body s).fst).bind (body s).snd).toMeasure μ).bind
        (Sum.elim (fun s => (iterate body s).toMeasure μ) .dirac) := by
  rw [iterate_eq, toMeasure_lift_bind, FreeM.toMeasure_lift_bind,
    Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  congr 1
  funext b
  rw [toMeasure_bind_of_discrete, FreeM.toMeasure_toResumption]
  congr 1
  funext r
  cases r <;> simp

end Iterate

section Repeat

variable (x : P.Obj (P.FreeM α)) (s : Set α) [DecidablePred (· ∈ s)]

/-- Rejection sampling: repeat the computation `x`, which begins with an operation, until it
returns a value in `s`, and return that value. -/
def repeatUntil : Resumption P α :=
  iterate (σ := PUnit)
    (fun _ => P.map (fun y => (fun a => if a ∈ s then .inr a else .inl ⟨⟩) <$> y) x) ⟨⟩

/-- Rejection sampling runs `x`, then returns its value if it lies in `s`, and starts again
otherwise. -/
theorem repeatUntil_eq :
    repeatUntil x s = ((FreeM.lift x.fst).bind x.snd).toResumption.bind fun a =>
      if a ∈ s then pure a else repeatUntil x s := by
  conv_lhs => rw [repeatUntil, iterate_eq]
  simp [Resumption.bind_assoc, PFunctor.map, apply_ite, repeatUntil]

variable [∀ b, MeasurableSpace (P.B b)] [∀ b, DiscreteMeasurableSpace (P.B b)]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] (μ : (b : P.A) → Measure (P.B b))
  [∀ b, IsProbabilityMeasure (μ b)]

/-- When `x` returns a value in `s` with positive probability, rejection sampling returns the law
of `x` conditioned on returning a value in `s`. -/
theorem toMeasure_repeatUntil (hs : ((FreeM.lift x.fst).bind x.snd).toMeasure μ s ≠ 0) :
    (repeatUntil x s).toMeasure μ = (((FreeM.lift x.fst).bind x.snd).toMeasure μ)[|s] := by
  set ν := ((FreeM.lift x.fst).bind x.snd).toMeasure μ
  have hfix := congrArg (toMeasure · μ) (repeatUntil_eq x s)
  simp only [toMeasure_bind_of_discrete, FreeM.toMeasure_toResumption] at hfix
  set T := (repeatUntil x s).toMeasure μ
  ext t ht
  have key : T t = ν (s ∩ t) + T t * ν sᶜ := by
    have h (y : α) : ((if y ∈ s then pure y else repeatUntil x s).toMeasure μ) t =
        s.indicator (t.indicator 1) y + sᶜ.indicator (fun _ => T t) y := by
      by_cases hy : y ∈ s <;> simp [hy, Measure.dirac_apply' _ ht, T]
    conv_lhs => rw [hfix]
    rw [Measure.bind_apply ht Measurable.of_discrete.aemeasurable]
    simp only [h]
    rw [lintegral_add_left .of_discrete, lintegral_indicator .of_discrete,
      lintegral_indicator_one ht, lintegral_indicator .of_discrete, setLIntegral_const,
      Measure.restrict_apply ht, Set.inter_comm]
  have hsum : ν s + ν sᶜ = 1 := by rw [measure_add_measure_compl .of_discrete, measure_univ]
  rw [cond_apply .of_discrete, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff hs (measure_ne_top _ _),
    ← ENNReal.add_left_inj (ENNReal.mul_ne_top (measure_ne_top T t) (measure_ne_top ν sᶜ)),
    ← key, mul_comm, ← mul_add, hsum, mul_one]

/-- When `x` returns a value in `s` with positive probability, rejection sampling returns almost
surely. -/
theorem isProbabilityMeasure_toMeasure_repeatUntil
    (hs : ((FreeM.lift x.fst).bind x.snd).toMeasure μ s ≠ 0) :
    IsProbabilityMeasure ((repeatUntil x s).toMeasure μ) := by
  rw [toMeasure_repeatUntil x s μ hs]
  exact cond_isProbabilityMeasure hs

end Repeat

end PFunctor.Resumption
