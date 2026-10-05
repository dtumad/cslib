/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Random
public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape
public import Cslib.Foundations.Data.PFunctor.Free.Measure.Approximation
public import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Cutoff error for adaptive finite sampling

Bounded rejection removes probability mass from the exact uniform measure. Applying this local
fact to a complete free program bounds any payoff in `[0, 1]` by the implemented payoff plus
the number of sampling calls times the per-call cutoff error.
-/

public section

namespace PFunctor.FreeM

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {P : PFunctor.{u, 0}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))
  (coin : P.FreeM (Fin 2)) (hcoin : denote μ coin = uniformOn Set.univ)

include hcoin

/-- Successful bounded samples are dominated by the exact uniform distribution. -/
theorem comap_denote_sampleFin_le (n bits attempts : ℕ) (hcover : n ≤ 2 ^ bits) :
    (denote μ (sampleFin coin n bits attempts)).comap some ≤ uniformOn Set.univ := by
  rw [denote_sampleFin μ coin hcoin, Resumption.comap_denote_truncate]
  rw [← Resumption.returnedMeasure_uniformFin hcover]
  exact le_iSup (Resumption.outputMeasure (fun _ => uniformOn Set.univ) ·
    (Resumption.uniformFin n (2 ^ bits))) attempts

variable [∀ op, IsProbabilityMeasure (μ op)]

omit [∀ op, IsProbabilityMeasure (μ op)] in
/-- Transporting a bounded sample through a finite equivalence preserves domination by the
uniform measure. No representation-specific distribution is needed by the caller. -/
theorem comap_denote_map_sampleFin_le {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] (n bits attempts : ℕ) (e : Fin n ≃ α)
    (hcover : n ≤ 2 ^ bits) :
    (denote μ (Option.map e <$> sampleFin coin n bits attempts)).comap some ≤
      uniformOn Set.univ := by
  rw [← map_uniformOn_univ e]
  have h := comap_denote_sampleFin_le μ coin hcoin n bits attempts hcover
  apply Measure.le_iff.mpr
  intro event hevent
  rw [Option.measurableEmbedding_some.comap_apply,
    ← map_eq_map, denote_map _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    Measure.map_apply Measurable.of_discrete hevent]
  have hpre : Option.map e ⁻¹' (some '' event) = some '' (e ⁻¹' event) := by
    ext out
    cases out <;> simp
  rw [hpre, ← Option.measurableEmbedding_some.comap_apply]
  exact h _

omit [∀ op, IsProbabilityMeasure (μ op)] in
/-- Re-encoding a successful finite draw leaves the cutoff probability unchanged. -/
theorem denote_map_sampleFin_none_le_of_bounds {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (n bits attempts : ℕ)
    (e : Fin n ≃ α) (hcover : n ≤ 2 ^ bits) (hsize : 2 ^ bits ≤ 2 * n) :
    denote μ (Option.map e <$> sampleFin coin n bits attempts) {none} ≤
      (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  rw [← map_eq_map, denote_map _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hpre : Option.map e ⁻¹' {none} = {none} := by
    ext out
    cases out <;> simp
  rw [hpre]
  exact denote_sampleFin_none_le_of_bounds μ coin hcoin n bits attempts hcover hsize

/-- A bounded sampler loses at most its failure probability for every bounded continuation. -/
theorem lintegral_uniform_le_sampleFin_add (n bits attempts : ℕ) [NeZero n]
    (hcover : n ≤ 2 ^ bits) (hsize : 2 ^ bits ≤ 2 * n)
    (post : Fin n → ℝ≥0∞) (hpost : ∀ value, post value ≤ 1) :
    ∫⁻ value, post value ∂uniformOn Set.univ ≤
      (∫⁻ out, out.elim 0 post ∂denote μ (sampleFin coin n bits attempts)) +
        (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  exact (lintegral_le_lintegral_option_add _ _
    (comap_denote_sampleFin_le μ coin hcoin n bits attempts hcover) post hpost).trans
      (add_le_add le_rfl
        (denote_sampleFin_none_le_of_bounds μ coin hcoin n bits attempts hcover hsize))

/-- A complete adaptive experiment loses at most `draws * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` when each ideal finite
sample is implemented by bounded binary rejection. The bound applies after stateful handlers
have been inlined, so it includes key generation, signing, and fresh cache entries. -/
theorem lintegral_uniform_le_liftM_sampleFin_add {Operation α : Type}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (range bits : Operation → ℕ) (attempts draws : ℕ) [∀ op, NeZero (range op)]
    (hcover : ∀ op, range op ≤ 2 ^ bits op) (hsize : ∀ op, 2 ^ bits op ≤ 2 * range op)
    (program : (PFunctor.mk Operation (fun op => Fin (range op))).FreeM α)
    (hdraws : queryBound program ≤ draws)
    (post : α → ℝ≥0∞) (hpost : ∀ value, post value ≤ 1) :
    ∫⁻ value, post value ∂denote (fun _ => uniformOn Set.univ) program ≤
      (∫⁻ out, out.elim 0 post ∂denote μ
        (program.liftM (fun op => OptionT.mk
          (sampleFin coin (range op) (bits op) attempts))).run) +
            draws * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  refine lintegral_denote_le_liftM_option_add
    (P := PFunctor.mk Operation (fun op => Fin (range op)))
    (fun _ => uniformOn Set.univ) μ
    (fun op => OptionT.mk (sampleFin coin (range op) (bits op) attempts))
    (fun _ => true) ((2 : ℝ≥0∞)⁻¹ ^ attempts) ?_ program draws ?_ post hpost
  · intro op f hf
    exact lintegral_uniform_le_sampleFin_add μ coin hcoin _ _ _ (hcover op) (hsize op) f hf
  · simpa only [queryBoundP_true] using hdraws

omit [∀ op, IsProbabilityMeasure (μ op)] in
/-- Cutoff failure can only remove successful outcomes from an adaptive finite-sampling
experiment. In particular, it cannot introduce successful forgeries or extractions. -/
theorem lintegral_liftM_sampleFin_le_uniform {Operation α : Type}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (range bits attempts : Operation → ℕ) (hcover : ∀ op, range op ≤ 2 ^ bits op)
    (program : (PFunctor.mk Operation (fun op => Fin (range op))).FreeM α)
    (post : α → ℝ≥0∞) :
    (∫⁻ out, out.elim 0 post ∂denote μ
      (program.liftM (fun op => OptionT.mk
        (sampleFin coin (range op) (bits op) (attempts op)))).run) ≤
      ∫⁻ value, post value ∂denote (fun _ => uniformOn Set.univ) program :=
  lintegral_liftM_option_le (fun _ => uniformOn Set.univ) μ _
    (fun op => comap_denote_sampleFin_le μ coin hcoin _ _ _ (hcover op)) program post

/-- Preparing and checking every slot of a finite tape incurs one cutoff error per slot,
including slots that a later consumer will leave unused. -/
theorem lintegral_replicate_uniform_le_sampleFin_add (n bits attempts count : ℕ) [NeZero n]
    [MeasurableSpace (List (Fin n))] [DiscreteMeasurableSpace (List (Fin n))]
    (hcover : n ≤ 2 ^ bits) (hsize : 2 ^ bits ≤ 2 * n)
    (post : List (Fin n) → ℝ≥0∞) (hpost : ∀ values, post values ≤ 1) :
    ∫⁻ values, post values ∂denote (P := PFunctor.mk Unit (fun _ => Fin n))
      (fun _ => uniformOn Set.univ) ((List.replicate count ()).mapM (fun _ => lift ())) ≤
        (∫⁻ values, values.elim 0 post ∂denote μ
          (List.mapM id <$>
            (List.replicate count ()).mapM (fun _ => sampleFin coin n bits attempts))) +
              count * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  let program := (List.replicate count ()).mapM
    (fun _ => lift (P := PFunctor.mk Unit (fun _ => Fin n)) ())
  have hcount : queryBound program ≤ count := by
    dsimp only [program]
    induction count with
    | zero => simp
    | succ count ih =>
      simp only [List.replicate_succ, List.mapM_cons, ← map_eq_pure_bind]
      apply (queryBound_bind_le _ _ count (fun value => by simpa using ih)).trans
      simp [queryBound_lift (P := PFunctor.mk Unit (fun _ => Fin n)), Nat.cast_add, add_comm]
  have h := lintegral_uniform_le_liftM_sampleFin_add μ coin hcoin
    (fun _ : Unit => n) (fun _ => bits) attempts count (fun _ => hcover) (fun _ => hsize)
    program hcount post hpost
  have hlift : (program.liftM (fun _ => OptionT.mk (sampleFin coin n bits attempts))) =
      (List.replicate count ()).mapM (fun _ => OptionT.mk (sampleFin coin n bits attempts)) := by
    dsimp only [program]
    rw [(isMonadHom_liftM _).map_listMapM]
    simp only [Function.comp_def, liftM_lift (P := PFunctor.mk Unit (fun _ => Fin n))]
  rw [hlift, denote_mapM_optionT] at h
  exact h

end PFunctor.FreeM
