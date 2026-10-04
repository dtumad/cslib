/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Init
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Monotone operations and limits of measures

Giry bind is monotone in a measurable measure-valued continuation. The lattice supremum of an
increasing sequence of measures is its pointwise supremum on measurable sets. Lower integration
and Giry bind commute with these increasing limits.

These facts are the measure-theoretic basis for interpreting progressively deeper observations
of a potentially nonterminating computation: returned mass grows with fuel, and its limit remains
a measure rather than merely a pointwise set function.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Giry bind is monotone in an almost-everywhere measurable continuation. -/
theorem bind_mono_right {μ : Measure α} {f g : α → Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.bind_apply hs hf, Measure.bind_apply hs hg]
  exact lintegral_mono_ae <| hfg.mono fun _ hx => hx s

/-- Giry bind preserves pointwise order of almost-everywhere measurable continuations.
The pointwise hypothesis lets generalized congruence descend into the continuations. -/
@[gcongr]
theorem bind_mono_right_of_forall {μ : Measure α} {f g : α → Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : ∀ x, f x ≤ g x) :
    μ.bind f ≤ μ.bind g :=
  bind_mono_right hf hg (Filter.Eventually.of_forall hfg)

private theorem iSup_tsum_of_monotone (f : ℕ → ℕ → ENNReal)
    (hf : ∀ i, Monotone fun n => f n i) :
    (⨆ n, ∑' i, f n i) = ∑' i, ⨆ n, f n i := by
  calc
    (⨆ n, ∑' i, f n i) = ⨆ n, ⨆ s : Finset ℕ, ∑ i ∈ s, f n i := by
      simp_rw [ENNReal.tsum_eq_iSup_sum]
    _ = ⨆ s : Finset ℕ, ⨆ n, ∑ i ∈ s, f n i := iSup_comm
    _ = ⨆ s : Finset ℕ, ∑ i ∈ s, ⨆ n, f n i := by
      congr 1
      funext s
      exact (ENNReal.finsetSum_iSup_of_monotone (s := s) hf).symm
    _ = ∑' i, ⨆ n, f n i := ENNReal.tsum_eq_iSup_sum.symm

/-- The measure whose value on a measurable set is the supremum of an increasing sequence. -/
private noncomputable def monotoneLimit (μ : ℕ → Measure α) (hμ : Monotone μ) : Measure α :=
  Measure.ofMeasurable
    (fun s _ => ⨆ n, μ n s)
    (by simp)
    (by
      intro s hs hdisjoint
      simp_rw [measure_iUnion hdisjoint hs]
      exact iSup_tsum_of_monotone (fun n i => μ n (s i)) fun i _ _ hnm => hμ hnm (s i))

private theorem monotoneLimit_apply (μ : ℕ → Measure α) (hμ : Monotone μ)
    (s : Set α) (hs : MeasurableSet s) :
    monotoneLimit μ hμ s = ⨆ n, μ n s :=
  Measure.ofMeasurable_apply s hs

/-- The lattice supremum of an increasing sequence of measures is pointwise on measurable sets. -/
theorem iSup_apply_of_monotone (μ : ℕ → Measure α) (hμ : Monotone μ)
    (s : Set α) (hs : MeasurableSet s) :
    (⨆ n, μ n) s = ⨆ n, μ n s := by
  have hSup : (⨆ n, μ n) = monotoneLimit μ hμ := by
    apply le_antisymm
    · refine iSup_le fun n => Measure.le_iff.mpr fun t ht => ?_
      rw [monotoneLimit_apply μ hμ t ht]
      exact le_iSup (fun k => μ k t) n
    · refine Measure.le_iff.mpr fun t ht => ?_
      rw [monotoneLimit_apply μ hμ t ht]
      exact iSup_le fun n => (le_iSup (fun k => μ k) n) t
  rw [hSup, monotoneLimit_apply μ hμ s hs]

/-- Giry bind commutes with an increasing sequence of measurable continuations. -/
theorem bind_iSup_of_monotone {μ : Measure α} {f : ℕ → α → Measure β}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : AEMeasurable (fun a => ⨆ n, f n a) μ)
    (hmono : ∀ a, Monotone fun n => f n a) :
    μ.bind (fun a => ⨆ n, f n a) = ⨆ n, μ.bind (f n) := by
  ext s hs
  rw [bind_apply hs hlim, iSup_apply_of_monotone _
    (fun i j hij => bind_mono_right (hf i) (hf j)
      (Filter.Eventually.of_forall fun a => hmono a hij)) s hs]
  simp_rw [iSup_apply_of_monotone _ (hmono _) s hs, bind_apply hs (hf _)]
  exact lintegral_iSup' (fun n => (measurable_coe hs).comp_aemeasurable (hf n))
    (Filter.Eventually.of_forall fun a i j hij => hmono a hij s)

/-- Integrating against an increasing limit of measures commutes with the limit. -/
theorem lintegral_iSup_of_monotone (μ : ℕ → Measure α) (hμ : Monotone μ)
    (f : α → ℝ≥0∞) : (∫⁻ a, f a ∂(⨆ n, μ n)) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  have hs (g : SimpleFunc α ℝ≥0∞) : g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := by
    simp only [SimpleFunc.lintegral,
      iSup_apply_of_monotone μ hμ _ (SimpleFunc.measurableSet_preimage _ _)]
    simp_rw [ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun r i j hij =>
      mul_le_mul' le_rfl (hμ hij _)
  simp only [lintegral_def, hs, iSup_comm (ι := ℕ)]

/-- Giry bind preserves increasing limits in its source measure. -/
theorem iSup_bind_of_monotone (μ : ℕ → Measure α) (hμ : Monotone μ)
    (f : α → Measure β) (hf : Measurable f) :
    (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hmono : Monotone fun n => (μ n).bind f := by
    intro i j hij
    apply Measure.le_iff.mpr
    intro s hs
    simp only [bind_apply hs hf.aemeasurable]
    exact lintegral_mono' (hμ hij) le_rfl
  ext s hs
  rw [bind_apply hs hf.aemeasurable, iSup_apply_of_monotone _ hmono _ hs,
    lintegral_iSup_of_monotone μ hμ]
  simp only [bind_apply hs hf.aemeasurable]

end MeasureTheory.Measure
