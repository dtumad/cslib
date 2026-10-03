/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Conditioning
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Independent finite PMF products

A product of finite distributions assigns each tuple the product of its coordinate masses.
Its induced measure is Mathlib's product measure, so its coordinates satisfy the existing
independence and concentration theorems. Mapping coordinates commutes with this product.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α β : ι → Type*} [∀ i, Finite (α i)]

open Classical in
/-- Draw each coordinate independently from its specified finite distribution. -/
noncomputable def pi (p : ∀ i, PMF (α i)) : PMF (∀ i, α i) :=
  let (i : ι) := Fintype.ofFinite (α i)
  PMF.ofFintype (fun outcome => ∏ i, p i (outcome i)) (by
    have hsum (i : ι) : ∑ a, p i a = 1 := by simpa only [tsum_fintype] using (p i).tsum_coe
    rw [← Fintype.prod_sum (fun i a => p i a)]
    simp only [hsum, Finset.prod_const_one])

/-- Independent tuple masses are products of their coordinate masses. -/
@[simp] theorem pi_apply (p : ∀ i, PMF (α i)) (outcome : ∀ i, α i) :
    pi p outcome = ∏ i, p i (outcome i) := rfl

/-- A tuple can occur precisely when every coordinate can occur. -/
theorem mem_support_pi_iff (p : ∀ i, PMF (α i)) (outcome : ∀ i, α i) :
    outcome ∈ (pi p).support ↔ ∀ i, outcome i ∈ (p i).support := by
  classical
  simp only [PMF.mem_support_iff, pi_apply, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_const]

/-- The PMF product agrees with the existing measure-theoretic product. -/
theorem toMeasure_pi [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, PMF (α i)) :
    (pi p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro outcome
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton,
    pi_apply]

/-- Coordinate projections of the product are mutually independent. -/
theorem iIndepFun_pi [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, PMF (α i)) :
    iIndepFun (fun i (outcome : ∀ i, α i) => outcome i) (pi p).toMeasure := by
  rw [toMeasure_pi]
  exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Each coordinate of the independent product has its specified distribution. -/
@[simp] theorem pi_map_eval (p : ∀ i, PMF (α i)) (i : ι) :
    (pi p).map (fun outcome => outcome i) = p i := by
  let (i : ι) : MeasurableSpace (α i) := ⊤
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_pi_apply i), toMeasure_pi]
  exact (measurePreserving_eval (fun i => (p i).toMeasure) i).map_eq

open Classical in
/-- Independent uniform coordinates give the uniform distribution on tuples. -/
theorem pi_uniformOfFintype [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] :
    pi (fun i => PMF.uniformOfFintype (α i)) = PMF.uniformOfFintype (∀ i, α i) := by
  ext outcome
  simp only [pi_apply, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  exact ENNReal.prod_inv_distrib (by intro i hi j hj hij; right; simp)

/-- Applying a separate function to each coordinate preserves the product structure. -/
theorem pi_map [∀ i, Finite (β i)] (p : ∀ i, PMF (α i)) (f : ∀ i, α i → β i) :
    pi (fun i => (p i).map (f i)) = (pi p).map (fun outcome i => f i (outcome i)) := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  let (i : ι) := Fintype.ofFinite (β i)
  ext result
  simp only [pi_apply, PMF.map_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases h : result = fun i => f i (outcome i)
  · subst result
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, result i ≠ f i (outcome i) := by
      simpa only [funext_iff, not_forall] using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Independent conditional samples can be drawn after the complete tuple of their inputs. -/
theorem pi_bind [∀ i, Finite (β i)] (p : ∀ i, PMF (α i))
    (kernel : ∀ i, α i → PMF (β i)) :
    pi (fun i => (p i).bind (kernel i)) =
      (pi p).bind (fun outcome => pi (fun i => kernel i (outcome i))) := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  let (i : ι) := Fintype.ofFinite (β i)
  ext result
  simp only [pi_apply, PMF.bind_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- Split an independent finite sequence into its first draw and its remaining draws. -/
theorem pi_fin_succ {γ : Type*} [Finite γ] (count : ℕ) (p : PMF γ) :
    pi (fun _ : Fin (count + 1) => p) =
      p.bind (fun first => (pi (fun _ : Fin count => p)).map (Fin.cons first)) := by
  let e := Fin.consEquiv (fun _ : Fin (count + 1) => γ)
  calc
    _ = (p.bind (fun first => (pi (fun _ : Fin count => p)).map (first, ·))).map e := by
      ext outcome
      rw [map_equiv_apply]
      dsimp only [e, Fin.consEquiv]
      simp only [Equiv.coe_fn_symm_mk, PMF.map, Function.comp_def]
      rw [bind_pair_apply]
      exact Fin.prod_univ_succ (fun i => p (outcome i))
    _ = _ := by
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Fin.consEquiv]

/-- Independent pairs can be sampled by drawing their first components, then drawing each
second component conditionally and independently. -/
theorem pi_bind_pair [∀ i, Finite (β i)] (p : ∀ i, PMF (α i))
    (kernel : ∀ i, α i → PMF (β i)) :
    (pi (fun i => (p i).bind (fun a => (kernel i a).map (a, ·)))).map
        (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2)) =
      (pi p).bind (fun outcome => (pi (fun i => kernel i (outcome i))).map (outcome, ·)) := by
  rw [pi_bind, PMF.map_bind]
  congr 1
  funext outcome
  rw [pi_map, PMF.map_comp]
  rfl

/-- A tuple of independent joint samples can be drawn by first drawing all observations and
then drawing the hidden coordinates independently from their conditional distributions. -/
theorem pi_joint_eq_bind_conditionalSnd [∀ i, Finite (β i)]
    (joint : ∀ i, PMF (α i × β i)) :
    (pi joint).map (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2)) =
      (pi (fun i => (joint i).map Prod.fst)).bind (fun observed =>
        (pi (fun i => conditionalSnd (joint i) (observed i))).map (observed, ·)) := by
  simpa only [bind_conditionalSnd] using
    pi_bind_pair (fun i => (joint i).map Prod.fst) (fun i => conditionalSnd (joint i))

/-- Conditioning independent joint samples on a possible observation tuple preserves independence
of their hidden coordinates. -/
theorem conditionalSnd_pi_joint [∀ i, Finite (β i)]
    (joint : ∀ i, PMF (α i × β i)) (observed : ∀ i, α i)
    (hobserved : observed ∈ (pi (fun i => (joint i).map Prod.fst)).support) :
    conditionalSnd ((pi joint).map
      (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2))) observed =
        pi (fun i => conditionalSnd (joint i) (observed i)) := by
  rw [pi_joint_eq_bind_conditionalSnd, conditionalSnd_bind_pair _ _ _ hobserved]

end Cslib.Probability.PMF
