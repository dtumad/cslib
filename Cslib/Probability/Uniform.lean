/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Fintype.Pi

/-!
# Uniform sampling and subset sums

A surjective additive homomorphism between finite groups preserves the uniform distribution.
Consequently, the sum over any nonempty subset of independently uniform group elements is
uniform, and two distinct nonempty subsets give independent uniform sums.
Replacing any one summand by a fresh uniform value also makes the complete sum uniform.

For bitstrings, addition is pointwise XOR. These subset sums are the pairwise independent
masks used by the Goldreich–Levin decoder. The joint-distribution theorem does not assert
mutual independence of three or more subset sums.
-/

@[expose] public section

namespace Cslib.Probability.PMF

/-- A finite sum is uniform if any one summand is fresh uniform, regardless of the others. -/
theorem uniformOfFintype_map_sum_update {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G] (values : ι → G) (i : ι) :
    (PMF.uniformOfFintype G).map (fun value => ∑ j, Function.update values i value j) =
      PMF.uniformOfFintype G := by
  simp only [Finset.sum_update_of_mem (Finset.mem_univ i)]
  exact uniformOfFintype_map_equiv (Equiv.addRight _)

/-- A surjective additive homomorphism of finite groups sends uniform inputs to uniform outputs. -/
theorem uniformOfFintype_map_addHom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype G).map f = PMF.uniformOfFintype H := by
  classical
  let section_ : H → G := fun b => (hf b).choose
  have hsection (b : H) : f (section_ b) = b := (hf b).choose_spec
  let Kernel := {a : G // f a = 0}
  have : Nonempty Kernel := ⟨⟨0, f.map_zero⟩⟩
  let e : G ≃ H × Kernel := {
    toFun := fun a => (f a, ⟨a - section_ (f a), by simp [hsection]⟩)
    invFun := fun p => p.2.1 + section_ p.1
    left_inv := fun a => by simp
    right_inv := fun p => by
      rcases p with ⟨b, a, ha⟩
      apply Prod.ext
      · simp [hsection, ha]
      · apply Subtype.ext
        simp [hsection, ha] }
  calc
    (PMF.uniformOfFintype G).map f =
        ((PMF.uniformOfFintype G).map e).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (H × Kernel)).map Prod.fst := by
      rw [uniformOfFintype_map_equiv]
    _ = PMF.uniformOfFintype H := by
      rw [uniformOfFintype_prod]
      simp [PMF.map, Function.comp_def]

private theorem sumPair_surjective_of_mem_notMem {ι G : Type*}
    [AddCommGroup G] (s t : Finset ι) {i : ι}
    (hi : i ∈ s) (hit : i ∉ t) (ht : t.Nonempty) :
    Function.Surjective (fun masks : ι → G => (∑ j ∈ s, masks j, ∑ j ∈ t, masks j)) := by
  classical
  obtain ⟨j, hj⟩ := ht
  rintro ⟨a, b⟩
  refine ⟨Pi.single i (a - if j ∈ s then b else 0) + Pi.single j b, ?_⟩
  ext <;> simp [Finset.sum_add_distrib, Finset.sum_pi_single', hi, hit, hj]

private theorem sumPair_surjective {ι G : Type*}
    [AddCommGroup G] (s t : Finset ι)
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ≠ t) :
    Function.Surjective (fun masks : ι → G => (∑ j ∈ s, masks j, ∑ j ∈ t, masks j)) := by
  classical
  by_cases hsub : s ⊆ t
  · have hex : ∃ i ∈ t, i ∉ s := by
      by_contra h
      apply hst
      apply Finset.Subset.antisymm hsub
      simpa [Finset.subset_iff] using h
    obtain ⟨i, hit, his⟩ := hex
    intro pair
    obtain ⟨masks, h⟩ :=
      sumPair_surjective_of_mem_notMem (G := G) t s hit his hs (pair.2, pair.1)
    exact ⟨masks, Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)⟩
  · obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hsub
    exact sumPair_surjective_of_mem_notMem s t his hit ht

/-- A nonempty subset sum of independent uniform group elements is uniform. -/
theorem uniformOfFintype_map_sum {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G]
    (s : Finset ι) (hs : s.Nonempty) :
    (PMF.uniformOfFintype (ι → G)).map (fun masks => ∑ i ∈ s, masks i) =
      PMF.uniformOfFintype G := by
  classical
  let f : (ι → G) →+ G := {
    toFun := fun masks => ∑ i ∈ s, masks i
    map_zero' := by simp
    map_add' := by intros; simp [Finset.sum_add_distrib] }
  apply uniformOfFintype_map_addHom f
  obtain ⟨i, hi⟩ := hs
  intro a
  exact ⟨Pi.single i a, by simp [f, hi]⟩

/-- Distinct nonempty subset sums have the joint distribution of two independent uniform samples. -/
theorem uniformOfFintype_map_sum_pair {ι G : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype G] [AddCommGroup G]
    (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ≠ t) :
    (PMF.uniformOfFintype (ι → G)).map
        (fun masks => (∑ i ∈ s, masks i, ∑ i ∈ t, masks i)) =
      PMF.uniformOfFintype (G × G) := by
  let f : (ι → G) →+ G × G := {
    toFun := fun masks => (∑ i ∈ s, masks i, ∑ i ∈ t, masks i)
    map_zero' := by simp
    map_add' := by intros; simp [Finset.sum_add_distrib] }
  exact uniformOfFintype_map_addHom f (sumPair_surjective s t hs ht hst)

end Cslib.Probability.PMF
