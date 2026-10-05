/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Resumption.Measure.Repeat
public import Mathlib.Probability.UniformOn

/-!
# Uniform finite sampling by rejection

A proposal in `Fin m` is accepted when it is below `n`. The theorem allows any `m ≥ n`;
choosing a power of two gives a dyadic proposal. Each operation here is one whole proposal,
so a machine implementation must charge for producing its bits.
-/

@[expose] public section

namespace PFunctor.Resumption

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Reject proposals outside the requested range. -/
def acceptFin (n : ℕ) {m : ℕ} (proposal : Fin m) : Option (Fin n) :=
  if h : proposal.val < n then some ⟨proposal.val, h⟩ else none

/-- Repeated uniform proposals, with an explicit infinite branch for repeated rejection. -/
def uniformFin (n m : ℕ) : Resumption ⟨Unit, fun _ => Fin m⟩ (Fin n) :=
  repeatUntil () (acceptFin n)

theorem setOf_acceptFin_eq_some {n m : ℕ} (h : n ≤ m) (a : Fin n) :
    {b : Fin m | acceptFin n b = some a} = {a.castLE h} := by
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, acceptFin]
  split_ifs with hb
  · simp only [Option.some.injEq, Fin.ext_iff, Fin.val_castLE]
  · simp only [false_iff]
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_castLE] at this
    exact hb (this ▸ a.isLt)

/-- The rejection probability is the fraction of proposals outside the range. -/
theorem uniformOn_acceptFin_none {n m : ℕ} [NeZero m] (h : n ≤ m) :
    uniformOn (Set.univ : Set (Fin m)) {b | acceptFin n b = none} =
      1 - (n : ℝ≥0∞) / m := by
  have hset : {b : Fin m | b.val < n} = Fin.castLE h '' Set.univ := by
    ext b
    constructor
    · intro hb
      exact ⟨⟨b.val, hb⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨a, _, rfl⟩
      exact a.isLt
  have hcompl : {b : Fin m | acceptFin n b = none} = {b : Fin m | b.val < n}ᶜ := by
    ext b
    simp [acceptFin]
  rw [hcompl, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ,
    uniformOn_univ, hset, Measure.count_injective_image (Fin.castLE_injective _)]
  simp

/-- Exact uniform output, with no conditioning on termination. -/
theorem returnedMeasure_uniformFin {n m : ℕ} [NeZero m] (h : n ≤ m) :
    returnedMeasure (P := ⟨Unit, fun _ => Fin m⟩) (fun _ => uniformOn Set.univ)
      (uniformFin n m) = uniformOn Set.univ := by
  apply Measure.ext_of_singleton
  intro a
  rw [uniformFin, returnedMeasure_repeatUntil_apply (P := ⟨Unit, fun _ => Fin m⟩)
    _ _ _ _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  rw [uniformOn_acceptFin_none h, setOf_acceptFin_eq_some h, uniformOn_univ, uniformOn_univ]
  simp only [Measure.count_singleton, Fintype.card_fin, one_div]
  have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hle : (n : ℝ≥0∞) / m ≤ 1 := by
    exact (ENNReal.div_le_iff hm (by simp)).mpr (by simpa using h)
  rw [ENNReal.sub_sub_cancel (by simp) hle,
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl hm)]
  rw [div_eq_mul_inv, mul_comm (m : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hm
    (by simp), mul_one]

/-- A finite cutoff exposes its failure probability instead of silently renormalizing. -/
theorem denote_truncate_uniformFin_none {n m : ℕ} [NeZero m] (h : n ≤ m) (attempts : ℕ) :
    FreeM.denote (P := ⟨Unit, fun _ => Fin m⟩) (fun _ => uniformOn Set.univ)
      (truncate attempts (uniformFin n m)) {none} = (1 - (n : ℝ≥0∞) / m) ^ attempts := by
  rw [uniformFin, denote_truncate_repeatUntil_none (P := ⟨Unit, fun _ => Fin m⟩),
    uniformOn_acceptFin_none h]

/-- The exact expected number of proposals. -/
theorem expectedQueries_uniformFin {n m : ℕ} [NeZero m] (h : n ≤ m) :
    expectedQueries (P := ⟨Unit, fun _ => Fin m⟩) (fun _ => uniformOn Set.univ)
      (uniformFin n m) = (m : ℝ≥0∞) / n := by
  rw [uniformFin, expectedQueries_repeatUntil (P := ⟨Unit, fun _ => Fin m⟩),
    uniformOn_acceptFin_none h]
  have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hle : (n : ℝ≥0∞) / m ≤ 1 :=
    (ENNReal.div_le_iff hm (by simp)).mpr (by simpa using h)
  rw [ENNReal.sub_sub_cancel (by simp) hle,
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl hm)]

end PFunctor.Resumption
