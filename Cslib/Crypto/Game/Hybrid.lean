/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Game
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic

/-!
# Polynomially many semantic game hops

The concrete hybrid inequality adds the advantages of adjacent games. The asymptotic theorem
requires a single negligible bound that works for every hop at each security parameter. Merely
assuming negligibility separately for each fixed hop does not suffice when the number of hops
grows with the parameter. The common bound may depend on the distinguisher.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.3.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped BigOperators

/-- Polynomial factors preserve a nonnegative negligible bound. -/
theorem negligible_polynomial_mul {ε : ℕ → ℝ} {p : ℕ → ℕ}
    (hε : Negligible ε) (hε₀ : ∀ n, 0 ≤ ε n) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ) * ε n) := by
  obtain ⟨c, d, hp⟩ := hp
  have hbound : Negligible (fun n => (c : ℝ) * ((n : ℝ) + 1) ^ d * ε n) := by
    convert hε.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d) using 1
    ext n
    simp
  apply negligible_of_le hbound (fun n => mul_nonneg (Nat.cast_nonneg _) (hε₀ n))
  intro n
  apply mul_le_mul_of_nonneg_right _ (hε₀ n)
  exact_mod_cast hp n

open Filter Topology in
/-- Negligible decay survives reindexing when the new parameter tends to infinity and the old
parameter is polynomially bounded in it. The reindexing function need not be computable. -/
theorem Negligible.comp_of_polynomial_bound {ε : ℕ → ℝ} {index bound : ℕ → ℕ}
    (hε : Negligible ε) (hindex : Tendsto index atTop atTop)
    (hbound : PolynomiallyBounded bound) (hle : ∀ᶠ n in atTop, n ≤ bound (index n)) :
    Negligible (fun n => ε (index n)) := by
  have habs : Negligible (fun n => |ε n|) := hε.trans_abs_le (fun _ => by simp)
  intro degree
  have hlimit := (negligible_polynomial_mul habs (fun _ => abs_nonneg _)
    (hbound.pow degree) 0).comp hindex
  simp only [pow_zero, one_mul, Nat.cast_pow, Function.comp_def] at hlimit
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlimit
  filter_upwards [hle] with n hn
  simp only [Function.comp_def, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  gcongr

open Filter in
/-- Negligible success is eventually smaller than the reciprocal of any positive
polynomially bounded loss. -/
theorem Negligible.eventually_le_inv_polynomial {ε : ℕ → ℝ} (hε : Negligible ε)
    (hε₀ : ∀ n, 0 ≤ ε n) {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (hpos : ∀ n, 0 < p n) :
    ∀ᶠ n in atTop, ε n ≤ 1 / (p n : ℝ) := by
  have h := negligible_polynomial_mul hε hε₀ hp 0
  simp only [pow_zero, one_mul] at h
  filter_upwards [h.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn
  apply (le_div_iff₀ (by exact_mod_cast hpos n)).mpr
  simpa only [mul_comm] using hn

namespace Game

/-- A uniformly selected experiment accepts with the average of its acceptance probabilities. -/
theorem winProbability_uniform {α : Type*} [Fintype α] [Nonempty α] (games : α → Game) :
    winProbability ((PMF.uniformOfFintype α).bind games) =
      (∑ a, winProbability (games a)) / Fintype.card α := by
  rw [winProbability, Probability.PMF.bind_apply_toReal]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    winProbability, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Randomly choosing an adjacent hybrid telescopes signed gaps.
Unused indices run the same rejecting game on both sides. This gives a single uniform reduction
with loss `capacity`, without selecting a length-dependent best hop. -/
theorem winProbability_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    winProbability (games 0) - winProbability (games hops) = (capacity : ℝ) *
      (winProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false)) - winProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false))) := by
  have hsum : (∑ i : Fin capacity, if i.val < hops then
      winProbability (games i.val) - winProbability (games (i.val + 1)) else 0) =
      winProbability (games 0) - winProbability (games hops) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < hops then
      winProbability (games i) - winProbability (games (i + 1)) else 0)]
    calc
      (∑ i ∈ Finset.range capacity, if i < hops then
          winProbability (games i) - winProbability (games (i + 1)) else 0) =
          ∑ i ∈ Finset.range hops, if i < hops then
            winProbability (games i) - winProbability (games (i + 1)) else 0 :=
        (Finset.sum_subset (Finset.range_mono hle) (by intro i _ hi; simp_all)).symm
      _ = ∑ i ∈ Finset.range hops,
          (winProbability (games i) - winProbability (games (i + 1))) :=
        Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi))
      _ = _ := Finset.sum_range_sub' (fun i => winProbability (games i)) hops
  rw [winProbability_uniform, winProbability_uniform]
  simp only [Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib]
  have hdiff (i : Fin capacity) :
      winProbability (if i.val < hops then games i.val else PMF.pure false) -
        winProbability (if i.val < hops then games (i.val + 1) else PMF.pure false) =
      if i.val < hops then winProbability (games i.val) - winProbability (games (i.val + 1))
        else 0 := by split_ifs <;> simp
  simp only [hdiff, hsum]
  have hcapacity : (capacity : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne capacity
  field_simp

/-- Averaging adjacent hybrids also preserves absolute distinguishing advantage, with the
sampling-range loss and no length-dependent choice of the best hop. -/
theorem advantage_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    advantage (games 0) (games hops) = (capacity : ℝ) *
      advantage
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false))
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false)) := by
  rw [advantage, advantage, winProbability_hybrid_average games hops capacity hle, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg capacity : (0 : ℝ) ≤ capacity)]

/-- The advantage between the endpoints is at most the sum of all adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → Game) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) := by
  induction hops with
  | zero => simp
  | succ hops ih =>
    calc
      advantage (games 0) (games (hops + 1)) ≤
          advantage (games 0) (games hops) + advantage (games hops) (games (hops + 1)) :=
        advantage_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1))) +
          advantage (games hops) (games (hops + 1)) := add_le_add ih le_rfl
      _ = _ := (Finset.sum_range_succ _ _).symm

/-- A common bound on each hop gives the usual linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → Game) (hops : ℕ) (ε : ℝ)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ (hops : ℝ) * ε := by
  calc
    advantage (games 0) (games hops) ≤
        ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) :=
      advantage_hybrid_le_sum games hops
    _ ≤ ∑ _i ∈ Finset.range hops, ε := Finset.sum_le_sum fun i hi =>
      hstep i (Finset.mem_range.mp hi)
    _ = _ := by simp

/-- Polynomially many hops with a common negligible bound have negligible total advantage. -/
theorem negligible_hybrid {games : ℕ → ℕ → Game} {hops : ℕ → ℕ} {ε : ℕ → ℝ}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε) (hε₀ : ∀ n, 0 ≤ ε n)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  negligible_of_le (negligible_polynomial_mul hε hε₀ hpoly)
    (fun _ => advantage_nonneg _ _) (fun n => advantage_hybrid_le _ _ _ (hstep n))

/-- A hybrid argument with a common hop bound for each admissible adversary. -/
theorem Secure.hybrid {Adversary : Type*} {games : Adversary → ℕ → ℕ → Game}
    {Admissible : Adversary → Prop} {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary, Admissible adversary →
      ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧ ∀ n i, i < hops n →
        advantage (games adversary n i) (games adversary n (i + 1)) ≤ ε n) :
    Secure (fun adversary n => games adversary n 0)
      (fun adversary n => games adversary n (hops n)) Admissible := by
  intro adversary ha
  obtain ⟨ε, hε, hε₀, hstep⟩ := hstep adversary ha
  exact negligible_hybrid hpoly hε hε₀ hstep

/-- A reduction may lose a polynomial factor and incur a negligible error. The bounds may
depend on the whole adversary, while the reduced adversary remains uniform. -/
theorem Secure.of_reduction_with_loss {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary →
      ∃ (loss : ℕ → ℕ) (error : ℕ → ℝ), PolynomiallyBounded loss ∧ Negligible error ∧ ∀ n,
        advantage (targetReal adversary n) (targetIdeal adversary n) ≤
          loss n * advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n) +
            error n) : Secure targetReal targetIdeal TargetAdmissible := by
  intro adversary ha
  obtain ⟨loss, error, hloss, herror, hbound⟩ := hbound adversary ha
  exact negligible_of_le
    ((negligible_polynomial_mul (h _ (hadmissible adversary ha))
      (fun _ => advantage_nonneg _ _) hloss).add herror)
    (fun _ => advantage_nonneg _ _) hbound

end Game

end Cslib.Crypto
