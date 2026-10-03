/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Basic
public import Cslib.Probability.Product
public import Mathlib.Data.List.OfFn

/-!
# Bounded repetition of probabilistic programs

`OracleComp.replicate count program` runs a program `count` times, collecting its results in
execution order. For a closed program driven by a uniform finite seed, its joint distribution
is evaluation at independently uniform seeds. The result type need not be finite.

This is a semantic combinator. Its uniform PPT certificate is supplied separately in
`Cslib.Computability.Probabilistic.Repeat`.
-/

@[expose] public section

namespace Cslib

universe u v

namespace OracleComp

variable {Query : Type u} {Response : Query → Type u} {α : Type v}

/-- Run a program a bounded number of times, collecting results in execution order. -/
def replicate : ℕ → OracleComp Query Response α → OracleComp Query Response (List α)
  | 0, _ => pure []
  | count + 1, program => do
    let first ← program
    let rest ← replicate count program
    return first :: rest

@[simp] theorem replicate_zero (program : OracleComp Query Response α) :
    replicate 0 program = pure [] := rfl

theorem replicate_succ (count : ℕ) (program : OracleComp Query Response α) :
    replicate (count + 1) program = program >>= fun first =>
      List.cons first <$> replicate count program := by
  simp only [replicate, bind_pure_comp]

/-- Splitting a repetition budget concatenates the two sampled lists in execution order. -/
theorem replicate_add (first second : ℕ) (program : OracleComp Query Response α) :
    replicate (first + second) program = (do
      let front ← replicate first program
      let back ← replicate second program
      return front ++ back) := by
  induction first with
  | zero => simp
  | succ first ih =>
    simp only [Nat.succ_add, replicate_succ, ih, bind_assoc, bind_map_left, map_bind,
      map_pure, List.cons_append]

/-- Split off the last draw of a repeated program. -/
theorem replicate_snoc (count : ℕ) (program : OracleComp Query Response α) :
    replicate (count + 1) program = (do
      let front ← replicate count program
      (fun last => front ++ [last]) <$> program) := by
  simpa only [replicate, bind_pure, bind_pure_comp, map_pure, Functor.map_map, Function.comp_def]
    using replicate_add count 1 program

/-- Applying a deterministic function to each draw commutes with collecting the draws. -/
theorem replicate_map {β : Type v} (count : ℕ) (program : OracleComp Query Response α)
    (f : α → β) :
    replicate count (f <$> program) = List.map f <$> replicate count program := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [replicate_succ, ih, bind_map_left, map_bind, Functor.map_map, List.map_cons]

/-- Count the true results of a bounded number of runs of a Boolean program. -/
def countTrue (count : ℕ) (program : OracleComp Query Response Bool) :
    OracleComp Query Response ℕ :=
  List.count true <$> replicate count program

/-- Test whether an empirical acceptance rate is below a rational threshold. Cross-products
implement the comparison using natural arithmetic. Accuracy theorems require positive count
and denominator; the program itself is defined for all parameters. -/
def testProbabilityLT (count numerator denominator : ℕ)
    (program : OracleComp Query Response Bool) : OracleComp Query Response Bool :=
  (fun successes => decide (successes * denominator < count * numerator)) <$>
    countTrue count program

end OracleComp

namespace ProbComp

variable {α Seed : Type*} [Fintype Seed] [Nonempty Seed]

/-- Every supported repeated output has the prescribed length and supported elements. -/
theorem mem_support_replicate_iff (count : ℕ) (program : ProbComp α)
    (values : List α) :
    values ∈ (eval (OracleComp.replicate count program)).support ↔
      values.length = count ∧ ∀ value ∈ values, value ∈ (eval program).support := by
  induction count generalizing values with
  | zero => cases values <;> simp
  | succ count ih =>
    cases values with
    | nil =>
      simp [OracleComp.replicate_succ]
    | cons value rest =>
      simp [OracleComp.replicate_succ, ih, and_assoc, and_left_comm]

/-- Repeated closed runs have the independent product law, for any finite output distribution. -/
theorem eval_replicate [Finite α] (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicate count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map List.ofFn := by
  induction count with
  | zero =>
    rw [OracleComp.replicate_zero, eval_pure]
    simp only [show (List.ofFn : (Fin 0 → α) → List α) = fun _ => [] by
      funext f; exact List.ofFn_zero, Function.const_def]
    exact (PMF.map_const _ []).symm
  | succ count ih =>
    rw [OracleComp.replicate_succ, eval_bind]
    simp [eval_map, ih, Probability.PMF.pi_fin_succ, PMF.map_bind, PMF.map_comp,
      Function.comp_def, List.ofFn_succ]

/-- The probability of a particular sequence of repeated outputs is the product of its masses. -/
theorem eval_replicate_apply_ofFn [Finite α] {count : ℕ}
    (program : ProbComp α) (outcomes : Fin count → α) :
    eval (OracleComp.replicate count program) (List.ofFn outcomes) =
      ∏ i, eval program (outcomes i) := by
  classical
  rw [eval_replicate]
  simp only [PMF.map_apply, List.ofFn_inj, tsum_ite_eq', Probability.PMF.pi_apply]

private theorem count_true_ofFn {count : ℕ} (bits : Fin count → Bool) :
    (List.ofFn bits).count true = ∑ i, (bits i).toNat := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    cases bits 0 <;> simp [Nat.add_comm]

/-- Counting successful repeated trials is the sum of independent Boolean indicators. -/
theorem eval_countTrue (count : ℕ) (program : ProbComp Bool) :
    eval (OracleComp.countTrue count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map
        (fun bits => ∑ i, (bits i).toNat) := by
  rw [OracleComp.countTrue, eval_map, eval_replicate, PMF.map_comp]
  congr 1
  funext bits
  exact count_true_ofFn bits

/-- Every execution returns a success count between zero and the number of trials. -/
theorem countTrue_le (count : ℕ) (program : ProbComp Bool) {successes : ℕ}
    (h : successes ∈ (eval (OracleComp.countTrue count program)).support) : successes ≤ count := by
  rw [eval_countTrue, PMF.mem_support_map_iff] at h
  obtain ⟨bits, _, rfl⟩ := h
  calc
    _ ≤ ∑ _ : Fin count, 1 := Finset.sum_le_sum (fun i _ => by cases bits i <;> decide)
    _ = count := by simp

/-- Repeated runs of a seeded closed program use independent seeds, including at count zero. -/
theorem eval_replicate_of_uniform (count : ℕ) (program : ProbComp α) (evaluate : Seed → α)
    (hlaw : eval program = (PMF.uniformOfFintype Seed).map evaluate) :
    eval (OracleComp.replicate count program) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => List.ofFn (fun i => evaluate (seeds i))) := by
  induction count with
  | zero =>
    rw [OracleComp.replicate_zero, eval_pure]
    simp only [List.ofFn_zero, Function.const_def, PMF.map_const]
  | succ count ih =>
    rw [OracleComp.replicate_succ, eval_bind, hlaw]
    simp only [eval_map, ih]
    rw [← Probability.PMF.uniformOfFintype_map_equiv
      (Fin.consEquiv (fun _ : Fin (count + 1) => Seed)), PMF.map_comp,
      Probability.PMF.uniformOfFintype_prod]
    simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, Fin.consEquiv,
      List.ofFn_succ]

end ProbComp

end Cslib
