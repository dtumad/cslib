/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Tactic.PolyTime
public import Mathlib.Data.Nat.Find

/-!
# Polynomial-time bounded search

`Nat.findGreatest` is polynomial-time for an efficient unary bound and a certified predicate.
The implementation reuses enumeration and list search; predicates may capture the original
input. The usual Mathlib specification of `Nat.findGreatest` remains available to clients.
-/

@[expose] public section

namespace Cslib.Probability

private theorem findGreatest_eq_findD (predicate : ℕ → Prop) [DecidablePred predicate] (bound : ℕ) :
    Nat.findGreatest predicate bound =
      (((List.range (bound + 1)).reverse).find? (fun i => decide (predicate i))).getD 0 := by
  induction bound with
  | zero => by_cases h : predicate 0 <;> simp [h]
  | succ bound ih =>
    rw [Nat.findGreatest_succ, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons]
    split_ifs <;> simp_all

/-- Search every index up to the supplied unary bound, returning the greatest match or zero. -/
theorem IsPolyTime.findGreatest {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    {predicate : α → ℕ → Prop} [∀ a, DecidablePred (predicate a)]
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hpredicate : IsPolyTime (pairEncoding input unaryEncoding)
      (fun a => [decide (predicate a.1 a.2)])) :
    IsPolyTime input (fun a => unaryEncoding (Nat.findGreatest (predicate a) (bound a))) := by
  simp only [findGreatest_eq_findD]
  exact (hbound.unary_add (g := fun _ => 1) (isPolyTime_const input [true])).range.list_reverse
    |>.list_findD_with (isPolyTime_input input) hpredicate (isPolyTime_const input [])

@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeFindGreatest : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PolyTime.applyUnaryHead #[(``Nat.findGreatest, ``IsPolyTime.findGreatest)]

end Cslib.Probability
