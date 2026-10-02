/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds on natural-valued functions

`PolynomiallyBounded f` supplies a bound `c * (n + 1) ^ d` for every `n`. It is a growth condition;
it does not assert that `f` is computable. The addition, multiplication and composition lemmas
are useful when accounting for sizes and running times. They are registered with `fun_prop`,
which proves bounds for polynomial expressions and compositions using local bound hypotheses.
-/

@[expose] public section

namespace Cslib

/-- A function is bounded at every input by a fixed multiple of a fixed power of `n + 1`. -/
@[fun_prop] def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d

namespace PolynomiallyBounded

@[fun_prop] theorem const (c : ℕ) : PolynomiallyBounded (fun _ => c) := ⟨c, 0, by simp⟩

@[fun_prop] theorem id : PolynomiallyBounded (fun n => n) := ⟨1, 1, by simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PolynomiallyBounded g) (h : ∀ n, f n ≤ g n) :
    PolynomiallyBounded f := by
  obtain ⟨c, d, hg⟩ := hg
  exact ⟨c, d, fun n => (h n).trans (hg n)⟩

@[fun_prop] theorem add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨c, d, hf⟩ := hf
  obtain ⟨c', d', hg⟩ := hg
  refine ⟨c + c', d + d', fun n => ?_⟩
  calc
    f n + g n ≤ c * (n + 1) ^ d + c' * (n + 1) ^ d' := Nat.add_le_add (hf n) (hg n)
    _ ≤ c * (n + 1) ^ (d + d') + c' * (n + 1) ^ (d + d') := by gcongr <;> omega
    _ = (c + c') * (n + 1) ^ (d + d') := by ring

@[fun_prop] theorem mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨c, d, hf⟩ := hf
  obtain ⟨c', d', hg⟩ := hg
  refine ⟨c * c', d + d', fun n => ?_⟩
  calc
    f n * g n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') := Nat.mul_le_mul (hf n) (hg n)
    _ = (c * c') * (n + 1) ^ (d + d') := by rw [pow_add]; ring

@[fun_prop] theorem pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (d : ℕ) :
    PolynomiallyBounded (fun n => f n ^ d) := by
  obtain ⟨c, e, hf⟩ := hf
  refine ⟨c ^ d, e * d, fun n => ?_⟩
  calc
    f n ^ d ≤ (c * (n + 1) ^ e) ^ d := Nat.pow_le_pow_left (hf n) d
    _ = c ^ d * (n + 1) ^ (e * d) := by rw [mul_pow, pow_mul]

@[fun_prop] theorem comp {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨c, d, hf⟩ := hf
  obtain ⟨c', d', hg⟩ := hg
  refine ⟨c * (c' + 1) ^ d, d' * d, fun n => ?_⟩
  have hsize : g n + 1 ≤ (c' + 1) * (n + 1) ^ d' := by
    have hp : 1 ≤ (n + 1) ^ d' := Nat.one_le_pow _ _ (by omega)
    calc
      g n + 1 ≤ c' * (n + 1) ^ d' + (n + 1) ^ d' := Nat.add_le_add (hg n) hp
      _ = (c' + 1) * (n + 1) ^ d' := by ring
  calc
    f (g n) ≤ c * (g n + 1) ^ d := hf (g n)
    _ ≤ c * ((c' + 1) * (n + 1) ^ d') ^ d := Nat.mul_le_mul_left c
      (Nat.pow_le_pow_left hsize d)
    _ = c * (c' + 1) ^ d * (n + 1) ^ (d' * d) := by rw [mul_pow, pow_mul, mul_assoc]

end PolynomiallyBounded

end Cslib
