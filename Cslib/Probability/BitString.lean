/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Vector.Basic

/-!
# Uniform binary strings

Uniform sampling from `Fin n → Bool`, represented as a list. The recursive equations connect
this finite uniform distribution to a program drawing one independent fair bit at a time.
-/

@[expose] public section

namespace Cslib.Probability

/-- The uniform distribution on binary words of exactly `n` bits. -/
noncomputable def uniformBits (n : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

@[simp] theorem uniformBits_zero : uniformBits 0 = PMF.pure [] := by
  simp [uniformBits, PMF.map, Function.comp_def]

/-- A uniform nonempty string consists of a fair first bit and an independent uniform tail. -/
theorem uniformBits_succ (n : ℕ) :
    uniformBits (n + 1) = (PMF.uniformOfFintype Bool).bind
      (fun bit => (uniformBits n).map (List.cons bit)) := by
  unfold uniformBits
  rw [← PMF.uniformOfFintype_map_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)),
    PMF.map_comp, PMF.uniformOfFintype_prod]
  simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.consEquiv]

/-- Concatenating independent uniform words gives a uniform word of the combined length. -/
theorem uniformBits_add (m n : ℕ) :
    uniformBits (m + n) = (uniformBits m).bind
      (fun left => (uniformBits n).map (left ++ ·)) := by
  induction m with
  | zero => simp [PMF.map, Function.comp_def]
  | succ m ih =>
    rw [Nat.succ_add, uniformBits_succ, ih, uniformBits_succ]
    simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, PMF.bind_bind, Function.comp_def]

/-- Appending one independent fair bit gives a uniform word one bit longer. -/
theorem uniformBits_snoc (n : ℕ) :
    uniformBits (n + 1) = (uniformBits n).bind
      (fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) := by
  rw [uniformBits_add n 1, uniformBits_succ 0]
  simp [PMF.map, Function.comp_def]

/-- Every sampled word has exactly the requested length. -/
theorem length_of_mem_support_uniformBits {n : ℕ} {word : List Bool}
    (h : word ∈ (uniformBits n).support) : word.length = n := by
  obtain ⟨bits, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp

/-- A length-preserving permutation sends a uniform word to a uniform word of the same length.
This is a distributional fact and makes no assumption about computing the inverse. -/
theorem uniformBits_map_of_bijective (f : List Bool → List Bool) (hf : Function.Bijective f)
    (hlen : ∀ word, (f word).length = word.length) (n : ℕ) :
    (uniformBits n).map f = uniformBits n := by
  let e : List.Vector Bool n ≃ List.Vector Bool n :=
    (Equiv.ofBijective f hf).subtypeEquiv (fun word => by simp [hlen])
  let bits : (Fin n → Bool) ≃ (Fin n → Bool) :=
    (Equiv.vectorEquivFin Bool n).symm.trans (e.trans (Equiv.vectorEquivFin Bool n))
  have hbits (word : Fin n → Bool) : List.ofFn (bits word) = f (List.ofFn word) := by
    change List.ofFn (List.Vector.get (e (List.Vector.ofFn word))) = _
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
    change f (List.Vector.ofFn word).toList = _
    rw [List.Vector.toList_ofFn]
  calc
    (uniformBits n).map f = ((PMF.uniformOfFintype (Fin n → Bool)).map bits).map List.ofFn := by
      simp only [uniformBits, PMF.map_comp]
      congr 1
      funext word
      exact (hbits word).symm
    _ = uniformBits n := by rw [PMF.uniformOfFintype_map_equiv]; rfl

end Cslib.Probability
