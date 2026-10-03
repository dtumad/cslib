/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.UniversalHash
public import Cslib.Probability.Uniform
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul

/-!
# Binary linear hashing

A uniformly random Boolean matrix defines a two-universal family: hash a bitstring by taking
its inner product with each row. For distinct inputs the difference of their hashes is uniform,
so they collide with probability exactly `2⁻ᵐ`, where `m` is the number of rows.

The construction uses the existing `BitString` representation and Mathlib's Boolean ring.
Its word implementation and polynomial-time certificate live in
`Cslib.Computability.Probabilistic.LinearHash`.

## References

* Iftach Haitner and Salil Vadhan, *The Many Entropies in One-Way Functions*, 2017,
  Section 2.4.1, the Boolean-matrix example following Definition 4.
  [Write-up](https://eccc.weizmann.ac.il/report/2017/084/download/).
* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 3.3, Lemma 1.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  Our matrix family instantiates the general leftover hash lemma; it uses more seed bits than
  the field-multiplication family in that write-up, while still having polynomial seed length.
-/

@[expose] public section

namespace Cslib.Probability.LinearHash

open Cslib.Probability.PMF

/-- Hash an `n`-bit input to `m` bits using the `m` rows of a Boolean matrix. -/
def hash {n m : ℕ} (rows : Fin m → BitString n) (input : BitString n) : BitString m :=
  fun i => rows i ⬝ᵥ input

/-- Hashing any nonzero input by a uniform matrix gives a uniform output. -/
theorem uniform_hash_nonzero {n m : ℕ} (input : BitString n) (hinput : input ≠ 0) :
    (PMF.uniformOfFintype (Fin m → BitString n)).map (fun rows => hash rows input) =
      PMF.uniformOfFintype (BitString m) := by
  let transform : (Fin m → BitString n) →+ BitString m := {
    toFun := fun rows => hash rows input
    map_zero' := by ext i; simp [hash]
    map_add' := by intros; ext i; simp [hash, add_dotProduct] }
  apply uniformOfFintype_map_addHom transform
  obtain ⟨j, hj⟩ : ∃ j, input j ≠ false := by
    by_contra! h
    exact hinput (funext h)
  have hj : input j = true := by cases h : input j <;> simp_all
  intro output
  refine ⟨fun i => Pi.single j (output i), ?_⟩
  ext i
  simp [transform, hash, single_dotProduct, hj, Bool.mul_eq_and]

/-- The difference of the hashes of distinct inputs is uniform. -/
theorem uniform_hash_sub {n m : ℕ} (x y : BitString n) (hxy : x ≠ y) :
    (PMF.uniformOfFintype (Fin m → BitString n)).map
        (fun rows => hash rows x - hash rows y) = PMF.uniformOfFintype (BitString m) := by
  have hsub (rows : Fin m → BitString n) : hash rows x - hash rows y = hash rows (x - y) := by
    ext i
    exact (dotProduct_sub _ _ _).symm
  simp only [hsub]
  exact uniform_hash_nonzero (x - y) (sub_ne_zero.mpr hxy)

/-- Uniform Boolean matrices are a two-universal hash family, including zero-width outputs. -/
theorem isTwoUniversal (n m : ℕ) :
    IsTwoUniversal (PMF.uniformOfFintype (Fin m → BitString n)) hash := by
  intro x y hxy
  have h := congrArg (fun p : PMF (BitString m) => (p 0).toReal) (uniform_hash_sub x y hxy)
  rw [map_apply_toReal] at h
  simpa only [eq_comm (a := (0 : BitString m)), sub_eq_zero, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast] using h.le

/-- Any initial block of a uniform matrix is itself uniform. Unused rows may remain public. -/
theorem uniform_prefix {n m count : ℕ} (h : m ≤ count) :
    (PMF.uniformOfFintype (Fin count → BitString n)).map
        (fun rows => rows ∘ Fin.castLE h) =
      PMF.uniformOfFintype (Fin m → BitString n) := by
  let restrict : (Fin count → BitString n) →+ (Fin m → BitString n) := {
    toFun := fun rows => rows ∘ Fin.castLE h
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact uniformOfFintype_map_addHom restrict
    (Fin.castLE_injective h).surjective_comp_right

/-- Prefixes of one public matrix give universal hashes at every shorter output length. -/
theorem isTwoUniversal_prefix {n m count : ℕ} (h : m ≤ count) :
    IsTwoUniversal (PMF.uniformOfFintype (Fin count → BitString n))
      (fun rows => hash (rows ∘ Fin.castLE h)) := by
  apply IsTwoUniversal.precompose_seed
  rw [uniform_prefix]
  exact isTwoUniversal n m

end Cslib.Probability.LinearHash
