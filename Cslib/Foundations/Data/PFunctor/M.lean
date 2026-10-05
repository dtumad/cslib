/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import Mathlib.Data.PFunctor.Univariate.M
public import Cslib.Foundations.Data.PFunctor.Basic

/-!
# Destructors and corecursion for polynomial M-types

Injectivity, corecursion equations, and a bisimulation principle for corecursors.
Adapted from PolyFun's polynomial M-type API.
-/

@[expose] public section

universe u uA uB v w

namespace PFunctor

namespace M

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ### Injectivity of `dest` -/

/-- The destructor of a polynomial M-type is injective. -/
theorem dest_injective : Function.Injective (M.dest (F := P)) :=
  Function.LeftInverse.injective M.mk_dest

@[simp] theorem dest_inj {u v : M P} : M.dest u = M.dest v ↔ u = v :=
  dest_injective.eq_iff

/-! ### Corecursion -/

/-- Bisimulation principle specialized to two `corec`s built from the same
shape transformer. If at every reachable state the two seed transitions agree
on shapes and yield bisimilar children, the two `corec`s are equal. -/
theorem corec_eq_corec {α : Type v} {β : Type w} (g : α → P α) (h : β → P β)
    (R : α → β → Prop) (x₀ : α) (y₀ : β)
    (hR : R x₀ y₀)
    (step : ∀ x y, R x y → ∃ a f f',
      g x = .mk a f ∧ h y = .mk a (f') ∧ ∀ i, R (f i) (f' i)) :
    M.corec g x₀ = M.corec h y₀ := by
  let S : M P → M P → Prop :=
    fun u v => ∃ x y, R x y ∧ u = M.corec g x ∧ v = M.corec h y
  refine M.bisim S ?_ _ _ ⟨x₀, y₀, hR, rfl, rfl⟩
  rintro u v ⟨x, y, hxy, rfl, rfl⟩
  obtain ⟨a, f, f', hf, hf', hR'⟩ := step x y hxy
  refine ⟨a, M.corec g ∘ f, M.corec h ∘ f', ?_, ?_, ?_⟩
  · rw [dest_corec, hf]; rfl
  · rw [dest_corec, hf']; rfl
  · intro i; exact ⟨f i, f' i, hR' i, rfl, rfl⟩

/-- A coalgebra morphism commutes with corecursion. -/
theorem corec_comp {β : Type w} (g : α → P α) (h : β → P β) (f : α → β)
    (hf : ∀ x, h (f x) = P.map f (g x)) : M.corec h ∘ f = M.corec g :=
  M.corec_unique g _ (fun x => by rw [Function.comp_apply, M.dest_corec, hf, P.map_map])

/-- Corecursing from the destructor reconstructs the original tree. -/
@[simp] theorem corec_dest (u : M P) : M.corec M.dest u = u :=
  congrFun (M.corec_unique M.dest id (fun _ => rfl)).symm u

end M

end PFunctor
