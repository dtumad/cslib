/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.List
public import Cslib.Computability.PolynomialTime.Option
public import Mathlib.Data.List.OfFn

/-!
# Fixed finite tables and tuples

The finite domains here are fixed before the input. These certificates implement finite control
tables and arrays of a fixed number of tapes; they do not certify families of growing lookup tables.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type} {input : α → Word} {element : β ↪ Word} {n : ℕ}

/-- Assemble a fixed number of efficiently computed values. -/
theorem IsPolyTime.list_ofFn {values : α → Fin n → β}
    (hvalues : ∀ i, IsPolyTime input (fun a => element (values a i))) :
    IsPolyTime input (fun a => listEncoding element (List.ofFn (values a))) := by
  induction n with
  | zero => simpa using isPolyTime_const input []
  | succ n ih =>
    simpa only [List.ofFn_succ] using (hvalues 0).list_cons (ih (fun i => hvalues i.succ))

/-- An injective representation of a fixed-size tuple. -/
def tupleEncoding (n : ℕ) (element : β ↪ Word) : (Fin n → β) ↪ Word where
  toFun values := listEncoding element (List.ofFn values)
  inj' := fun _ _ h => List.ofFn_injective ((listEncoding element).injective h)

/-- A uniform increase in component size gives a linear increase in tuple size. -/
theorem length_tupleEncoding_le {values others : Fin n → β} {bound : ℕ}
    (h : ∀ i, (element (values i)).length ≤ (element (others i)).length + bound) :
    (tupleEncoding n element values).length ≤
      (tupleEncoding n element others).length + 2 * n * bound := by
  induction n with
  | zero => simp [tupleEncoding]
  | succ n ih =>
    have hhead := h 0
    have htail := ih (fun i => h i.succ)
    change (listEncoding element (List.ofFn values)).length ≤
      (listEncoding element (List.ofFn others)).length + _
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [listEncoding_cons, length_pairEncoding]
    change 2 * (element (values 0)).length +
      (tupleEncoding n element (fun i => values i.succ)).length + 1 ≤
      2 * (element (others 0)).length +
        (tupleEncoding n element (fun i => others i.succ)).length + 1 + _
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at *
    omega

/-- Construct a fixed-size tuple from its certified components. -/
theorem IsPolyTime.tuple {values : α → Fin n → β}
    (hvalues : ∀ i, IsPolyTime input (fun a => element (values a i))) :
    IsPolyTime input (fun a => tupleEncoding n element (values a)) := IsPolyTime.list_ofFn hvalues

/-- Access a fixed component, including its complete encoded value. -/
theorem IsPolyTime.tuple_apply {values : α → Fin n → β}
    (hvalues : IsPolyTime input (fun a => tupleEncoding n element (values a))) (i : Fin n) :
    IsPolyTime input (fun a => element (values a i)) := by
  cases isEmpty_or_nonempty β with
  | inl h =>
    convert isPolyTime_const input [] using 1
    funext a
    exact (h.false (values a i)).elim
  | inr h =>
    let fallback := Classical.choice h
    simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some] using
      hvalues.list_getD (count := fun _ => i.val)
        (isPolyTime_const input (unaryEncoding i.val)) fallback

/-- Evaluate a fixed finite function by scanning its complete constant table. -/
theorem isPolyTime_of_finite [Finite α] (input : α ↪ Word) (f : α → Word) :
    IsPolyTime input f := by
  classical
  let := Fintype.ofFinite α
  let table := Finset.univ.toList.map (fun a => (a, f a))
  have htable : IsPolyTime input
      (fun _ => listEncoding (pairEncoding input wordEncoding) table) := isPolyTime_const _ _
  have h := ((isPolyTime_input input).list_lookup htable).option_getD
    (fallback := fun _ => []) (isPolyTime_const input [])
  simpa only [table, List.lookup_graph f (Finset.mem_toList.mpr (Finset.mem_univ _)),
    Option.getD_some, wordEncoding, Function.Embedding.refl_apply] using h

/-- Any fixed function on a finite control value may follow its certified computation. -/
theorem IsPolyTime.finite_map [Finite β] {value : α → β}
    (hvalue : IsPolyTime input (fun a => element (value a))) (f : β → Word) :
    IsPolyTime input (fun a => f (value a)) :=
  (isPolyTime_of_finite element f).comp_encoded hvalue

/-- Select among a fixed finite collection of efficient deterministic branches. -/
theorem IsPolyTime.finite_cases [Finite β] {value : α → β} {branch : β → α → Word}
    (hvalue : IsPolyTime input (fun a => element (value a)))
    (hbranch : ∀ b, IsPolyTime input (branch b)) :
    IsPolyTime input (fun a => branch (value a) a) := by
  classical
  let := Fintype.ofFinite β
  let enum := (Fintype.equivFin β).symm
  have htable : IsPolyTime input (fun a => listEncoding (pairEncoding element wordEncoding)
      (List.ofFn (fun i => (enum i, branch (enum i) a)))) :=
    IsPolyTime.list_ofFn (fun i =>
      (isPolyTime_const input (element (enum i))).pair (hbranch (enum i)))
  have h := (hvalue.list_lookup htable).option_getD
    (fallback := fun _ => []) (isPolyTime_const input [])
  have heq (a : α) :
      (List.ofFn (fun i => (enum i, branch (enum i) a))).lookup (value a) =
        some (branch (value a) a) := by
    have hmem : value a ∈ List.ofFn enum :=
      List.mem_ofFn.mpr ⟨(Fintype.equivFin β) (value a), by simp [enum]⟩
    simpa only [List.map_ofFn, Function.comp_def] using
      List.lookup_graph (fun b => branch b a) hmem
  simpa only [heq, Option.getD_some, wordEncoding, Function.Embedding.refl_apply] using h

/-- Enumerate a fixed finite control type in unary. The enumeration is chosen once. -/
noncomputable def finiteEncoding (Control : Type) [Fintype Control] : Control ↪ Word where
  toFun state := unaryEncoding ((Fintype.equivFin Control) state).val
  inj' := by
    intro a b h
    apply (Fintype.equivFin Control).injective
    exact Fin.ext (unaryEncoding.injective h)

/-- A finite runtime index selects a component of a fixed-size tuple. -/
theorem IsPolyTime.tuple_get {values : α → Fin n → β} {index : α → Fin n}
    (hvalues : IsPolyTime input (fun a => tupleEncoding n element (values a)))
    (hindex : IsPolyTime input (fun a => finiteEncoding (Fin n) (index a))) :
    IsPolyTime input (fun a => element (values a (index a))) :=
  hindex.finite_cases (fun i => hvalues.tuple_apply i)

/-- Updating a fixed array copies the retained components and the replacement value. -/
theorem IsPolyTime.tuple_update {values : α → Fin n → β} {index : α → Fin n}
    {replacement : α → β}
    (hvalues : IsPolyTime input (fun a => tupleEncoding n element (values a)))
    (hindex : IsPolyTime input (fun a => finiteEncoding (Fin n) (index a)))
    (hreplacement : IsPolyTime input (fun a => element (replacement a))) :
    IsPolyTime input (fun a => tupleEncoding n element
      (Function.update (values a) (index a) (replacement a))) := by
  apply IsPolyTime.tuple
  intro i
  simpa only [Function.update_apply, apply_ite] using
    (hindex.finite_map (fun j => [decide (i = j)])).ite hreplacement (hvalues.tuple_apply i)

end Turing.MultiTapeTM
