/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Arithmetic
public import Cslib.Computability.Probabilistic.Fold

/-!
# Polynomial-time list operations

Runtime indices are charged through their unary encodings. Slicing uses the shared shrinking-loop
rule; enumerating an interval charges for every encoded index in its quadratic-size output.
Filtering and first-match search reuse the certified collection combinators, including predicates
that capture runtime data. Word equality checks both lengths and aligned bits.
-/

@[expose] public section

namespace Cslib.Probability

variable {α Item : Type} {encode : α → Word}

/-- Count occurrences of an efficiently computed bit in an efficiently computed word. -/
theorem IsPolyTime.count {word : α → Word} {bit : α → Bool}
    (hword : IsPolyTime encode word) (hbit : IsPolyTime encode (fun a => [bit a])) :
    IsPolyTime encode (fun a => List.replicate ((word a).count (bit a)) true) := by
  simpa only [List.count_eq_length_filter, List.filter_map, List.length_map,
    Function.comp_def, id_eq] using
    ((hword.map_with_bit hbit (fun bit value => value == bit)).filter id).unaryLength

variable {count : α → ℕ}

/-- Test a fixed Boolean predicate on every bit of an efficient word. -/
theorem IsPolyTime.any {word : α → Word} (hword : IsPolyTime encode word)
    (predicate : Bool → Bool) : IsPolyTime encode (fun a => [(word a).any predicate]) := by
  simpa [List.any_eq] using ((hword.filter predicate).unaryLength.unary_eq
    (g := fun _ => 0) (isPolyTime_const encode [])).map Bool.not

/-- Compare two efficient words, checking both their lengths and their aligned bits. -/
theorem IsPolyTime.beq {left right : α → Word}
    (hleft : IsPolyTime encode left) (hright : IsPolyTime encode right) :
    IsPolyTime encode (fun a => [left a == right a]) := by
  have heq (left right : Word) : (left == right) =
      (decide (left.length = right.length) && !(left.zipWith Bool.xor right).any id) := by
    induction left generalizing right with
    | nil => cases right <;> simp
    | cons bit left ih =>
      cases right with
      | nil => simp
      | cons bit' right => cases bit <;> cases bit' <;> simp [ih]
  simpa only [heq, List.map_singleton] using
    (hleft.unaryLength.unary_eq hright.unaryLength).bool₂
      (((hleft.zipWith hright Bool.xor).any id).map Bool.not) Bool.and

private theorem flatMap_if_singleton (predicate : Item → Bool) (values : List Item) :
    values.flatMap (fun item => if predicate item then [item] else []) =
      values.filter predicate := by
  induction values with
  | nil => rfl
  | cons item values ih => cases h : predicate item <;> simp [h, ih]

/-- Filter an encoded collection using a certified predicate. -/
theorem IsPolyTime.list_filter {element : Item ↪ Word} {values : α → List Item}
    {predicate : Item → Bool}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hpredicate : IsPolyTime element (fun value => [predicate value])) :
    IsPolyTime encode (fun a => listEncoding element ((values a).filter predicate)) := by
  have hstep : IsPolyTime element
      (fun item => listEncoding element (if predicate item then [item] else [])) := by
    simpa only [apply_ite, listEncoding_nil] using hpredicate.cond
      ((isPolyTime_input element).list_cons (isPolyTime_const element []))
      (isPolyTime_const element [])
  simpa only [flatMap_if_singleton] using hvalues.list_flatMap hstep

/-- Filter with a predicate that captures efficiently computed runtime data. -/
theorem IsPolyTime.list_filter_with {Environment : Type}
    {environment : Environment ↪ Word} {element : Item ↪ Word}
    {env : α → Environment} {values : α → List Item} {predicate : Environment → Item → Bool}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hpredicate : IsPolyTime (pairEncoding environment element)
      (fun pair => [predicate pair.1 pair.2])) :
    IsPolyTime encode (fun a => listEncoding element ((values a).filter (predicate (env a)))) := by
  have hstep : IsPolyTime (pairEncoding environment element) (fun pair =>
      listEncoding element (if predicate pair.1 pair.2 then [pair.2] else [])) := by
    simpa only [apply_ite, listEncoding_nil] using hpredicate.cond
      ((isPolyTime_snd environment element).list_cons (isPolyTime_const _ []))
      (isPolyTime_const _ [])
  simpa only [flatMap_if_singleton] using hvalues.list_flatMap_with (output := element)
    (f := fun env item => if predicate env item then [item] else []) henv hstep

/-- Read the first element, with an efficiently computed default for an empty collection. -/
theorem IsPolyTime.list_headD_with [Inhabited Item] {element : Item ↪ Word}
    {values : α → List Item} {fallback : α → Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hfallback : IsPolyTime encode (fun a => element (fallback a))) :
    IsPolyTime encode (fun a => element ((values a).headD (fallback a))) := by
  have h := (hvalues.list_unaryLength.unary_eq
    (g := fun _ => 0) (isPolyTime_const encode [])).ite hfallback (hvalues.list_headD default)
  convert h using 1
  funext a
  cases values a <;> simp

/-- Find the first match for a captured predicate, with an efficiently computed default.
Filtering before reading the head shares the existing collection implementation. -/
theorem IsPolyTime.list_findD_with {Environment : Type} [Inhabited Item]
    {environment : Environment ↪ Word} {element : Item ↪ Word}
    {env : α → Environment} {values : α → List Item} {predicate : Environment → Item → Bool}
    {fallback : α → Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hpredicate : IsPolyTime (pairEncoding environment element)
      (fun pair => [predicate pair.1 pair.2]))
    (hfallback : IsPolyTime encode (fun a => element (fallback a))) :
    IsPolyTime encode (fun a =>
      element (((values a).find? (predicate (env a))).getD (fallback a))) := by
  simpa only [List.headD_eq_head?_getD, List.head?_filter] using
    (hvalues.list_filter_with henv hpredicate).list_headD_with hfallback

/-- Drop an efficiently computed number of bits. -/
theorem IsPolyTime.drop {word : α → Word} (hword : IsPolyTime encode word)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => (word a).drop (count a)) := by
  simpa only [List.tail_iterate] using
    hword.iterate_of_length_le (step := List.tail) hcount (isPolyTime_tail wordEncoding)
      (by intro word; simp)

/-- Drop an efficiently computed number of elements from an encoded collection. -/
theorem IsPolyTime.list_drop {element : Item ↪ Word} {values : α → List Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => listEncoding element ((values a).drop (count a))) := by
  simpa only [List.tail_iterate] using hvalues.iterate_encoded_of_length_le
    (stateEncoding := listEncoding element) (step := List.tail) hcount
    (isPolyTime_list_tail element)
    (by intro values; simpa only [List.drop_one] using length_listEncoding_drop_le element values 1)

private theorem take_eq_reverse_drop_reverse {β : Type} (values : List β) (count : ℕ) :
    (values.reverse.drop (values.length - count)).reverse = values.take count := by
  rw [List.drop_reverse, List.reverse_reverse, Nat.sub_sub_eq_min, Nat.min_comm,
    ← List.take_eq_take_min]

/-- Take an efficiently computed number of bits, including requests past the end of the word. -/
theorem IsPolyTime.take {word : α → Word} (hword : IsPolyTime encode word)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => (word a).take (count a)) := by
  simpa only [take_eq_reverse_drop_reverse] using
    (hword.reverse.drop (hword.unaryLength.unary_sub hcount)).reverse

/-- Take an efficiently computed number of elements from an encoded collection. -/
theorem IsPolyTime.list_take {element : Item ↪ Word} {values : α → List Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => listEncoding element ((values a).take (count a))) := by
  simpa only [take_eq_reverse_drop_reverse] using
    (hvalues.list_reverse.list_drop (hvalues.list_unaryLength.unary_sub hcount)).list_reverse

/-- Read a bit at a runtime index, returning the fixed default out of range. -/
theorem IsPolyTime.getD {word : α → Word} (hword : IsPolyTime encode word)
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) (fallback : Bool) :
    IsPolyTime encode (fun a => [(word a)[count a]?.getD fallback]) := by
  simpa only [List.headD_eq_head?_getD, List.head?_drop] using (hword.drop hcount).headD fallback

/-- Read an encoded element at a runtime index, returning the fixed default out of range. -/
theorem IsPolyTime.list_getD {element : Item ↪ Word} {values : α → List Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) (fallback : Item) :
    IsPolyTime encode (fun a => element ((values a)[count a]?.getD fallback)) := by
  simpa only [List.headD_eq_head?_getD, List.head?_drop] using
    (hvalues.list_drop hcount).list_headD fallback

/-- Enumerate the indices below a unary bound. The encoding of `range n` occupies exactly
`n * n` bits, including the separators around zero and the other indices. -/
theorem isPolyTime_range : IsPolyTime unaryEncoding
    (fun n => listEncoding unaryEncoding (List.range n)) := by
  let advance (indices : List ℕ) := indices.length :: indices
  have hstep : IsPolyTime (listEncoding unaryEncoding)
      (fun indices => listEncoding unaryEncoding (advance indices)) :=
    (isPolyTime_list_unaryLength unaryEncoding).list_cons
      (isPolyTime_input (listEncoding unaryEncoding))
  have htrace (n : ℕ) : advance^[n] [] = (List.range n).reverse := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Function.iterate_succ_apply', advance, ih, List.range_succ]
  have hlength (n : ℕ) :
      (listEncoding unaryEncoding (List.range n).reverse).length = n * n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, listEncoding_cons, length_pairEncoding, unaryEncoding_apply,
        List.length_replicate, ih]
      ring
  have h := (isPolyTime_const unaryEncoding []).iterate_encoded
    (stateEncoding := listEncoding unaryEncoding) (initial := fun _ => []) (step := advance)
    (isPolyTime_input unaryEncoding) hstep (size := fun n => n * n) (by fun_prop) (by
      intro n index hi
      simpa only [htrace, hlength, unaryEncoding_apply, List.length_replicate] using
        Nat.mul_le_mul hi hi)
  simpa only [htrace, List.reverse_reverse] using h.list_reverse

/-- Enumerate the indices below an efficiently computed unary bound. -/
theorem IsPolyTime.range (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => listEncoding unaryEncoding (List.range (count a))) :=
  isPolyTime_range.comp_encoded (encodeArg := unaryEncoding) hcount

end Cslib.Probability
