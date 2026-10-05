/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Arithmetic
public import Cslib.Computability.PolynomialTime.Fold
public import Cslib.Computability.PolynomialTime.Option
import Mathlib.Tactic.Ring

/-!
# Polynomial-time list operations

Runtime indices are charged through their unary encodings. Slicing uses the shared shrinking-loop
rule; enumerating an interval charges for every encoded index in its quadratic-size output.
Filtering and first-match search reuse the certified collection combinators, including predicates
that capture runtime data. Word equality checks both lengths and aligned bits.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

variable {α Item Key Value : Type} {encode : α → Word}

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

/-- Read an optional head without assuming that the element type is inhabited. -/
theorem IsPolyTime.list_head? {element : Value ↪ Word} {encode : α → Word}
    {values : α → List Value}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a))) :
    IsPolyTime encode (fun a => optionEncoding element (values a).head?) := by
  have hnone := hvalues.list_unaryLength.unary_eq (g := fun _ => 0) (isPolyTime_const encode [])
  have hsome := (isPolyTime_const encode [true]).append hvalues.bitPair_fst
  have h := hnone.ite (isPolyTime_const encode []) hsome
  convert h using 1
  funext a
  cases values a <;> simp [pairEncoding]

/-- Read a bit at a unary index, preserving the distinction between a blank and a zero bit. -/
theorem IsPolyTime.get? {word : α → Word}
    (hword : IsPolyTime encode word)
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a))) :
    IsPolyTime encode (fun a => optionEncoding boolEncoding ((word a)[count a]?)) := by
  simpa only [List.head?_drop] using (hword.drop hcount).encode_list_bool.list_head?

/-- Reading the first encoded element uses the same machine across an indexed type family. -/
theorem IsPolyTime.list_head?_indexed {Value : α → Type}
    {element : ∀ a, Value a ↪ Word} {values : ∀ a, List (Value a)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a))) :
    IsPolyTime encode (fun a => optionEncoding (element a) (values a).head?) := by
  let words (a : α) := (values a).map (element a)
  have heq (a : α) : listEncoding wordEncoding (words a) =
      listEncoding (element a) (values a) :=
    listEncoding_map (element a) wordEncoding (element a) (fun _ => rfl) (values a)
  have hw : IsPolyTime encode (fun a => listEncoding wordEncoding (words a)) := by
    simpa only [heq] using hvalues
  convert hw.list_head? using 1
  funext a
  dsimp only [words]
  cases values a <;> rfl

/-- Locate the first true bit, retaining failure when every bit is false. The index is the
length of the initial false prefix, computed by the existing word-scanning machine. -/
theorem IsPolyTime.findIdx? {word : α → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => optionEncoding unaryEncoding ((word a).findIdx? id)) := by
  have heq (word : Word) : word.findIdx? id =
      if word.any id then some (word.takeWhile Bool.not).length else none := by
    induction word with
    | nil => rfl
    | cons bit word ih =>
      cases bit <;> cases h : word.any id <;> simp [List.findIdx?_cons, ih, h]
  have hindex := (hword.takeWhile Bool.not).unaryLength.option_some
    (element := fun _ => unaryEncoding)
  convert (hword.any id).cond hindex (isPolyTime_const encode []) using 1
  funext a
  rw [heq]
  split <;> rfl

/-- Locate the first match of an efficient predicate that captures runtime data. -/
theorem IsPolyTime.list_findIdx?_with {Environment : Type}
    {environment : Environment ↪ Word} {element : Item ↪ Word}
    {env : α → Environment} {values : α → List Item} {predicate : Environment → Item → Bool}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hpredicate : IsPolyTime (pairEncoding environment element)
      (fun pair => [predicate pair.1 pair.2])) :
    IsPolyTime encode (fun a =>
      optionEncoding unaryEncoding ((values a).findIdx? (predicate (env a)))) := by
  simpa only [List.findIdx?_map, Function.comp_def, id_eq] using
    (hvalues.list_map_with (output := boolEncoding) henv hpredicate).decode_list_bool.findIdx?

/-- Advancing an indexed answer tape requires only the encoded list's tail. -/
theorem IsPolyTime.list_tail_indexed {Value : α → Type}
    {element : ∀ a, Value a ↪ Word} {values : ∀ a, List (Value a)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a))) :
    IsPolyTime encode (fun a => listEncoding (element a) (values a).tail) := by
  convert hvalues.bitPair_snd using 1
  funext a
  cases values a with
  | nil => rfl
  | cons value values => exact (List.BitPair.snd_encode _ _).symm

/-- Count an indexed collection without decoding its elements. -/
theorem IsPolyTime.list_unaryLength_indexed {Value : α → Type}
    {element : ∀ a, Value a ↪ Word} {values : ∀ a, List (Value a)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a))) :
    IsPolyTime encode (fun a => unaryEncoding (values a).length) := by
  have hw : IsPolyTime encode
      (fun a => listEncoding wordEncoding ((values a).map (element a))) := by
    simpa only [listEncoding_map (element _) wordEncoding (element _) (fun _ => rfl)] using hvalues
  simpa only [List.length_map, unaryEncoding_apply] using hw.list_unaryLength

/-- Take a prefix of an indexed collection, charging for the unary index and copied elements. -/
theorem IsPolyTime.list_take_indexed {Value : α → Type}
    {element : ∀ a, Value a ↪ Word} {values : ∀ a, List (Value a)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a)))
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a))) :
    IsPolyTime encode (fun a => listEncoding (element a) ((values a).take (count a))) := by
  have hw : IsPolyTime encode
      (fun a => listEncoding wordEncoding ((values a).map (element a))) := by
    simpa only [listEncoding_map (element _) wordEncoding (element _) (fun _ => rfl)] using hvalues
  simpa only [← List.map_take,
    listEncoding_map (element _) wordEncoding (element _) (fun _ => rfl)] using hw.list_take hcount

/-- Skipping an indexed answer block charges for its unary length without decoding elements. -/
theorem IsPolyTime.list_drop_indexed {Value : α → Type}
    {element : ∀ a, Value a ↪ Word} {values : ∀ a, List (Value a)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a)))
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a))) :
    IsPolyTime encode (fun a => listEncoding (element a) ((values a).drop (count a))) := by
  let words (a : α) := (values a).map (element a)
  have heq (a : α) (values : List (Value a)) :
      listEncoding wordEncoding (values.map (element a)) = listEncoding (element a) values :=
    listEncoding_map (element a) wordEncoding (element a) (fun _ => rfl) values
  have hw : IsPolyTime encode (fun a => listEncoding wordEncoding (words a)) := by
    simpa only [words, heq] using hvalues
  simpa only [words, ← List.map_drop, heq] using hw.list_drop hcount

/-- Ordinary first-match association-list lookup charges for key comparison and scanning. -/
theorem IsPolyTime.list_lookup [BEq Key] [LawfulBEq Key]
    {key : Key ↪ Word} {value : Value ↪ Word}
    {encode : α → Word} {keys : α → Key} {values : α → List (Key × Value)}
    (hkeys : IsPolyTime encode (fun a => key (keys a)))
    (hvalues : IsPolyTime encode (fun a => listEncoding (pairEncoding key value) (values a))) :
    IsPolyTime encode (fun a => optionEncoding value ((values a).lookup (keys a))) := by
  classical
  let item := pairEncoding key value
  have hpred : IsPolyTime (pairEncoding key item)
      (fun p => [decide (p.1 = p.2.1)]) := by
    have h := (isPolyTime_fst key item).beq (isPolyTime_snd key item).fst
    simpa only [Bool.beq_eq_decide_eq, key.injective.eq_iff] using h
  have hfiltered := hvalues.list_filter_with
    (predicate := fun k pair => decide (k = pair.1)) hkeys hpred
  have hmapped := hfiltered.list_map (isPolyTime_snd key value)
  have hhead := hmapped.list_head?
  convert hhead using 1
  funext a
  congr 1
  have heq (input : Key) (entries : List (Key × Value)) :
      entries.lookup input =
        ((entries.filter (fun pair => decide (input = pair.1))).map Prod.snd).head? := by
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
      rcases entry with ⟨k, v⟩
      by_cases he : input = k <;> simp [List.lookup_cons, Bool.beq_eq_decide_eq, he, ih]
  exact heq _ _

private theorem lookup_map_encoding [BEq Key] [LawfulBEq Key]
    (key : Key ↪ Word) (value : Value ↪ Word) (entries : List (Key × Value)) (query : Key) :
    (entries.map (fun pair => (key pair.1, value pair.2))).lookup (key query) =
      (entries.lookup query).map value := by
  classical
  induction entries with
  | nil => rfl
  | cons pair entries ih =>
    rcases pair with ⟨k, v⟩
    by_cases he : query = k
    · simp [he]
    · simp [List.lookup_cons, Bool.beq_eq_decide_eq, key.injective.eq_iff, he, ih]

/-- The same lookup machine works across an indexed family of key and value encodings. -/
theorem IsPolyTime.list_lookup_indexed {ι : Type} {Key Value : ι → Type}
    [∀ i, BEq (Key i)] [∀ i, LawfulBEq (Key i)]
    {parameter : α → ι} {key : ∀ i, Key i ↪ Word} {value : ∀ i, Value i ↪ Word}
    {keys : ∀ a, Key (parameter a)} {values : ∀ a, List (Key (parameter a) × Value (parameter a))}
    (hkeys : IsPolyTime encode (fun a => key (parameter a) (keys a)))
    (hvalues : IsPolyTime encode
      (fun a => listEncoding (pairEncoding (key (parameter a)) (value (parameter a))) (values a))) :
    IsPolyTime encode
      (fun a => optionEncoding (value (parameter a)) ((values a).lookup (keys a))) := by
  let words (a : α) := (values a).map
    (fun pair => (key (parameter a) pair.1, value (parameter a) pair.2))
  have heq (a : α) : listEncoding (pairEncoding wordEncoding wordEncoding) (words a) =
      listEncoding (pairEncoding (key (parameter a)) (value (parameter a))) (values a) :=
    listEncoding_map (pairEncoding (key (parameter a)) (value (parameter a)))
      (pairEncoding wordEncoding wordEncoding)
      (fun pair => (key (parameter a) pair.1, value (parameter a) pair.2))
      (fun _ => rfl) (values a)
  have hw : IsPolyTime encode
      (fun a => listEncoding (pairEncoding wordEncoding wordEncoding) (words a)) := by
    simpa only [heq] using hvalues
  have h := hkeys.list_lookup (key := wordEncoding) hw
  convert h using 1
  funext a
  change optionEncoding (value (parameter a)) ((values a).lookup (keys a)) =
    optionEncoding wordEncoding ((words a).lookup (key (parameter a) (keys a)))
  rw [show (words a).lookup (key (parameter a) (keys a)) =
    ((values a).lookup (keys a)).map (value (parameter a)) from
      lookup_map_encoding (key (parameter a)) (value (parameter a)) (values a) (keys a)]
  exact (optionEncoding_map (value (parameter a)) wordEncoding (value (parameter a))
    (fun _ => rfl) ((values a).lookup (keys a))).symm

/-- Membership compares encoded values, using one machine for every indexed element type. -/
theorem IsPolyTime.list_mem_indexed {Value : α → Type} [∀ a, DecidableEq (Value a)]
    {element : ∀ a, Value a ↪ Word} {value : ∀ a, Value a} {values : ∀ a, List (Value a)}
    (hvalue : IsPolyTime encode (fun a => element a (value a)))
    (hvalues : IsPolyTime encode (fun a => listEncoding (element a) (values a))) :
    IsPolyTime encode (fun a => [decide (value a ∈ values a)]) := by
  have hwords : IsPolyTime encode
      (fun a => listEncoding wordEncoding ((values a).map (element a))) := by
    simpa only [listEncoding_map (element _) wordEncoding (element _) (fun _ => rfl)] using hvalues
  have hfiltered := hwords.list_filter_with (environment := wordEncoding) hvalue
    ((isPolyTime_fst wordEncoding wordEncoding).beq (isPolyTime_snd wordEncoding wordEncoding))
  have h := (hfiltered.beq (isPolyTime_const encode [])).map Bool.not
  convert h using 1
  funext a
  simp only [List.map_singleton]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
  rw [← listEncoding_nil wordEncoding, (listEncoding wordEncoding).injective.ne_iff]
  simp [ne_eq, List.filter_eq_nil_iff, Bool.beq_eq_decide_eq, (element a).injective.eq_iff]

end Turing.MultiTapeTM
