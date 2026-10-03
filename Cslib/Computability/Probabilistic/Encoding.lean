/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PolynomialTime
public import Cslib.Foundations.Data.List.BitPair

/-!
# Efficient encodings and data operations

`pairEncoding` combines explicit encodings without exposing their machine representations.
Pair construction, projections, and calls on pairs have polynomial-time certificates. The
projection proofs share one finite-state transducer and the existing transducer compiler.
`coinInputEncoding` is the word-pair instance used for deterministic evaluation with saved coins.
`listEncoding` reuses this representation for cons cells and the same projections for head and
tail. Its size is linear in the collection's contents, including empty element encodings.
-/

@[expose] public section

namespace Cslib.Probability

open Automata

variable {α β γ : Type}

/-- Unary natural numbers charge their numerical value to the input or output length. -/
def unaryEncoding : ℕ ↪ Word where
  toFun n := List.replicate n true
  inj' := by intro m n h; simpa using congrArg List.length h

@[simp] theorem unaryEncoding_apply (n : ℕ) : unaryEncoding n = List.replicate n true := rfl

/-- Encode a pair using tagged bits for its first component and a delimiter before the second. -/
def pairEncoding (left : α ↪ Word) (right : β ↪ Word) : (α × β) ↪ Word where
  toFun pair := List.BitPair.encode (left pair.1) (right pair.2)
  inj' := by
    intro a b h
    obtain ⟨hl, hr⟩ := List.BitPair.encode_inj.mp h
    exact Prod.ext (left.injective hl) (right.injective hr)

@[simp] theorem length_pairEncoding (left : α ↪ Word) (right : β ↪ Word) (pair : α × β) :
    (pairEncoding left right pair).length = 2 * (left pair.1).length + (right pair.2).length + 1 :=
  List.BitPair.length_encode _ _

/-- A coin tape and an ordinary input use the shared binary pair encoding. -/
abbrev coinInputEncoding : (Word × Word) ↪ Word := pairEncoding wordEncoding wordEncoding

private def project (first : Bool) (fallback : Word := []) :
    DeterministicTransducer Bool Bool (Option Bool) where
  initial := none
  next state bit := match state with
    | none => some bit
    | some true => none
    | some false => some false
  output state bit := match state with
    | none => []
    | some side => if side == first then [bit] else []
  finish state := if state.isNone then fallback else []

private theorem project_eval_suffix (first : Bool) (word : Word) (fallback : Word := []) :
    (project first fallback).evalFrom (some false) word = if first then [] else word := by
  induction word with
  | nil => cases first <;> rfl
  | cons bit word ih =>
    change (if false == first then [bit] else []) ++
      (project first fallback).evalFrom (some false) word = if first then [] else bit :: word
    rw [ih]
    cases first <;> rfl

private theorem project_eval (first : Bool) (left right : Word) (fallback : Word := []) :
    (project first fallback).eval (List.BitPair.encode left right) =
      if first then left else right := by
  induction left with
  | nil => exact project_eval_suffix first right fallback
  | cons bit left ih =>
    change (if true == first then [bit] else []) ++
      (project first fallback).eval (List.BitPair.encode left right) =
        if first then bit :: left else right
    rw [ih]
    cases first <;> rfl

private theorem project_eval_decode (first : Bool) (word : Word) :
    (project first).eval word =
      if first then List.BitPair.fst word else List.BitPair.snd word := by
  match word with
  | [] => cases first <;> rfl
  | false :: rest => exact project_eval_suffix first rest
  | [true] => cases first <;> rfl
  | true :: bit :: rest =>
    change (if true == first then [bit] else []) ++ (project first).eval rest =
      if first then bit :: List.BitPair.fst rest else List.BitPair.snd rest
    rw [project_eval_decode first rest]
    cases first <;> rfl

/-- Total first-component decoding is polynomial time, including malformed words. -/
theorem isPolyTime_bitPair_fst : IsPolyTime wordEncoding List.BitPair.fst := by
  simpa [project_eval_decode, wordEncoding] using (project true).isPolyTime wordEncoding

/-- Total second-component decoding shares the same finite-state transducer. -/
theorem isPolyTime_bitPair_snd : IsPolyTime wordEncoding List.BitPair.snd := by
  simpa [project_eval_decode, wordEncoding] using (project false).isPolyTime wordEncoding

/-- Reading the first component of a pair is polynomial time in its complete encoding. -/
theorem isPolyTime_fst (left : α ↪ Word) (right : β ↪ Word) :
    IsPolyTime (pairEncoding left right) (fun pair => left pair.1) := by
  simpa only [pairEncoding, Function.Embedding.coeFn_mk, project_eval, ↓reduceIte] using
    (project true).isPolyTime (pairEncoding left right)

/-- Reading the second component of a pair is polynomial time in its complete encoding. -/
theorem isPolyTime_snd (left : α ↪ Word) (right : β ↪ Word) :
    IsPolyTime (pairEncoding left right) (fun pair => right pair.2) := by
  simpa only [pairEncoding, Function.Embedding.coeFn_mk, project_eval, Bool.false_eq_true,
    ↓reduceIte] using (project false).isPolyTime (pairEncoding left right)

/-- A list is a sequence of self-delimiting element encodings. Its representation is linear
in the sum of element sizes; encoding a cons cell reuses the pair representation. -/
def listEncoding (element : α ↪ Word) : List α ↪ Word where
  toFun values := values.foldr (fun value rest => List.BitPair.encode (element value) rest) []
  inj' := by
    intro values others h
    induction values generalizing others with
    | nil =>
      cases others with
      | nil => rfl
      | cons value rest => have := congrArg List.length h; simp at this
    | cons value rest ih =>
      cases others with
      | nil => have := congrArg List.length h; simp at this
      | cons other others =>
        obtain ⟨hhead, htail⟩ := List.BitPair.encode_inj.mp h
        exact congrArg₂ List.cons (element.injective hhead) (ih htail)

@[simp] theorem listEncoding_nil (element : α ↪ Word) : listEncoding element [] = [] := rfl

@[simp] theorem listEncoding_cons (element : α ↪ Word) (value : α) (rest : List α) :
    listEncoding element (value :: rest) = pairEncoding element (listEncoding element)
      (value, rest) := rfl

/-- Concatenation of lists is concatenation of their encoded words. -/
@[simp] theorem listEncoding_append (element : α ↪ Word) (values others : List α) :
    listEncoding element (values ++ others) = listEncoding element values ++
      listEncoding element others := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    simp only [List.cons_append, listEncoding_cons, pairEncoding, Function.Embedding.coeFn_mk,
      List.BitPair.encode, ih, List.append_assoc, List.cons_append]

/-- Every element contributes its tagged data and one delimiter. -/
@[simp] theorem length_listEncoding (element : α ↪ Word) (values : List α) :
    (listEncoding element values).length =
      (values.map (fun value => 2 * (element value).length + 1)).sum := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Even zero-length element codes occupy a delimiter in a list. -/
theorem list_length_le_length_encoding (element : α ↪ Word) (values : List α) :
    values.length ≤ (listEncoding element values).length := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    simp only [List.length_cons, listEncoding_cons, length_pairEncoding]
    lia

/-- An element's code fits within the code of a list containing it. -/
theorem length_element_le_length_listEncoding (element : α ↪ Word)
    {value : α} {values : List α} (hmem : value ∈ values) :
    (element value).length ≤ (listEncoding element values).length := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
    simp only [listEncoding_cons, length_pairEncoding]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · lia
    · have := ih hmem; lia

/-- A uniform element-size bound gives a linear bound on the encoded collection. -/
theorem length_listEncoding_le (element : α ↪ Word) {values : List α} {bound : ℕ}
    (hbound : ∀ value ∈ values, (element value).length ≤ bound) :
    (listEncoding element values).length ≤ values.length * (2 * bound + 1) := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have hhead := hbound value (by simp)
    have hrest := ih (fun value hmem => hbound value (by simp [hmem]))
    simp only [listEncoding_cons, length_pairEncoding, List.length_cons, Nat.add_mul]
    lia

/-- Removing an initial segment cannot increase the representation size. -/
theorem length_listEncoding_drop_le (element : α ↪ Word) (values : List α) (count : ℕ) :
    (listEncoding element (values.drop count)).length ≤ (listEncoding element values).length := by
  have h := congrArg List.length
    (listEncoding_append element (values.take count) (values.drop count))
  rw [List.take_append_drop, List.length_append] at h
  lia

/-- Reading a list head shares the pair projection; the fixed default handles the empty list. -/
theorem isPolyTime_list_headD (element : α ↪ Word) (fallback : α) :
    IsPolyTime (listEncoding element) (fun values => element (values.headD fallback)) := by
  have heval (values : List α) :
      (project true (element fallback)).eval (listEncoding element values) =
        element (values.headD fallback) := by
    cases values with
    | nil => rfl
    | cons value rest => exact project_eval true _ _ _
  simpa only [heval] using (project true (element fallback)).isPolyTime (listEncoding element)

/-- Reading a list tail shares the pair projection, including the empty-list case. -/
theorem isPolyTime_list_tail (element : α ↪ Word) :
    IsPolyTime (listEncoding element) (fun values => listEncoding element values.tail) := by
  have heval (values : List α) : (project false).eval (listEncoding element values) =
      listEncoding element values.tail := by
    cases values with
    | nil => rfl
    | cons value rest => exact project_eval false _ _
  simpa only [heval] using (project false).isPolyTime (listEncoding element)

private def listCounter : DeterministicTransducer Bool Bool Bool where
  initial := false
  next data bit := !data && bit
  output data bit := if !data && !bit then [true] else []
  finish _ := []

/-- Count list elements in unary by recognizing their delimiters. -/
theorem isPolyTime_list_unaryLength (element : α ↪ Word) :
    IsPolyTime (listEncoding element) (fun values => List.replicate values.length true) := by
  have hpair (head rest : Word) : listCounter.eval (List.BitPair.encode head rest) =
      true :: listCounter.eval rest := by
    induction head with
    | nil => rfl
    | cons bit head ih => exact ih
  have heval (values : List α) : listCounter.eval (listEncoding element values) =
      List.replicate values.length true := by
    induction values with
    | nil => rfl
    | cons value rest ih =>
      change listCounter.eval (List.BitPair.encode (element value) (listEncoding element rest)) =
        List.replicate (rest.length + 1) true
      rw [hpair, ih, List.replicate_succ]
  simpa only [heval] using listCounter.isPolyTime (listEncoding element)

/-- Encoding a word as a list of bits is a fixed substitution. -/
@[simp] theorem listEncoding_bool (word : Word) :
    listEncoding boolEncoding word = word.flatMap (fun bit => [true, bit, false]) := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    change true :: bit :: false :: listEncoding boolEncoding word =
      true :: bit :: false :: word.flatMap (fun bit => [true, bit, false])
    rw [ih]

variable {encode : γ → Word} {left : α ↪ Word} {right : β ↪ Word}

/-- Decode the first component of an efficiently computed word. -/
theorem IsPolyTime.bitPair_fst {word : γ → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => List.BitPair.fst (word a)) :=
  isPolyTime_bitPair_fst.comp_encoded hword

/-- Decode the second component of an efficiently computed word. -/
theorem IsPolyTime.bitPair_snd {word : γ → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => List.BitPair.snd (word a)) :=
  isPolyTime_bitPair_snd.comp_encoded hword

/-- Pair two efficiently computed values, charging for the complete encoded pair. -/
theorem IsPolyTime.pair {f : γ → α} {g : γ → β}
    (hf : IsPolyTime encode (fun a => left (f a)))
    (hg : IsPolyTime encode (fun a => right (g a))) :
    IsPolyTime encode (fun a => pairEncoding left right (f a, g a)) :=
  (hf.flatMap (fun bit => [true, bit])).append ((isPolyTime_const encode [false]).append hg)

/-- Project the first component of an efficiently computed pair. -/
theorem IsPolyTime.fst {f : γ → α × β} (hf : IsPolyTime encode (fun a =>
    pairEncoding left right (f a))) : IsPolyTime encode (fun a => left (f a).1) :=
  (isPolyTime_fst left right).comp_encoded hf

/-- Project the second component of an efficiently computed pair. -/
theorem IsPolyTime.snd {f : γ → α × β} (hf : IsPolyTime encode (fun a =>
    pairEncoding left right (f a))) : IsPolyTime encode (fun a => right (f a).2) :=
  (isPolyTime_snd left right).comp_encoded hf

/-- Call a certified two-argument function on two efficiently prepared values. -/
theorem IsPolyTime.comp_pair {f : α → β → Word} {g : γ → α} {h : γ → β}
    (hf : IsPolyTime (pairEncoding left right) (fun pair => f pair.1 pair.2))
    (hg : IsPolyTime encode (fun a => left (g a)))
    (hh : IsPolyTime encode (fun a => right (h a))) :
    IsPolyTime encode (fun a => f (g a) (h a)) :=
  hf.comp_encoded (hg.pair hh)

variable {element : α ↪ Word}

/-- Construct a list from an efficient element and tail. -/
theorem IsPolyTime.list_cons {value : γ → α} {rest : γ → List α}
    (hvalue : IsPolyTime encode (fun a => element (value a)))
    (hrest : IsPolyTime encode (fun a => listEncoding element (rest a))) :
    IsPolyTime encode (fun a => listEncoding element (value a :: rest a)) :=
  hvalue.pair (right := listEncoding element) hrest

/-- Append two efficiently computed lists. -/
theorem IsPolyTime.list_append {values others : γ → List α}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hothers : IsPolyTime encode (fun a => listEncoding element (others a))) :
    IsPolyTime encode (fun a => listEncoding element (values a ++ others a)) := by
  simpa only [listEncoding_append] using hvalues.append hothers

/-- Read the head of an efficiently computed list, with a fixed default. -/
theorem IsPolyTime.list_headD {values : γ → List α}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a))) (fallback : α) :
    IsPolyTime encode (fun a => element ((values a).headD fallback)) :=
  (isPolyTime_list_headD element fallback).comp_encoded hvalues

/-- Drop the head of an efficiently computed list. -/
theorem IsPolyTime.list_tail {values : γ → List α}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a))) :
    IsPolyTime encode (fun a => listEncoding element (values a).tail) :=
  (isPolyTime_list_tail element).comp_encoded hvalues

/-- Count the elements of an efficiently computed list in unary. -/
theorem IsPolyTime.list_unaryLength {values : γ → List α}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a))) :
    IsPolyTime encode (fun a => List.replicate (values a).length true) :=
  (isPolyTime_list_unaryLength element).comp_encoded hvalues

/-- View an efficiently computed word as an encoded list of bits. -/
theorem IsPolyTime.encode_list_bool {word : γ → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => listEncoding boolEncoding (word a)) := by
  simpa only [listEncoding_bool] using hword.flatMap (fun bit => [true, bit, false])

private def withBit (code : Bool → Bool → Word) :
    DeterministicTransducer Bool Bool (Option Bool × Bool) where
  initial := (none, false)
  next state bit := match state with
    | (none, false) => (none, true)
    | (none, true) => (some bit, true)
    | (some saved, _) => (some saved, false)
  output state bit := match state with
    | (some saved, false) => code saved bit
    | _ => []
  finish _ := []

/-- A bit supplied at runtime can select a substitution for every bit of a word. The finite
transducer reads the bit's encoding, retains it, and applies the selected substitution. -/
theorem isPolyTime_flatMap_with_bit (code : Bool → Bool → Word) :
    IsPolyTime (pairEncoding boolEncoding wordEncoding)
      (fun pair => pair.2.flatMap (code pair.1)) := by
  have hsuffix (saved : Bool) (word : Word) :
      (withBit code).evalFrom (some saved, false) word = word.flatMap (code saved) := by
    induction word with
    | nil => rfl
    | cons bit word ih => exact congrArg (code saved bit ++ ·) ih
  have heval (pair : Bool × Word) :
      (withBit code).eval (pairEncoding boolEncoding wordEncoding pair) =
        pair.2.flatMap (code pair.1) := hsuffix pair.1 pair.2
  simpa only [heval] using (withBit code).isPolyTime (pairEncoding boolEncoding wordEncoding)

/-- Substitute bits using an efficiently computed Boolean parameter. -/
theorem IsPolyTime.flatMap_with_bit {word : γ → Word} {bit : γ → Bool}
    (hword : IsPolyTime encode word) (hbit : IsPolyTime encode (fun a => [bit a]))
    (code : Bool → Bool → Word) :
    IsPolyTime encode (fun a => (word a).flatMap (code (bit a))) :=
  (isPolyTime_flatMap_with_bit code).comp_pair
    (left := boolEncoding) (right := wordEncoding)
    (f := fun bit word => word.flatMap (code bit)) hbit hword

/-- Map over an efficient word using an efficiently computed Boolean parameter. -/
theorem IsPolyTime.map_with_bit {word : γ → Word} {bit : γ → Bool}
    (hword : IsPolyTime encode word) (hbit : IsPolyTime encode (fun a => [bit a]))
    (op : Bool → Bool → Bool) :
    IsPolyTime encode (fun a => (word a).map (op (bit a))) := by
  simpa only [List.map_eq_flatMap] using hword.flatMap_with_bit hbit (fun x y => [op x y])

/-- Apply any fixed Boolean operation to an efficiently computed bit. -/
theorem IsPolyTime.bool₁ {f : γ → Bool} (hf : IsPolyTime encode (fun a => [f a]))
    (op : Bool → Bool) : IsPolyTime encode (fun a => [op (f a)]) := by
  simpa using hf.map op

/-- Combine two efficiently computed bits by any fixed Boolean operation. -/
theorem IsPolyTime.bool₂ {f g : γ → Bool}
    (hf : IsPolyTime encode (fun a => [f a])) (hg : IsPolyTime encode (fun a => [g a]))
    (op : Bool → Bool → Bool) : IsPolyTime encode (fun a => [op (f a) (g a)]) := by
  simpa using hg.map_with_bit hf op

/-- Select between two efficient words using an efficiently computed condition. Both branches
have their own certificates, so this rule also accounts for their output sizes. -/
theorem IsPolyTime.ite {condition : γ → Prop} [∀ a, Decidable (condition a)] {yes no : γ → Word}
    (hcondition : IsPolyTime encode (fun a => [decide (condition a)]))
    (hyes : IsPolyTime encode yes) (hno : IsPolyTime encode no) :
    IsPolyTime encode (fun a => if condition a then yes a else no a) := by
  have h := (hyes.flatMap_with_bit hcondition (fun bit value => if bit then [value] else [])).append
    (hno.flatMap_with_bit hcondition (fun bit value => if bit then [] else [value]))
  convert h using 1
  funext a
  by_cases ha : condition a <;> simp [ha]

/-- Select a word using an efficiently computed Boolean flag. -/
theorem IsPolyTime.cond {condition : γ → Bool} {yes no : γ → Word}
    (hcondition : IsPolyTime encode (fun a => [condition a]))
    (hyes : IsPolyTime encode yes) (hno : IsPolyTime encode no) :
    IsPolyTime encode (fun a => if condition a then yes a else no a) := by
  apply IsPolyTime.ite
  · simpa using hcondition
  · exact hyes
  · exact hno

end Cslib.Probability
