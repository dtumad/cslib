/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.PolynomialTime
public import Cslib.Computability.Probabilistic.Realization.Transducer
public import Cslib.Computability.Probabilistic.Realization.Iteration

/-!
# Deterministic polynomial-time algorithms

The public efficiency interface includes word substitutions, finite-state folds, constants,
input projections, and concatenation of polynomial-time word functions.
Machine construction and simulation proofs live in
`Cslib.Computability.Probabilistic.Realization.PolynomialTime`.
Algorithm-level efficiency proofs use the closure theorems without unpacking their witnesses.
-/

@[expose] public section

namespace Cslib.Probability

open Automata

variable {α : Type} (encode : α → Word)

/-- Replacing each input bit by a fixed word is polynomial time. -/
theorem isPolyTime_flatMap (code : Bool → Word) :
    IsPolyTime encode (fun a => (encode a).flatMap code) := by
  simpa using (DeterministicTransducer.flatMap code).isPolyTime encode

/-- Any fold through a fixed finite state space, followed by a fixed output encoding, is efficient.
Finiteness applies to the accumulator, so this rule does not make arbitrary folds efficient. -/
theorem isPolyTime_foldl {State : Type} [Finite State] (next : State → Bool → State)
    (initial : State) (finish : State → Word) :
    IsPolyTime encode (fun a => finish ((encode a).foldl next initial)) := by
  simpa using (DeterministicTransducer.fold next initial finish).isPolyTime encode

/-- A Boolean fold returns one encoded output bit. -/
theorem isPolyTime_foldl_bool (next : Bool → Bool → Bool) (initial : Bool) :
    IsPolyTime encode (fun a => [(encode a).foldl next initial]) :=
  isPolyTime_foldl encode next initial List.singleton

/-- A fixed output word can be produced in polynomial time for any input encoding. -/
theorem isPolyTime_const (output : Word) : IsPolyTime encode (fun _ => output) :=
  isPolyTime_foldl encode (fun (_ : Unit) (_ : Bool) => ()) () (fun _ => output)

/-- Copying the encoded input is polynomial time. -/
theorem isPolyTime_input : IsPolyTime encode encode := by
  simpa using isPolyTime_flatMap encode (fun bit => [bit])

/-- A fixed map on input bits is polynomial time. -/
theorem isPolyTime_map (f : Bool → Bool) :
    IsPolyTime encode (fun a => (encode a).map f) := by
  simpa only [List.map_eq_flatMap] using isPolyTime_flatMap encode (fun bit => [f bit])

/-- Filtering input bits by a fixed predicate is polynomial time. -/
theorem isPolyTime_filter (p : Bool → Bool) :
    IsPolyTime encode (fun a => (encode a).filter p) := by
  have heq (word : Word) : word.flatMap (fun bit => if p bit then [bit] else []) =
      word.filter p := by
    induction word with
    | nil => rfl
    | cons bit word ih => cases h : p bit <;> simp [h, ih]
  simpa only [heq] using isPolyTime_flatMap encode (fun bit => if p bit then [bit] else [])

/-- Compute the input length in unary. Its output length is charged in the efficiency proof. -/
theorem isPolyTime_unaryLength :
    IsPolyTime encode (fun a => List.replicate (encode a).length true) := by
  have heq (word : Word) : word.flatMap (fun _ => [true]) =
      List.replicate word.length true := by
    induction word with
    | nil => rfl
    | cons bit word ih => simp [List.replicate_succ, ih]
  simpa only [heq] using isPolyTime_flatMap encode (fun _ => [true])

/-- Drop the first input bit, returning the empty word on an empty input. -/
theorem isPolyTime_tail : IsPolyTime encode (fun a => (encode a).tail) := by
  let transducer : DeterministicTransducer Bool Bool Bool :=
    { initial := true, next := fun _ _ => false,
      output := fun first bit => if first then [] else [bit], finish := fun _ => [] }
  have heval (word : Word) (first : Bool) :
      transducer.evalFrom first word = if first then word.tail else word := by
    induction word generalizing first with
    | nil => cases first <;> rfl
    | cons bit word ih => cases first <;> simp [DeterministicTransducer.evalFrom, transducer, ih]
  simpa [DeterministicTransducer.eval, heval, transducer] using transducer.isPolyTime encode

/-- Read the first input bit as a word of length at most one. -/
theorem isPolyTime_head : IsPolyTime encode (fun a => (encode a).take 1) := by
  let transducer : DeterministicTransducer Bool Bool Bool :=
    { initial := true, next := fun _ _ => false,
      output := fun first bit => if first then [bit] else [], finish := fun _ => [] }
  have heval (word : Word) (first : Bool) :
      transducer.evalFrom first word = if first then word.take 1 else [] := by
    induction word generalizing first with
    | nil => cases first <;> rfl
    | cons bit word ih => cases first <;> simp [DeterministicTransducer.evalFrom, transducer, ih]
  simpa [DeterministicTransducer.eval, heval, transducer] using transducer.isPolyTime encode

/-- Read the first bit, using a fixed fallback on empty input, and encode it as one bit. -/
theorem isPolyTime_headD (fallback : Bool) :
    IsPolyTime encode (fun a => [(encode a).headD fallback]) := by
  let transducer : DeterministicTransducer Bool Bool Bool :=
    { initial := true, next := fun _ _ => false,
      output := fun first bit => if first then [bit] else [],
      finish := fun first => if first then [fallback] else [] }
  have heval (word : Word) (first : Bool) :
      transducer.evalFrom first word = if first then [word.headD fallback] else [] := by
    induction word generalizing first with
    | nil => cases first <;> rfl
    | cons bit word ih => cases first <;> simp [DeterministicTransducer.evalFrom, transducer, ih]
  simpa [DeterministicTransducer.eval, heval, transducer] using transducer.isPolyTime encode

/-- Read the longest prefix whose bits satisfy a fixed predicate. -/
theorem isPolyTime_takeWhile (p : Bool → Bool) :
    IsPolyTime encode (fun a => (encode a).takeWhile p) := by
  let transducer : DeterministicTransducer Bool Bool Bool :=
    { initial := true, next := fun active bit => active && p bit,
      output := fun active bit => if active && p bit then [bit] else [], finish := fun _ => [] }
  have heval (word : Word) (active : Bool) :
      transducer.evalFrom active word = if active then word.takeWhile p else [] := by
    induction word generalizing active with
    | nil => cases active <;> rfl
    | cons bit word ih =>
      change (if active && p bit then [bit] else []) ++
        transducer.evalFrom (active && p bit) word =
          if active then (bit :: word).takeWhile p else []
      cases active <;> cases h : p bit <;>
        simp [h, ih]
  have h := transducer.isPolyTime encode
  change IsPolyTime encode (fun a => transducer.evalFrom true (encode a)) at h
  simpa only [heval, ↓reduceIte] using h

/-- Skip the longest prefix whose bits satisfy a fixed predicate. -/
theorem isPolyTime_dropWhile (p : Bool → Bool) :
    IsPolyTime encode (fun a => (encode a).dropWhile p) := by
  let transducer : DeterministicTransducer Bool Bool Bool :=
    { initial := true, next := fun active bit => active && p bit,
      output := fun active bit => if active && p bit then [] else [bit], finish := fun _ => [] }
  have heval (word : Word) (active : Bool) :
      transducer.evalFrom active word = if active then word.dropWhile p else word := by
    induction word generalizing active with
    | nil => cases active <;> rfl
    | cons bit word ih =>
      change (if active && p bit then [] else [bit]) ++
        transducer.evalFrom (active && p bit) word =
          if active then (bit :: word).dropWhile p else bit :: word
      cases active <;> cases h : p bit <;>
        simp [h, ih]
  have h := transducer.isPolyTime encode
  change IsPolyTime encode (fun a => transducer.evalFrom true (encode a)) at h
  simpa only [heval, ↓reduceIte] using h

variable {encode}

/-- Efficiently prepare an encoded argument and call its certified implementation. The callee
only needs a contract on valid encodings; arbitrary malformed words are never supplied to it. -/
theorem IsPolyTime.comp_encoded {β : Type} {encodeArg : β → Word}
    {f : α → β} {g : β → Word}
    (hg : IsPolyTime encodeArg g) (hf : IsPolyTime encode (fun a => encodeArg (f a))) :
    IsPolyTime encode (fun a => g (f a)) := by
  obtain ⟨c, d, hfsize⟩ := hf.length_le
  obtain ⟨c', d', hgsize⟩ := hg.length_le
  let firstSize := fun length => c * (length + 1) ^ d
  let secondSize := fun length => c' * (length + 1) ^ d'
  have hfirst : PolynomiallyBounded firstSize := ⟨c, d, fun _ => le_rfl⟩
  have hsecond : PolynomiallyBounded secondSize := ⟨c', d', fun _ => le_rfl⟩
  apply Realization.isPolyTime_of_trajectory
    (values := fun a index => if index = 0 then encodeArg (f a) else g (f a))
    (arguments := fun a _ => f a) (count := fun _ => 1)
    hf (isPolyTime_const encode [true]) hg
    (by
      intro a index hi
      have : index = 0 := by lia
      simp [this])
    (by intro a index _; simp)
    (hfirst.add (hsecond.comp hfirst))
  intro a index hindex
  have hcases : index = 0 ∨ index = 1 := by lia
  rcases hcases with rfl | rfl
  · exact (hfsize a).trans (Nat.le_add_right _ _)
  · simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
    apply (hgsize (f a)).trans
    apply le_trans _ (Nat.le_add_left _ _)
    exact Nat.mul_le_mul_left c'
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hfsize a) 1) d')

/-- Polynomial-time word functions compose. The intermediate output length bounds the second
call's runtime; both calls are implemented by one fixed finite machine. -/
theorem IsPolyTime.comp {f : α → Word} {g : Word → Word}
    (hg : IsPolyTime wordEncoding g) (hf : IsPolyTime encode f) :
    IsPolyTime encode (fun a => g (f a)) :=
  hg.comp_encoded hf

/-- Replace every output bit of an efficient function by a fixed word. -/
theorem IsPolyTime.flatMap {f : α → Word} (hf : IsPolyTime encode f) (code : Bool → Word) :
    IsPolyTime encode (fun a => (f a).flatMap code) :=
  (isPolyTime_flatMap wordEncoding code).comp hf

/-- Map a fixed bit function over the output of an efficient function. -/
theorem IsPolyTime.map {f : α → Word} (hf : IsPolyTime encode f) (g : Bool → Bool) :
    IsPolyTime encode (fun a => (f a).map g) :=
  (isPolyTime_map wordEncoding g).comp hf

/-- Prepend an efficiently computed bit to an efficiently computed word. -/
theorem IsPolyTime.cons {bit : α → Bool} {word : α → Word}
    (hbit : IsPolyTime encode (fun a => [bit a])) (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => bit a :: word a) :=
  hbit.append hword

/-- Filter the output of an efficient function by a fixed predicate. -/
theorem IsPolyTime.filter {f : α → Word} (hf : IsPolyTime encode f) (p : Bool → Bool) :
    IsPolyTime encode (fun a => (f a).filter p) :=
  (isPolyTime_filter wordEncoding p).comp hf

/-- Run a finite-state fold over the output of an efficient function. -/
theorem IsPolyTime.foldl {State : Type} [Finite State] {f : α → Word}
    (hf : IsPolyTime encode f) (next : State → Bool → State) (initial : State)
    (finish : State → Word) :
    IsPolyTime encode (fun a => finish ((f a).foldl next initial)) :=
  (isPolyTime_foldl wordEncoding next initial finish).comp hf

/-- Fold an efficiently computed word into a Boolean accumulator. -/
theorem IsPolyTime.foldl_bool {f : α → Word} (hf : IsPolyTime encode f)
    (next : Bool → Bool → Bool) (initial : Bool) :
    IsPolyTime encode (fun a => [(f a).foldl next initial]) :=
  hf.foldl next initial List.singleton

/-- Compute the output length of an efficient function in unary. -/
theorem IsPolyTime.unaryLength {f : α → Word} (hf : IsPolyTime encode f) :
    IsPolyTime encode (fun a => List.replicate (f a).length true) :=
  (isPolyTime_unaryLength wordEncoding).comp hf

/-- Drop the first bit from an efficiently computed word. -/
theorem IsPolyTime.tail {f : α → Word} (hf : IsPolyTime encode f) :
    IsPolyTime encode (fun a => (f a).tail) :=
  (isPolyTime_tail wordEncoding).comp hf

/-- Read the first bit of an efficiently computed word. -/
theorem IsPolyTime.head {f : α → Word} (hf : IsPolyTime encode f) :
    IsPolyTime encode (fun a => (f a).take 1) :=
  (isPolyTime_head wordEncoding).comp hf

/-- Decode an efficient algorithm's answer as its first bit, with a fixed fallback. -/
theorem IsPolyTime.headD {f : α → Word} (hf : IsPolyTime encode f) (fallback : Bool) :
    IsPolyTime encode (fun a => [(f a).headD fallback]) :=
  (isPolyTime_headD wordEncoding fallback).comp hf

/-- Take a prefix of an efficiently computed word using a fixed bit predicate. -/
theorem IsPolyTime.takeWhile {f : α → Word} (hf : IsPolyTime encode f) (p : Bool → Bool) :
    IsPolyTime encode (fun a => (f a).takeWhile p) :=
  (isPolyTime_takeWhile wordEncoding p).comp hf

/-- Drop a prefix of an efficiently computed word using a fixed bit predicate. -/
theorem IsPolyTime.dropWhile {f : α → Word} (hf : IsPolyTime encode f) (p : Bool → Bool) :
    IsPolyTime encode (fun a => (f a).dropWhile p) :=
  (isPolyTime_dropWhile wordEncoding p).comp hf

end Cslib.Probability
