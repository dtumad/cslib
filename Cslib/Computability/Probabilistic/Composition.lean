/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.Composition
public import Cslib.Computability.Probabilistic.Parameter
public import Cslib.Computability.Probabilistic.Encoding

/-!
# Efficient sequencing and deterministic processing of probabilistic programs

`IsPPTOn.bind` and `map` compose programs with encoded input and result types. Their `_with`
variants retain the caller's input for a captured continuation or callback. `preprocess` prepares
arguments, and `ite` selects between closed probabilistic programs. All copying and intermediate
output sizes contribute to the polynomial bound.

The `IsPPT` specializations retain the unary security parameter automatically. Machine
implementations and resource proofs live in `Realization.Composition`; the public combinators
share those realizations.
-/

@[expose] public section

namespace Cslib.Probability

/-- Prepare an encoded argument before running a typed probabilistic program. -/
theorem IsPPTOn.preprocess {α β γ : Type} {input : α → Word} {middle : β ↪ Word}
    {output : γ ↪ Word} {program : β → ProbComp γ} {prepare : α → β}
    (hprogram : IsPPTOn middle output program)
    (hprepare : IsPolyTime input (fun a => middle (prepare a))) :
    IsPPTOn input output (fun a => program (prepare a)) := by
  simpa using hprepare.isPPTOn.bind hprogram

/-- Call a certified two-argument probabilistic program on efficiently prepared values. -/
theorem IsPPTOn.preprocess_pair {α β γ δ : Type} {input : α → Word}
    {left : β ↪ Word} {right : γ ↪ Word} {output : δ ↪ Word}
    {program : β → γ → ProbComp δ} {f : α → β} {g : α → γ}
    (hprogram : IsPPTOn (pairEncoding left right) output (fun pair => program pair.1 pair.2))
    (hf : IsPolyTime input (fun a => left (f a)))
    (hg : IsPolyTime input (fun a => right (g a))) :
    IsPPTOn input output (fun a => program (f a) (g a)) :=
  hprogram.preprocess (prepare := fun a => (f a, g a)) (hf.pair hg)

/-- Map a certified deterministic function over any encoded probabilistic result. -/
theorem IsPPTOn.map {α β γ : Type} {input : α → Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : α → ProbComp β} {f : β → γ} (hprogram : IsPPTOn input middle program)
    (hf : IsPolyTime middle (fun b => output (f b))) :
    IsPPTOn input output (fun a => f <$> program a) := by
  simpa using hprogram.bind hf.isPPTOn

/-- Retain efficiently computed runtime data alongside a probabilistic result. -/
theorem IsPPTOn.pair {α β γ : Type} {input : α → Word} {left : β ↪ Word} {right : γ ↪ Word}
    {program : α → ProbComp γ} {f : α → β} (hprogram : IsPPTOn input right program)
    (hf : IsPolyTime input (fun a => left (f a))) :
    IsPPTOn input (pairEncoding left right) (fun a => (fun b => (f a, b)) <$> program a) := by
  apply IsPPTOn.of_encoded
  refine (hprogram.encoded.prefix
    ((hf.flatMap (fun bit => [true, bit])).append (isPolyTime_const input [false]))).congr ?_
  intro a
  simp [ProbComp.eval_map, pairEncoding, List.BitPair.encode, List.BitPair.tagged,
    List.append_assoc]

/-- Keep the caller's input available to a later computation. Copying its encoding is charged. -/
theorem IsPPTOn.keep_input {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {program : α → ProbComp β} (hprogram : IsPPTOn input output program) :
    IsPPTOn input (pairEncoding input output) (fun a => (fun b => (a, b)) <$> program a) :=
  hprogram.pair (isPolyTime_input input)

/-- A probabilistic continuation may capture the caller's input as well as the sampled result. -/
theorem IsPPTOn.bind_with {α β γ : Type} {input : α ↪ Word} {middle : β ↪ Word}
    {output : γ ↪ Word} {first : α → ProbComp β} {second : α → β → ProbComp γ}
    (hfirst : IsPPTOn input middle first)
    (hsecond : IsPPTOn (pairEncoding input middle) output (fun pair => second pair.1 pair.2)) :
    IsPPTOn input output (fun a => do
      let b ← first a
      second a b) := by
  simpa only [bind_map_left] using hfirst.keep_input.bind hsecond

/-- A deterministic callback may capture input data while mapping a probabilistic result. -/
theorem IsPPTOn.map_with {α β γ : Type} {input : α ↪ Word} {middle : β ↪ Word}
    {output : γ ↪ Word} {program : α → ProbComp β} {f : α → β → γ}
    (hprogram : IsPPTOn input middle program)
    (hf : IsPolyTime (pairEncoding input middle) (fun pair => output (f pair.1 pair.2))) :
    IsPPTOn input output (fun a => f a <$> program a) := by
  simpa using hprogram.bind_with (output := output) (second := fun a b => pure (f a b)) hf.isPPTOn

/-- Select a closed probabilistic branch with an efficiently computed condition. The proof may
run both total programs and discard one result; their sum is still a polynomial bound. -/
theorem IsPPTOn.ite {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {condition : α → Prop} [∀ a, Decidable (condition a)] {yes no : α → ProbComp β}
    (hcondition : IsPolyTime input (fun a => [decide (condition a)]))
    (hyes : IsPPTOn input output yes) (hno : IsPPTOn input output no) :
    IsPPTOn input output (fun a => if condition a then yes a else no a) := by
  have hno' : IsPPTOn (pairEncoding input output) output (fun pair => no pair.1) :=
    hno.preprocess (isPolyTime_fst input output)
  have hselect : IsPolyTime (pairEncoding (pairEncoding input output) output)
      (fun pair => output (if condition pair.1.1 then pair.1.2 else pair.2)) := by
    have hinput := (isPolyTime_fst (pairEncoding input output) output).fst
    simpa only [apply_ite] using (hcondition.comp_encoded hinput).ite
      (isPolyTime_fst (pairEncoding input output) output).snd
      (isPolyTime_snd (pairEncoding input output) output)
  have hcombined : IsPPTOn input output (fun a => do
    let b ← yes a
    (fun c => if condition a then b else c) <$> no a) :=
    hyes.bind_with (second := fun a b => (fun c => if condition a then b else c) <$> no a)
      (hno'.map_with (output := output) hselect)
  apply hcombined.congr
  intro a
  by_cases ha : condition a <;>
    simp [ha, ProbComp.eval_bind, ProbComp.eval_map, PMF.map, Function.comp_def]

/-- A Boolean flag selects between certified probabilistic branches. -/
theorem IsPPTOn.cond {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {condition : α → Bool} {yes no : α → ProbComp β}
    (hcondition : IsPolyTime input (fun a => [condition a]))
    (hyes : IsPPTOn input output yes) (hno : IsPPTOn input output no) :
    IsPPTOn input output (fun a => if condition a then yes a else no a) := by
  exact IsPPTOn.ite (by simpa using hcondition) hyes hno

/-- Call a certified cryptographic program with an efficiently prepared parameter and input. -/
theorem IsPPT.preprocess {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : ℕ → Word → ProbComp β} {parameter : α → ℕ} {word : α → Word}
    (hprogram : IsPPT output program)
    (hparameter : IsPolyTime input (fun a => List.replicate (parameter a) true))
    (hword : IsPolyTime input word) :
    IsPPTOn input output (fun a => program (parameter a) (word a)) :=
  hprogram.on.preprocess (prepare := fun a => (parameter a, word a))
    (hparameter.parameterInput hword)


/-- Retain the original security parameter beside a PPT program's result. -/
theorem IsPPT.keep_parameter {program : ℕ → Word → ProbComp Word}
    (h : IsPPT wordEncoding program) :
    IsPPT parameterEncoding (fun n input => (fun word => (n, word)) <$> program n input) := by
  apply IsPPTOn.isPPT
  apply IsPPTOn.of_encoded
  refine (h.on.prefix (isPolyTime_security.append
    (isPolyTime_const parameterEncoding [false]))).congr ?_
  rintro ⟨n, input⟩
  simp [ProbComp.eval_map, parameterEncoding, parameterInput, List.append_assoc]

/-- A PPT program may return the encoded parameter and input of another PPT program. -/
theorem IsPPT.bind_parameter {α : Type} {encode : α ↪ Word}
    {first : ℕ → Word → ProbComp (ℕ × Word)} {second : ℕ → Word → ProbComp α}
    (hfirst : IsPPT parameterEncoding first) (hsecond : IsPPT encode second) :
    IsPPT encode (fun n input => do
      let (nextParameter, nextInput) ← first n input
      second nextParameter nextInput) := (hfirst.on.bind hsecond.on).isPPT

/-- Run a PPT word-valued program, then pass its result to another PPT program at the same
security parameter. Both programs are realized by fixed machines; all handoff costs are charged. -/
theorem IsPPT.bind {α : Type} {encode : α ↪ Word}
    {first : ℕ → Word → ProbComp Word} {second : ℕ → Word → ProbComp α}
    (hfirst : IsPPT wordEncoding first) (hsecond : IsPPT encode second) :
    IsPPT encode (fun n input => do
      let word ← first n input
      second n word) := by
  simpa only [bind_map_left] using hfirst.keep_parameter.bind_parameter hsecond

/-- Efficient deterministic postprocessing of a PPT word-valued program preserves PPT. -/
theorem IsPPT.map_word {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp Word} {f : Word → α}
    (hprogram : IsPPT wordEncoding program)
    (hf : IsPolyTime wordEncoding (fun word => encode (f word))) :
    IsPPT encode (fun n input => f <$> program n input) := by
  exact (hprogram.on.map hf).isPPT

/-- Prepare a PPT program's input with an efficient deterministic word algorithm. -/
theorem IsPPT.preprocess_word {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} {prepare : Word → Word}
    (hprogram : IsPPT encode program) (hprepare : IsPolyTime wordEncoding prepare) :
    IsPPT encode (fun n input => program n (prepare input)) := by
  simpa using hprepare.isPPT_word.bind hprogram

end Cslib.Probability
