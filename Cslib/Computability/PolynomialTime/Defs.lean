/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Uniform deterministic polynomial time

A function `f : α → Word` is computable in polynomial time from an encoding of its inputs as binary
words (`IsPolyTime`) if a single finite-control multi-tape machine computes it on every input
within `c * (n + 1) ^ d` transitions, where `n` is the length of the encoded input. This is the
polynomial case of `ComputableInTimeAndSpace` (`IsPolyTime.computableInTimeAndSpace`,
`isPolyTime_of_computableInTimeAndSpace`).

Algorithms indexed by a security parameter `n` read it in unary, followed by a delimiter and their
remaining input (`parameterEncoding`), so a polynomial bound in the input length is polynomial in
`n` and the length of the remaining input.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Binary words, the inputs and outputs of machines. -/
abbrev Word := List Bool

/-- A security parameter in unary, a delimiter, and then the remaining input. -/
def parameterInput (security : ℕ) (input : Word) : Word :=
  List.replicate security true ++ false :: input

@[simp]
theorem length_parameterInput (security : ℕ) (input : Word) :
    (parameterInput security input).length = security + input.length + 1 := by
  simp [parameterInput, Nat.add_assoc]

@[simp]
theorem parameterInput_inj {n m : ℕ} {input input' : Word} :
    parameterInput n input = parameterInput m input' ↔ n = m ∧ input = input' := by
  induction n generalizing m with
  | zero => cases m <;> simp [parameterInput, List.replicate_succ]
  | succ n ih =>
    cases m with
    | zero => simp [parameterInput, List.replicate_succ]
    | succ m => simpa [parameterInput, List.replicate_succ] using ih (m := m)

/-- Binary words encode themselves. -/
def wordEncoding : Word ↪ Word := Function.Embedding.refl _

/-- The encoding of a security parameter together with the remaining input. -/
def parameterEncoding : (ℕ × Word) ↪ Word where
  toFun pair := parameterInput pair.1 pair.2
  inj' := by
    rintro ⟨n, input⟩ ⟨m, input'⟩ h
    obtain ⟨rfl, rfl⟩ := parameterInput_inj.mp h
    rfl

@[simp]
theorem parameterEncoding_apply (input : ℕ × Word) :
    parameterEncoding input = parameterInput input.1 input.2 := rfl

/-- A Boolean is encoded by a single bit. -/
def boolEncoding : Bool ↪ Word := ⟨fun b => [b], by intro a b h; simpa using h⟩

@[simp]
theorem boolEncoding_apply (b : Bool) : boolEncoding b = [b] := rfl

/-- `f` is computed from the encoding `encode` of its inputs by one finite-control machine
within `c * (n + 1) ^ d` transitions on inputs whose encoding has length `n`. -/
def IsPolyTime {α : Type} (encode : α → Word) (f : α → Word) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM k Bool State) (c d : ℕ),
    ∀ a, let cfg := machine.runFrom (machine.initCfg (encode a)) (c * ((encode a).length + 1) ^ d)
      cfg.state = none ∧ cfg.output = f a

/-- The output of a polynomial-time function has polynomial length. -/
theorem IsPolyTime.length_le {α : Type} {encode : α → Word} {f : α → Word}
    (h : IsPolyTime encode f) : ∃ c d : ℕ, ∀ a, (f a).length ≤ c * ((encode a).length + 1) ^ d := by
  obtain ⟨k, State, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  have := machine.length_output_runFrom_le (machine.initCfg (encode a))
    (c * ((encode a).length + 1) ^ d)
  rw [(h a).2] at this
  simpa using this

/-- A polynomial-time function is computable in polynomial time and space. -/
theorem IsPolyTime.computableInTimeAndSpace {α : Type} {encode : α ↪ Word} {f : α → Word}
    (h : IsPolyTime encode f) :
    ∃ c d s : ℕ, ComputableInTimeAndSpace f encode wordEncoding
      (fun a => c * ((encode a).length + 1) ^ d)
      (fun a => s * (((encode a).length + 1) ^ d + 1)) := by
  obtain ⟨k, State, _, machine, c, d, h⟩ := h
  refine ⟨c, d, k * (c + 1), k, State, inferInstance, machine, fun a => ?_⟩
  refine ⟨c * ((encode a).length + 1) ^ d, le_rfl,
    machine.spaceUsed (machine.initCfg (encode a)) (c * ((encode a).length + 1) ^ d), ?_,
    (h a).1, (h a).2, rfl⟩
  apply (machine.spaceUsed_linear _ _).trans
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, ← Nat.mul_assoc]
  omega

/-- A function computable within a polynomial time bound is polynomial-time, whatever the space
bound. -/
theorem isPolyTime_of_computableInTimeAndSpace {α : Type} {encode : α ↪ Word} {f : α → Word}
    {c d : ℕ} {space : α → ℕ}
    (h : ComputableInTimeAndSpace f encode wordEncoding
      (fun a => c * ((encode a).length + 1) ^ d) space) : IsPolyTime encode f := by
  obtain ⟨k, State, _, machine, h⟩ := h
  refine ⟨k, State, inferInstance, machine, c, d, fun a => ?_⟩
  obtain ⟨time, htime, _, _, hhalt, hout, _⟩ := h a
  rw [machine.runFrom_eq_of_halt _ htime hhalt]
  exact ⟨hhalt, hout⟩

end Turing.MultiTapeTM
