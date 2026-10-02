/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Concat
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RestoreWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeCall
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Deterministic polynomial-time constructions

Two polynomial-time functions on the same encoded input can have their outputs concatenated.
The shared `MultiTapeTM.concat` construction gives each machine fresh work tapes, preserves
accumulated output and charges for restoring the input head before the second computation.
The finite machine and the polynomial bound remain independent of the input.

`IsPolyTime.exists_restoring_machine` additionally makes any polynomial-time computation
reusable: its result is appended to the current output, and all scratch tapes and heads are
restored before it halts. The compiler's complete overhead is linear in the original runtime
and input length.

`IsPolyTime.exists_tape_machine` buffers both the argument and result for calls inside loops.
The bounded-iteration closure theorem is in `Cslib.Computability.Probabilistic.Iteration`.
-/

@[expose] public section

namespace Cslib.Probability

open Turing Turing.MultiTapeTM

/-- Compute two functions of the same input and concatenate their outputs in polynomial time. -/
theorem IsPolyTime.append {α : Type} {encode : α → Word} {f g : α → Word}
    (hf : IsPolyTime encode f) (hg : IsPolyTime encode g) :
    IsPolyTime encode (fun a => f a ++ g a) := by
  obtain ⟨k₀, states₀, tm₀, c₀, d₀, h₀⟩ := hf
  obtain ⟨k₁, states₁, tm₁, c₁, d₁, h₁⟩ := hg
  have hpoly : PolynomiallyBounded (fun length =>
      c₀ * (length + 1) ^ d₀ + c₁ * (length + 1) ^ d₁ + length + 2) := by fun_prop
  obtain ⟨c, d, hbound⟩ := hpoly
  apply isPolyTime_of_finite_machine (tm₀.concat tm₁) c d
  intro a
  have hrun := runFrom_concat tm₀ tm₁ (h₀ a).1 (h₀ a).2 (h₁ a).1 (h₁ a).2
  rw [runFrom_eq_of_halt _ _ (hbound (encode a).length) hrun.1]
  exact hrun

/-- Every polynomial-time function has a finite machine that appends its result and restores
all work tapes and heads, with one polynomial bound across all inputs and output prefixes. -/
theorem IsPolyTime.exists_restoring_machine {α : Type} {encode : α → Word} {f : α → Word}
    (h : IsPolyTime encode f) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM k Bool State) (c d : ℕ),
      ∀ a output,
        machine.runFrom (wordsCfg (encode a) (some machine.q₀) (fun _ => []) output)
          (c * ((encode a).length + 1) ^ d) =
          wordsCfg (encode a) none (fun _ => []) (output ++ f a) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h
  have hpoly : PolynomiallyBounded (fun length => 7 * (c * (length + 1) ^ d) + length + 9) := by
    fun_prop
  obtain ⟨coefficient, degree, hbound⟩ := hpoly
  refine ⟨k + k, _, inferInstance, machine.restoreWork, coefficient, degree, ?_⟩
  intro a output
  have hrun := runFrom_restoreWork_output machine (c * ((encode a).length + 1) ^ d)
    (hmachine a).1 output
  rw [(hmachine a).2] at hrun
  rw [runFrom_eq_of_halt _ _ (hbound (encode a).length) (by rw [hrun]; rfl)]
  exact hrun

/-- A polynomial-time function can be called on a work-tape word. Its input is preserved, its
result is buffered, and all scratch tapes and heads return to normal form. The clock depends
only on the encoded argument, independently of the ambient input and output. -/
theorem IsPolyTime.exists_tape_machine {α : Type} {encode : α → Word} {f : α → Word}
    (h : IsPolyTime encode f) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (machine : MultiTapeTM (k + 3) Bool State) (c d : ℕ),
      ∀ a outerInput output,
        machine.runFrom
          (wordsCfg outerInput (some machine.q₀) (TapeCall.words k (encode a) []) output)
          (c * ((encode a).length + 1) ^ d) =
          wordsCfg outerInput none (TapeCall.words k (encode a) (f a)) output := by
  obtain ⟨k, State, hfinite, machine, c, d, hmachine⟩ := h.exists_restoring_machine
  let : Finite State := hfinite
  refine ⟨k, _, inferInstance, machine.tapeCall, 2 * c + 6, d, ?_⟩
  intro a outerInput output
  have hresult :
      machine.runFrom (wordsCfg (encode a) (some machine.q₀) (fun _ => []) [])
        (c * ((encode a).length + 1) ^ d) =
        wordsCfg (encode a) none (fun _ => []) (f a) := by
    simpa only [List.nil_append] using hmachine a []
  have hlength := machine.length_output_runFrom_le
    (wordsCfg (encode a) (some machine.q₀) (fun _ => []) [])
    (c * ((encode a).length + 1) ^ d)
  rw [hresult] at hlength
  simp only [wordsCfg_output, List.length_nil, Nat.zero_add] at hlength
  have hbound :
      c * ((encode a).length + 1) ^ d + (f a).length + 6 ≤
        (2 * c + 6) * ((encode a).length + 1) ^ d := by
    have hp : 0 < ((encode a).length + 1) ^ d := by positivity
    nlinarith
  have hrun := runFrom_tapeCall (outerInput := outerInput) machine (encode a) (f a) output
    (c * ((encode a).length + 1) ^ d) hresult
  rw [runFrom_eq_of_halt _ _ hbound (by rw [hrun]; rfl)]
  exact hrun

end Cslib.Probability
