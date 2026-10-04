/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Relabel
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Basic.Finite.Sum

/-!
# Uniform deterministic polynomial time

A certificate gives one finite-control binary machine and a polynomial clock for all encoded
inputs. The input encoding is fixed by the caller. Local computation and writing the encoded
output are charged by the existing multi-tape transition semantics.

Adapted from Samuel Schlesinger's crypto branch. This layer has no probabilistic imports.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Binary words used at the machine boundary. -/
abbrev Word := List Bool

/-- Unary security parameter, a zero delimiter, then the auxiliary input. -/
def parameterInput (security : ℕ) (input : Word) : Word :=
  List.replicate security true ++ false :: input

@[simp] theorem length_parameterInput (security : ℕ) (input : Word) :
    (parameterInput security input).length = security + input.length + 1 := by
  simp [parameterInput, Nat.add_assoc]

/-- The delimiter makes both the security parameter and auxiliary input recoverable. -/
@[simp] theorem parameterInput_inj {n m : ℕ} {input input' : Word} :
    parameterInput n input = parameterInput m input' ↔ n = m ∧ input = input' := by
  induction n generalizing m with
  | zero => cases m <;> simp [parameterInput, List.replicate_succ]
  | succ n ih =>
    cases m with
    | zero => simp [parameterInput, List.replicate_succ]
    | succ m => simpa [parameterInput, List.replicate_succ] using (ih (m := m))

/-- The identity encoding of binary words. -/
def wordEncoding : Word ↪ Word := Function.Embedding.refl _

/-- The machine input encoding for an algorithm with a security parameter and auxiliary input. -/
def parameterEncoding : (ℕ × Word) ↪ Word where
  toFun pair := parameterInput pair.1 pair.2
  inj' := by
    rintro ⟨n, input⟩ ⟨m, input'⟩ h
    obtain ⟨rfl, rfl⟩ := parameterInput_inj.mp h
    rfl

@[simp] theorem parameterEncoding_apply (input : ℕ × Word) :
    parameterEncoding input = parameterInput input.1 input.2 := rfl

/-- A Boolean is represented by its single bit. -/
def boolEncoding : Bool ↪ Word := ⟨fun b => [b], by intro a b h; simpa using h⟩

/-- A uniform deterministic machine computes `f` from an explicit binary encoding, with a
polynomial bound on every input. The finite control and polynomial are independent of the input. -/
def IsPolyTime {α : Type} (encode : α → Word) (f : α → Word) : Prop :=
  ∃ (k states : ℕ) (machine : Turing.MultiTapeTM k Bool (Fin states)) (c d : ℕ),
    ∀ a, let cfg := machine.runFrom (machine.initCfg (encode a)) (c * ((encode a).length + 1) ^ d)
      cfg.state = none ∧ cfg.output = f a

/-- A deterministic certificate may use any finite control type. Relabelling supplies the
canonical `Fin` presentation without changing execution time or output. -/
theorem isPolyTime_of_finite_machine {α State : Type} [Finite State] {k : ℕ}
    {encode : α → Word} {f : α → Word} (machine : Turing.MultiTapeTM k Bool State) (c d : ℕ)
    (h : ∀ a,
      let cfg := machine.runFrom (machine.initCfg (encode a))
        (c * ((encode a).length + 1) ^ d)
      cfg.state = none ∧ cfg.output = f a) : IsPolyTime encode f := by
  classical
  let := Fintype.ofFinite State
  refine ⟨k, Fintype.card State, machine.relabel (Fintype.equivFin State), c, d, ?_⟩
  intro a
  simp only [Turing.MultiTapeTM.initCfg_relabel, Turing.MultiTapeTM.runFrom_relabel,
    Turing.Cfg.relabel_state, Turing.Cfg.relabel_output]
  exact ⟨congrArg (Option.map (Fintype.equivFin State)) (h a).1, (h a).2⟩

/-- Polynomial time also bounds the size of an explicitly written output. -/
theorem IsPolyTime.length_le {α : Type} {encode : α → Word} {f : α → Word}
    (h : IsPolyTime encode f) : ∃ c d : ℕ, ∀ a, (f a).length ≤ c * ((encode a).length + 1) ^ d := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  have hout := machine.length_output_runFrom_le (machine.initCfg (encode a))
    (c * ((encode a).length + 1) ^ d)
  rw [(h a).2] at hout
  simpa using hout

/-- The polynomial-time certificate specializes the existing time-and-space contract.
Work space is bounded by the number of visited cells on the finitely many tapes. -/
theorem IsPolyTime.computableInTimeAndSpace {α : Type} {encode : α ↪ Word} {f : α → Word}
    (h : IsPolyTime encode f) :
    ∃ c d s : ℕ, ComputableInTimeAndSpace f encode wordEncoding
      (fun a => c * ((encode a).length + 1) ^ d)
      (fun a => s * (((encode a).length + 1) ^ d + 1)) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, k * (c + 1), k, Fin states, inferInstance, machine, fun a => ?_⟩
  refine ⟨c * ((encode a).length + 1) ^ d, le_rfl,
    machine.spaceUsed (machine.initCfg (encode a)) (c * ((encode a).length + 1) ^ d), ?_,
    (h a).1, (h a).2, rfl⟩
  apply (machine.spaceUsed_linear _ _).trans
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, ← Nat.mul_assoc]
  omega

/-- A polynomial clock in the existing computability predicate gives a uniform certificate;
the supplied space bound is immaterial to this implication. -/
theorem isPolyTime_of_computableInTimeAndSpace {α : Type} {encode : α ↪ Word} {f : α → Word}
    {c d : ℕ} {space : α → ℕ}
    (h : ComputableInTimeAndSpace f encode wordEncoding
      (fun a => c * ((encode a).length + 1) ^ d) space) : IsPolyTime encode f := by
  obtain ⟨k, State, hfinite, machine, h⟩ := h
  let : Finite State := hfinite
  apply isPolyTime_of_finite_machine machine c d
  intro a
  obtain ⟨time, htime, _, _, hhalt, hout, _⟩ := h a
  rw [machine.runFrom_eq_of_halt _ htime hhalt]
  exact ⟨hhalt, hout⟩

end Turing.MultiTapeTM
