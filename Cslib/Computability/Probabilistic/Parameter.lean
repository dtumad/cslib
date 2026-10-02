/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PolynomialTime

/-!
# Efficient access to a security parameter and auxiliary input

The public input representation is a unary parameter, a delimiter, and an arbitrary word.
Prefix operations recover both components. These certificates let reductions use the components
directly, and let deterministic word algorithms run inside probabilistic programs.
-/

@[expose] public section

namespace Cslib.Probability

@[simp] theorem takeWhile_parameterInput (n : ℕ) (input : Word) :
    (parameterInput n input).takeWhile id = List.replicate n true := by
  simp [parameterInput]

@[simp] theorem dropWhile_parameterInput (n : ℕ) (input : Word) :
    (parameterInput n input).dropWhile id = false :: input := by
  simp [parameterInput]

/-- Read the security parameter in unary. -/
theorem isPolyTime_security :
    IsPolyTime parameterEncoding (fun pair => List.replicate pair.1 true) := by
  simpa [parameterEncoding] using isPolyTime_takeWhile parameterEncoding id

/-- Read the auxiliary input, preserving every bit after the parameter delimiter. -/
theorem isPolyTime_auxiliaryInput : IsPolyTime parameterEncoding Prod.snd := by
  simpa [parameterEncoding] using (isPolyTime_dropWhile parameterEncoding id).tail

/-- Assemble an efficiently computed unary parameter and auxiliary input. -/
theorem IsPolyTime.parameterInput {α : Type} {encode : α → Word}
    {parameter : α → ℕ} {input : α → Word}
    (hparameter : IsPolyTime encode (fun a => List.replicate (parameter a) true))
    (hinput : IsPolyTime encode input) :
    IsPolyTime encode (fun a => parameterInput (parameter a) (input a)) :=
  hparameter.append ((isPolyTime_const encode [false]).append hinput)

/-- An efficient deterministic word algorithm is PPT when run on the auxiliary input.
The same algorithm works for every security parameter. -/
theorem IsPolyTime.isPPT_word {α : Type} {encode : α ↪ Word} {f : Word → α}
    (h : IsPolyTime wordEncoding (fun input => encode (f input))) :
    IsPPT encode (fun _ input => pure (f input)) :=
  (h.comp isPolyTime_auxiliaryInput).isPPT

end Cslib.Probability
