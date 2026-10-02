/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Composition

/-!
# Efficient input preparation

Appending a fixed bit to a PPT adversary's input preserves PPT. The proof composes the public
parameter, input, constant, and concatenation rules; their implementations account for preparing
the argument and starting the adversary on it.
-/

@[expose] public section

namespace Cslib.Probability

/-- Append one bit to the auxiliary input and retain the original security parameter. -/
theorem isPPT_snoc_parameter (bit : Bool) :
    IsPPT parameterEncoding (fun n input => pure (n, input ++ [bit])) :=
  (isPolyTime_security.parameterInput
    (isPolyTime_auxiliaryInput.append (isPolyTime_const parameterEncoding [bit]))).isPPT

/-- A fixed appended challenge bit has a uniform PPT input-preparation routine. -/
theorem IsPPT.snoc_input {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) (bit : Bool) :
    IsPPT encode (fun n input => program n (input ++ [bit])) := by
  simpa only [pure_bind] using (isPPT_snoc_parameter bit).bind_parameter h

end Cslib.Probability
