/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Realization.Composition
public import Cslib.Computability.Probabilistic.Parameter

/-!
# Efficient sequencing and deterministic processing of probabilistic programs

`IsPPT.bind` passes an intermediate word to the next program and retains the security parameter.
`IsPPT.map_word` and `IsPPT.preprocess_word` use ordinary deterministic efficiency certificates
to process a result or prepare an argument. Machine implementations and their resource proofs
live in `Cslib.Computability.Probabilistic.Realization.Composition`.
-/

@[expose] public section

namespace Cslib.Probability

/-- Efficient deterministic postprocessing of a PPT word-valued program preserves PPT. -/
theorem IsPPT.map_word {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp Word} {f : Word → α}
    (hprogram : IsPPT wordEncoding program)
    (hf : IsPolyTime wordEncoding (fun word => encode (f word))) :
    IsPPT encode (fun n input => f <$> program n input) := by
  simpa using hprogram.bind hf.isPPT_word

/-- Prepare a PPT program's input with an efficient deterministic word algorithm. -/
theorem IsPPT.preprocess_word {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} {prepare : Word → Word}
    (hprogram : IsPPT encode program) (hprepare : IsPolyTime wordEncoding prepare) :
    IsPPT encode (fun n input => program n (prepare input)) := by
  simpa using hprepare.isPPT_word.bind hprogram

end Cslib.Probability
