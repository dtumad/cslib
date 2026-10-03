/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Computability.Probabilistic.Composition

/-!
# Efficient postprocessing reductions

Computational indistinguishability is preserved by a uniform PPT continuation, including one
that uses the security parameter. The proof explicitly composes that continuation with the
distinguisher. Neither input ensemble needs to be efficiently sampled.
-/

@[expose] public section

namespace Cslib.Crypto.ComputationallyIndistinguishable

open Probability

/-- A uniform PPT continuation preserves computational indistinguishability. -/
theorem bind {X Y : ℕ → PMF Word} (h : ComputationallyIndistinguishable X Y)
    (program : ℕ → Word → ProbComp Word) (hprogram : IsPPT wordEncoding program) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun word => ProbComp.eval (program n word)))
      (fun n => (Y n).bind (fun word => ProbComp.eval (program n word))) := by
  intro adversary hadversary
  have hreduce := h (fun n word => program n word >>= adversary n) (hprogram.bind hadversary)
  simpa only [distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample, PMF.bind_bind]
    using hreduce

/-- An efficiently computed, parameter-dependent map preserves indistinguishability. -/
theorem map {X Y : ℕ → PMF Word} (h : ComputationallyIndistinguishable X Y)
    (f : ℕ → Word → Word)
    (hf : IsPolyTime parameterEncoding (fun input => f input.1 input.2)) :
    ComputationallyIndistinguishable (fun n => (X n).map (f n))
      (fun n => (Y n).map (f n)) := by
  have hp : IsPPT wordEncoding (fun n word => pure (f n word)) :=
    IsPolyTime.isPPT (encode := wordEncoding) (f := f) (by simpa [wordEncoding] using hf)
  simpa only [ProbComp.eval_pure, PMF.map, Function.comp_def] using
    h.bind (fun n word => pure (f n word)) hp

end Cslib.Crypto.ComputationallyIndistinguishable
