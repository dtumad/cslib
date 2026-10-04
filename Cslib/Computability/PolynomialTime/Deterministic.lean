/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic

/-! # Deterministic polynomial time implies probabilistic polynomial time -/

public section

namespace Turing.MultiTapeTM

open MultiTapePTM MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

/-- Reuse a deterministic machine certificate without changing its transition clock.
Its unused private coins have no effect on the result or the shared oracle state. -/
theorem IsPolyTime.isPPT {Oracle α β : Type} [DecidableEq Oracle] [Finite Oracle]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    {input : α ↪ Word} {output : β ↪ Word} {f : α → β}
    (h : IsPolyTime input (fun a => output (f a))) :
    IsPPT (Oracle := Oracle) input output (fun a => pure (f a)) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, Fin states, inferInstance, ofDeterministic machine, c, d, fun a => ?_⟩
  constructor
  · intro final hfinal
    have heq := canReturn_ofDeterministic machine _ _ final hfinal
    rw [heq]
    exact (h a).1
  · intro S _ _ _ oracle state
    change FreeM.runKernel (effectKernel oracle)
      (output? <$> (ofDeterministic machine).runConfigFrom _
        ((ofDeterministic machine).initialConfig (input a))) state = _
    rw [runKernel_ofDeterministic]
    simp only [map_pure, FreeM.runKernel_pure]
    congr 1
    change (output? {
      tapes := machine.runFrom (machine.initCfg (input a)) (c * ((input a).length + 1) ^ d)
      channels := fun _ => {} }, state) = _
    simp only [output?, (h a).1, (h a).2, Option.isNone_none, ↓reduceIte]

end Turing.MultiTapeTM
