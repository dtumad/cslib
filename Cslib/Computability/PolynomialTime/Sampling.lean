/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.UniformBits

/-! # Uniform polynomial-time binary sampling -/

public section

namespace Turing.MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory MultiTapeTM

variable {Oracle : Type} [DecidableEq Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- The sampling machine has the same joint result-and-state measure as independent fair bits.
In particular, it neither calls nor modifies any of the shared oracle operations. -/
theorem runKernel_uniformBitsMachine {S : Type} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S)) (n : ℕ) (input : Word) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      (uniformBitsMachine.run (n + 1) (parameterInput n input)) state =
      FreeM.runKernel (effectKernel oracle)
        (some <$> (List.replicate n ()).mapM (fun _ => coin)) state := by
  rw [run_uniformBitsMachine, map_eq_pure_bind]
  conv_lhs => rw [← FreeM.bind_eq_bind, FreeM.runKernel_bind]
  conv_rhs => rw [← FreeM.bind_eq_bind, FreeM.runKernel_bind]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall fun out => runKernel_coin_const oracle _ out.2

/-- One state and a linear pathwise clock implement all binary sample lengths. -/
theorem isPPT_sampleBits [Finite Oracle] :
    IsPPT parameterEncoding wordEncoding
      (fun input => (List.replicate input.1 ()).mapM (fun _ => coin (Oracle := Oracle))) := by
  refine ⟨inferInstance, 0, Fin 1, inferInstance, uniformBitsMachine, 1, 1, fun ⟨n, input⟩ => ?_⟩
  have hhalt := haltsWithin_uniformBitsMachine (Oracle := Oracle) n input
  have htime : n + 1 ≤ 1 * ((parameterInput n input).length + 1) ^ 1 := by simp; omega
  refine ⟨hhalt.mono htime, Realizes.mono ?_ hhalt htime⟩
  intro S _ _ _ oracle state
  simpa only [wordEncoding, Function.Embedding.refl_apply, parameterEncoding_apply] using
    runKernel_uniformBitsMachine oracle n input state

end Turing.MultiTapePTM
