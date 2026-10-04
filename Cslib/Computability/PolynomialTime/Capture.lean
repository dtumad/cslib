/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Composition
public import Cslib.Computability.PolynomialTime.Encoding
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.OutputPrefix

/-!
# Retaining input data across probabilistic calls

An initializer writes retained data and restores its work tapes before the probabilistic call.
The resulting certificate charges for both computations. Pairing with retained input then gives
captured continuations using ordinary monadic bind.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeTM MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β γ : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Viewing a result through its encoding changes no machine or clock. -/
theorem isPPT_map_encoding_iff {input : α ↪ Word} {output : β ↪ Word}
    {program : α → (effects Oracle).FreeM β} :
    IsPPT input wordEncoding (fun a => output <$> program a) ↔ IsPPT input output program := by
  simp only [IsPPT, Realizes, wordEncoding, Function.Embedding.refl_apply,
    ← comp_map, Function.comp_def]

/-- Write an efficiently computed prefix, restore the workspace, and run the source program. -/
theorem IsPPT.prefix {input : α ↪ Word} {output : β ↪ Word} {pre : α → Word}
    {program : α → (effects Oracle).FreeM β} (hprogram : IsPPT input output program)
    (hprefix : IsPolyTime input pre) :
    IsPPT input wordEncoding (fun a => (fun value => pre a ++ output value) <$> program a) := by
  obtain ⟨ki, InitState, hfinite, initializer, ci, di, hi⟩ := hprefix.exists_restoring_machine
  let : Finite InitState := hfinite
  obtain ⟨horacle, ks, ports, RunState, hfinite, source, dispatch, cs, ds, hs⟩ := hprogram
  let : Finite RunState := hfinite
  let prep := initializer.extendTapes (Fin.castAddEmb ks)
  let runner := source.extendTapes (Fin.natAddEmb ki)
  let compiled := (ofDeterministic prep).seq runner
  let prepareTime (length : ℕ) := ci * (length + 1) ^ di
  let runTime (length : ℕ) := cs * (length + 1) ^ ds
  have hpoly : PolynomiallyBounded (fun length => prepareTime length + runTime length) := by
    fun_prop
  obtain ⟨coefficient, degree, htime⟩ := hpoly
  have hprep (a : α) :
      prep.runFrom (prep.initCfg (input a)) (prepareTime (input a).length) =
        wordsCfg (input a) none (fun _ => []) (pre a) := by
    change prep.runFrom (Cfg.init prep.q₀ (input a)) _ = _
    rw [Cfg.init_eq_wordsCfg]
    apply MultiTapeTM.runFrom_extendTapes_words
    · simpa [prepareTime, Function.comp_def] using hi a []
    · intro i _
      rfl
  let ready (a : α) : Config (ki + ks) Bool InitState (Fin ports) (input a) :=
    { tapes := wordsCfg (input a) none (fun _ => []) (pre a) }
  have hready (a : α) (final : Config (ki + ks) Bool InitState (Fin ports) (input a))
      (hfinal : MonadAttach.CanReturn ((ofDeterministic prep).runConfigFrom
        (prepareTime (input a).length) ((ofDeterministic prep).initialConfig (input a))) final) :
      final = ready a := by
    rw [canReturn_ofDeterministic _ _ _ _ hfinal]
    change ({ tapes := prep.runFrom (prep.initCfg (input a)) (prepareTime (input a).length) } :
      Config (ki + ks) Bool InitState (Fin ports) (input a)) = _
    rw [hprep]
  have hstart (a : α) : Sequential.start runner (ready a) =
      OutputPrefix.config (runner.initialConfig (input a)) (pre a) := by
    simp [Sequential.start, ready, initialConfig, OutputPrefix.config,
      Cfg.prependOutput, wordsCfg, Cfg.withState]
  have hrunner (a : α) : runner.HaltsWithin (runTime (input a).length)
      (OutputPrefix.config (runner.initialConfig (input a)) (pre a)) := by
    apply HaltsWithin.prefixOutput
    rw [initialConfig_extendTapes]
    exact (hs a).1.extendTapes _ _ _
  have hhalt (a : α) : compiled.HaltsWithin
      (prepareTime (input a).length + runTime (input a).length)
      (compiled.initialConfig (input a)) := by
    change ((ofDeterministic prep).seq runner).HaltsWithin
      (prepareTime (input a).length + runTime (input a).length)
      (Sequential.left runner ((ofDeterministic prep).initialConfig (input a)))
    apply HaltsWithin.seq
    · intro final hfinal
      rw [hready a final hfinal]
      rfl
    · intro final hfinal
      rw [hready a final hfinal, hstart]
      exact hrunner a
  refine ⟨horacle, ki + ks, ports, InitState ⊕ RunState, inferInstance,
    compiled, dispatch, coefficient, degree, fun a => ?_⟩
  refine ⟨(hhalt a).mono (htime (input a).length),
    Realizes.mono ?_ (hhalt a) (htime (input a).length)⟩
  intro S _ _ _ oracle state
  change FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
    (output? <$> compiled.runConfigFrom _
      (Sequential.left runner ((ofDeterministic prep).initialConfig (input a)))) state = _
  rw [runConfigFrom_seq _ _ (prepareTime (input a).length) (runTime (input a).length) _
    (by intro final hfinal; rw [hready a final hfinal]; rfl)
    (by intro final hfinal; rw [hready a final hfinal, hstart]; exact hrunner a)]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  rw [runKernel_bind_ofDeterministic]
  change FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
    ((runner.runConfigFrom _ (Sequential.start runner
      { tapes := prep.runFrom (prep.initCfg (input a)) (prepareTime (input a).length) })) >>=
        fun final => pure (output? (Sequential.right final))) state = _
  rw [hprep]
  change FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
    ((runner.runConfigFrom _ (Sequential.start runner (ready a))) >>=
      fun final => pure (output? (Sequential.right final))) state = _
  simp only [Sequential.output?_right, ← map_eq_pure_bind]
  rw [hstart]
  change FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
    (runner.runFrom _ (OutputPrefix.config (runner.initialConfig (input a)) (pre a))) state = _
  rw [runFrom_prefixOutput, initialConfig_extendTapes, runFrom_embed]
  change FreeM.runKernel (effectKernel (fun port => oracle (dispatch port)))
    ((fun result => result.map (pre a ++ ·)) <$> source.run (runTime (input a).length) (input a))
      state = _
  conv_lhs => rw [← FreeM.map_eq_map, FreeM.runKernel_map]
  rw [(hs a).2 S oracle state]
  rw [← FreeM.runKernel_map]
  simp only [FreeM.map_eq_map, ← comp_map, Function.comp_def, Option.map_some,
    wordEncoding, Function.Embedding.refl_apply]

/-- Retain efficiently computed data alongside a probabilistic result. -/
theorem IsPPT.pair {input : α ↪ Word} {output : β ↪ Word} {environment : γ ↪ Word}
    {program : α → (effects Oracle).FreeM β} {env : α → γ}
    (hprogram : IsPPT input output program)
    (henv : IsPolyTime input (fun a => environment (env a))) :
    IsPPT input (pairEncoding environment output)
      (fun a => (fun value => (env a, value)) <$> program a) := by
  apply isPPT_map_encoding_iff.mp
  simpa only [← comp_map, Function.comp_def, pairEncoding, Function.Embedding.coeFn_mk,
    List.BitPair.encode, List.BitPair.tagged, List.append_assoc, List.singleton_append] using
    hprogram.prefix ((henv.flatMap (fun bit => [true, bit])).append
      (isPolyTime_const input [false]))

/-- An efficient continuation may depend on both the original input and the sampled value. -/
theorem IsPPT.bind_with {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → (effects Oracle).FreeM β} {second : α → β → (effects Oracle).FreeM γ}
    (hfirst : IsPPT input middle first)
    (hsecond : IsPPT (pairEncoding input middle) output (fun pair => second pair.1 pair.2)) :
    IsPPT input output (fun a => first a >>= second a) := by
  simpa only [bind_map_left] using (hfirst.pair (isPolyTime_input input)).bind hsecond

/-- Efficient deterministic postprocessing may retain the original input. -/
theorem IsPPT.map_with {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : α → (effects Oracle).FreeM β} {f : α → β → γ}
    (hprogram : IsPPT input middle program)
    (hf : IsPolyTime (pairEncoding input middle) (fun pair => output (f pair.1 pair.2))) :
    IsPPT input output (fun a => f a <$> program a) := by
  simpa only [← comp_map, Function.comp_def] using
    (hprogram.pair (isPolyTime_input input)).map hf

/-- Retain the input when the result type and its representation depend on that input. -/
theorem IsPPT.sigma {input : α ↪ Word} {β : α → Type} {output : ∀ a, β a ↪ Word}
    {program : ∀ a, (effects Oracle).FreeM (β a)}
    (hprogram : IsPPT input wordEncoding (fun a => output a <$> program a)) :
    IsPPT input (sigmaEncoding input output) (fun a => Sigma.mk a <$> program a) := by
  apply isPPT_map_encoding_iff.mp
  have h := isPPT_map_encoding_iff.mpr (hprogram.pair (isPolyTime_input input))
  simpa only [← comp_map, Function.comp_def, sigmaEncoding, pairEncoding,
    Function.Embedding.coeFn_mk, wordEncoding, Function.Embedding.refl_apply] using h

end Turing.MultiTapePTM
