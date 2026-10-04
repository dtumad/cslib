/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Support
public import Cslib.Computability.PolynomialTime.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Uniform polynomial-time sequencing

Composition uses the physical buffered-input compiler. Reachability reflection ensures that every
machine path produces a valid intermediate code, whose length is bounded by the source's clock.
Both subroutines use the same oracle environment, including its state across adaptive calls.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeTM MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β γ : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Uniform machine certificates compose, charging for the buffered input and its preparation. -/
theorem IsPPT.bind {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → (effects Oracle).FreeM β} {second : β → (effects Oracle).FreeM γ}
    (hfirst : IsPPT input middle first) (hsecond : IsPPT middle output second) :
    IsPPT input output (fun a => first a >>= second) := by
  obtain ⟨hfinite, k₀, ports₀, State₀, hstate₀, source, dispatch₀, c₀, d₀, hsource⟩ := hfirst
  obtain ⟨_, k₁, ports₁, State₁, hstate₁, target, dispatch₁, c₁, d₁, htarget⟩ := hsecond
  let : Finite State₀ := hstate₀
  let : Finite State₁ := hstate₁
  let : Countable β := middle.injective.countable
  let : MeasurableSpace β := ⊤
  let firstTime (length : ℕ) := c₀ * (length + 1) ^ d₀
  let secondTime (length : ℕ) := c₁ * (firstTime length + 1) ^ d₁
  have hpoly : PolynomiallyBounded
      (fun length => firstTime length + (firstTime length + 4 + secondTime length)) := by
    fun_prop
  obtain ⟨coefficient, degree, htime⟩ := hpoly
  have hbound (a : α) (value : β) (hvalue : MonadAttach.CanReturn (first a) value) :
      c₁ * ((middle value).length + 1) ^ d₁ ≤ secondTime (input a).length := by
    have hlength := length_of_canReturn_run source _ (input a) (middle value)
      ((hsource a).2.canReturn_iff.mpr ⟨value, hvalue, rfl⟩)
    exact Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right hlength 1) d₁)
  have hnext (a : α) (value : β) (hvalue : MonadAttach.CanReturn (first a) value) :
      target.HaltsWithin (secondTime (input a).length) (target.initialConfig (middle value)) ∧
        target.Realizes dispatch₁ (secondTime (input a).length)
          (middle value) output (second value) :=
    ⟨(htarget value).1.mono (hbound a value hvalue),
      (htarget value).2.mono (htarget value).1 (hbound a value hvalue)⟩
  have hnextMachine (a : α) (cfg : Config k₀ Bool State₀ (Fin ports₀) (input a))
      (hcfg : MonadAttach.CanReturn
        (source.runConfigFrom (firstTime (input a).length) (source.initialConfig (input a))) cfg) :
      target.HaltsWithin (secondTime (input a).length) (target.initialConfig cfg.tapes.output) := by
    have hword : MonadAttach.CanReturn (source.run (firstTime (input a).length) (input a))
        (some cfg.tapes.output) :=
      (FreeM.canReturn_map _ _ _).mpr ⟨cfg, hcfg, by simp [output?, (hsource a).1 cfg hcfg]⟩
    obtain ⟨value, hvalue, hencode⟩ := (hsource a).2.canReturn hword
    rw [← hencode]
    exact (hnext a value hvalue).1
  have hhalt (a : α) := (hsource a).1.comp (hnextMachine a)
  refine ⟨hfinite, k₁ + k₀ + 2, ports₀ + ports₁,
    State₀ ⊕ (MultiTapeTM.PrepareInput.Control ⊕ State₁), inferInstance,
    source.comp target, Fin.addCases dispatch₀ dispatch₁, coefficient, degree, fun a => ?_⟩
  refine ⟨(hhalt a).mono (htime (input a).length),
    Realizes.mono ?_ (hhalt a) (htime (input a).length)⟩
  intro S _ _ _ oracle state
  rw [runKernel_comp source target (input a) (firstTime (input a).length)
    (secondTime (input a).length) (hsource a).1 (hnextMachine a)]
  conv_lhs => rw [← FreeM.bind_eq_bind, FreeM.runKernel_bind, runKernel_liftM_rename]
  simp only [Fin.castAddEmb_apply, Fin.addCases_left]
  rw [(hsource a).2 S oracle state]
  conv_lhs =>
    rw [map_eq_pure_bind, ← FreeM.bind_eq_bind, FreeM.runKernel_bind]
    simp only [FreeM.runKernel_pure]
    rw [Measure.bind_bind Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable]
    simp only [Measure.dirac_bind Measurable.of_discrete]
  conv_rhs => rw [map_bind, ← FreeM.bind_eq_bind, FreeM.runKernel_bind]
  apply Measure.bind_congr_right
  filter_upwards [FreeM.runKernel_ae_canReturn (effectKernel oracle) (first a) state] with out hout
  rw [runKernel_liftM_rename]
  simpa only [Fin.natAddEmb_apply, Fin.addCases_right] using
    (hnext a out.1 hout).2 S oracle out.2

/-- An efficient deterministic function may process a probabilistic result. -/
theorem IsPPT.map {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : α → (effects Oracle).FreeM β} {f : β → γ}
    (hprogram : IsPPT input middle program)
    (hf : IsPolyTime middle (fun value => output (f value))) :
    IsPPT input output (fun a => f <$> program a) := by
  let : Finite Oracle := hprogram.1
  simpa only [← map_eq_pure_bind] using hprogram.bind hf.isPPT

/-- An efficient deterministic initializer may supply a probabilistic program's input. -/
theorem IsPPT.comp {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : β → (effects Oracle).FreeM γ} {f : α → β}
    (hprogram : IsPPT middle output program)
    (hf : IsPolyTime input (fun value => middle (f value))) :
    IsPPT input output (fun a => program (f a)) := by
  let : Finite Oracle := hprogram.1
  simpa only [pure_bind] using hf.isPPT.bind hprogram

end Turing.MultiTapePTM
