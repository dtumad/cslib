/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Realizer
public import Cslib.Computability.PolynomialTime.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Uniform polynomial-time sequencing

Composition uses the physical buffered-input compiler. Reachability reflection ensures that every
machine path produces a valid intermediate code, whose length is bounded by the source's clock.
Both subroutines use the same oracle environment, including its state across adaptive calls.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeTM MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β γ : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Compose the chosen machines, charging for the buffered input and its preparation.
Both the implementing machine and its polynomial clock are constructed from the supplied data. -/
def Realizer.bind {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → (effects Oracle).FreeM β} {second : β → (effects Oracle).FreeM γ}
    (hfirst : Realizer input middle first) (hsecond : Realizer middle output second) :
    Realizer input output (fun a => first a >>= second) := by
  obtain ⟨hfinite, k₀, ports₀, State₀, hstate₀, source, dispatch₀, c₀, d₀, hhalt₀, hreal₀⟩ := hfirst
  obtain ⟨_, k₁, ports₁, State₁, hstate₁, target, dispatch₁, c₁, d₁, hhalt₁, hreal₁⟩ := hsecond
  have hsource a := And.intro (hhalt₀ a) (hreal₀ a)
  have htarget a := And.intro (hhalt₁ a) (hreal₁ a)
  let : Finite State₀ := hstate₀
  let : Finite State₁ := hstate₁
  let : Countable β := middle.injective.countable
  let : MeasurableSpace β := ⊤
  let firstTime (length : ℕ) := c₀ * (length + 1) ^ d₀
  let secondTime (length : ℕ) := c₁ * (firstTime length + 1) ^ d₁
  let coefficient := 2 * c₀ + 4 + c₁ * (c₀ + 1) ^ d₁
  let degree := d₀ + d₀ * d₁
  have htime (length : ℕ) : firstTime length + (firstTime length + 4 + secondTime length) ≤
      coefficient * (length + 1) ^ degree := by
    have hpow : 1 ≤ (length + 1) ^ d₀ := Nat.one_le_pow _ _ (by omega)
    have hsize : firstTime length + 1 ≤ (c₀ + 1) * (length + 1) ^ d₀ := by
      dsimp only [firstTime]
      nlinarith
    have hsecond : secondTime length ≤ c₁ * (c₀ + 1) ^ d₁ * (length + 1) ^ (d₀ * d₁) := by
      calc
        _ ≤ c₁ * ((c₀ + 1) * (length + 1) ^ d₀) ^ d₁ := by
          exact Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left hsize d₁)
        _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]
    have hfirst : firstTime length ≤ c₀ * (length + 1) ^ degree := by
      dsimp only [firstTime, degree]
      gcongr
      omega
    have hsecond' : secondTime length ≤ c₁ * (c₀ + 1) ^ d₁ * (length + 1) ^ degree := by
      apply hsecond.trans
      dsimp only [degree]
      gcongr
      omega
    have hunit : 1 ≤ (length + 1) ^ degree := Nat.one_le_pow _ _ (by omega)
    dsimp only [coefficient]
    nlinarith
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
    source.comp target, Fin.addCases dispatch₀ dispatch₁, coefficient, degree,
    fun a => (hhalt a).mono (htime (input a).length), fun a => ?_⟩
  apply Realizes.mono ?_ (hhalt a) (htime (input a).length)
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

/-- The composed witness retains the physical composition of the original machines. -/
@[simp] theorem Realizer.bind_machine {input : α ↪ Word} {middle : β ↪ Word}
    {output : γ ↪ Word} {first : α → (effects Oracle).FreeM β}
    {second : β → (effects Oracle).FreeM γ}
    (source : Realizer input middle first) (target : Realizer middle output second) :
    (source.bind target).machine = source.machine.comp target.machine := rfl

/-- Uniform machine certificates compose, retaining the shared oracle environment. -/
theorem IsPPT.bind {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → (effects Oracle).FreeM β} {second : β → (effects Oracle).FreeM γ}
    (hfirst : IsPPT input middle first) (hsecond : IsPPT middle output second) :
    IsPPT input output (fun a => first a >>= second) := by
  obtain ⟨source⟩ := isPPT_iff_nonempty_realizer.mp hfirst
  obtain ⟨target⟩ := isPPT_iff_nonempty_realizer.mp hsecond
  exact (source.bind target).isPPT

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
