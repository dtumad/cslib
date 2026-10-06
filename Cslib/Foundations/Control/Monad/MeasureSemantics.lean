/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measure semantics of monads

A measure semantics of a monad `m` interprets each computation `x : m α` as a measure `sem x` on
its results. It sends `pure a` to the Dirac measure at `a` (`IsPureMeasureSemantics`), and
`x >>= f` to the Giry bind of `sem x` with `fun a => sem (f a)` whenever that continuation is
measurable (`IsMeasureSemantics`), which holds automatically on discrete spaces. Measures do not
form a `Monad`, since a measure needs a measurable space on its type, so this is not an instance
of `IsMonadHom`; precomposing with a monad morphism gives a semantics of its source
(`IsMeasureSemantics.comp`).

Semantics are passed explicitly rather than found by instance search, so a monad may carry
several, such as the output measures of programs under different distributions of the answers to
their operations. No bound on total mass is imposed: computations may fail to return and lose
mass. A semantics is evaluated with the measurable spaces its result types carry; on discrete
spaces nothing is lost.
-/

@[expose] public section

open MeasureTheory

universe u v w

namespace Cslib

/-- `sem` interprets `pure a` as the Dirac measure at `a`. -/
structure IsPureMeasureSemantics (m : Type u → Type v) [Pure m]
    (sem : ∀ {α : Type u} [MeasurableSpace α], m α → Measure α) : Prop where
  map_pure {α : Type u} [MeasurableSpace α] (a : α) : sem (pure a) = .dirac a

/-- `sem` is a measure semantics of the monad `m`: it interprets `pure` by Dirac measures and
`>>=` by the Giry bind along measurable continuations. -/
structure IsMeasureSemantics (m : Type u → Type v) [Monad m]
    (sem : ∀ {α : Type u} [MeasurableSpace α], m α → Measure α) : Prop
    extends IsPureMeasureSemantics m sem where
  map_bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (x : m α) {f : α → m β}
    (hf : Measurable fun a => sem (f a)) : sem (x >>= f) = (sem x).bind fun a => sem (f a)

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {F : ∀ {α}, m α → n α} {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

namespace IsPureMeasureSemantics

variable {sem : ∀ {α : Type u} [MeasurableSpace α], n α → Measure α}

theorem comp (hsem : IsPureMeasureSemantics n sem) (hF : IsMonadHom m n F) :
    IsPureMeasureSemantics m fun x => sem (F x) where
  map_pure a := by rw [hF.map_pure, hsem.map_pure]

end IsPureMeasureSemantics

namespace IsMeasureSemantics

section

variable {sem : ∀ {α : Type u} [MeasurableSpace α], m α → Measure α}
  (hsem : IsMeasureSemantics m sem)
include hsem

theorem map_bind_of_discrete [DiscreteMeasurableSpace α] (x : m α) (f : α → m β) :
    sem (x >>= f) = (sem x).bind fun a => sem (f a) :=
  hsem.map_bind x .of_discrete

theorem map_map [LawfulMonad m] (x : m α) {f : α → β} (hf : Measurable f) :
    sem (f <$> x) = (sem x).map f := by
  have hpure : Measurable fun a => sem (pure (f a) : m β) := by
    simp only [hsem.map_pure]
    exact Measure.measurable_dirac.comp hf
  rw [← bind_pure_comp, hsem.map_bind x hpure]
  simpa [hsem.map_pure] using Measure.bind_dirac_eq_map _ hf

theorem map_map_of_discrete [LawfulMonad m] [DiscreteMeasurableSpace α] (x : m α) (f : α → β) :
    sem (f <$> x) = (sem x).map f :=
  hsem.map_map x .of_discrete

end

theorem comp {sem : ∀ {α : Type u} [MeasurableSpace α], n α → Measure α}
    (hsem : IsMeasureSemantics n sem) (hF : IsMonadHom m n F) :
    IsMeasureSemantics m fun x => sem (F x) where
  toIsPureMeasureSemantics := hsem.toIsPureMeasureSemantics.comp hF
  map_bind x f hf := by rw [hF.map_bind]; exact hsem.map_bind _ hf

end IsMeasureSemantics

end Cslib
