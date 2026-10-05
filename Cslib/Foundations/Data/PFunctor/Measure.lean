/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measures on polynomial-functor responses

`PFunctor.OutputMeasure P` bundles a measure for each response type of `P`, using its existing
measurable space. The bundle is an explicit argument to an interpretation: the same interface
can have several different laws. `ofMeasure` bundles existing measures, and `sum` combines
interpretations of interfaces.

As with Mathlib's `Measure`, response measurable spaces are parameters, not fields of the bundle.
Operations infer these parameters from their measure arguments. No global instance chooses a
measure or replaces a response measurable space. Discreteness and normalization use the native
`DiscreteMeasurableSpace` and `IsProbabilityMeasure` classes; arbitrary measures are also allowed.
-/

@[expose] public section

open MeasureTheory

universe uA uB uQ

namespace PFunctor

/-- Explicit operation measures on the existing measurable response spaces. -/
structure OutputMeasure (P : PFunctor.{uA, uB}) [∀ op, MeasurableSpace (P.B op)] where
  /-- The measure of each operation's responses. -/
  measure : (op : P.A) → Measure (P.B op)

namespace OutputMeasure

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uB}}
  {mP : ∀ op, MeasurableSpace (P.B op)} {mQ : ∀ op, MeasurableSpace (Q.B op)}

instance : CoeFun (OutputMeasure P) (fun _ => (op : P.A) → Measure (P.B op)) :=
  ⟨fun μ => μ.measure⟩

@[ext]
theorem ext {μ ν : OutputMeasure P} (h : ∀ op, μ op = ν op) : μ = ν := by
  cases μ
  cases ν
  congr 1
  funext op
  exact h op

/-- Bundle measures without changing their measurable spaces. -/
abbrev ofMeasure (μ : (op : P.A) → Measure (P.B op)) : OutputMeasure P := ⟨μ⟩

@[simp]
theorem ofMeasure_apply (μ : (op : P.A) → Measure (P.B op)) (op : P.A) :
    ofMeasure μ op = μ op := rfl

/-- The response spaces of a sum are inherited from its components. This is not a global
instance: it only assembles the given spaces into a dependent family. -/
abbrev sumMeasurableSpace (P : PFunctor.{uA, uB}) (Q : PFunctor.{uQ, uB})
    [mP : ∀ op, MeasurableSpace (P.B op)] [mQ : ∀ op, MeasurableSpace (Q.B op)] :
    (op : (P + Q).A) → MeasurableSpace ((P + Q).B op)
  | .inl op => mP op
  | .inr op => mQ op

instance [hP : ∀ op, DiscreteMeasurableSpace (P.B op)]
    [hQ : ∀ op, DiscreteMeasurableSpace (Q.B op)] (op : (P + Q).A) :
    @DiscreteMeasurableSpace ((P + Q).B op) (sumMeasurableSpace P Q op) := by
  cases op with
  | inl op => exact hP op
  | inr op => exact hQ op

/-- Interpret a sum using the component measures on their original measurable spaces. -/
def sum (μ : OutputMeasure P) (ν : OutputMeasure Q) :
    @OutputMeasure.{max uA uQ, uB} (P + Q) (sumMeasurableSpace P Q) :=
  @OutputMeasure.mk.{max uA uQ, uB} (P + Q) (sumMeasurableSpace P Q)
    (fun op => match op with | .inl op => μ op | .inr op => ν op)

@[simp]
theorem sum_inl (μ : OutputMeasure P) (ν : OutputMeasure Q) (op : P.A) :
    μ.sum ν (.inl op) = μ op := rfl

@[simp]
theorem sum_inr (μ : OutputMeasure P) (ν : OutputMeasure Q) (op : Q.A) :
    μ.sum ν (.inr op) = ν op := rfl

instance (μ : OutputMeasure P) (ν : OutputMeasure Q)
    [hμ : ∀ op, IsProbabilityMeasure (μ op)] [hν : ∀ op, IsProbabilityMeasure (ν op)]
    (op : (P + Q).A) : IsProbabilityMeasure (μ.sum ν op) := by
  cases op with
  | inl op => exact hμ op
  | inr op => exact hν op

end OutputMeasure
end PFunctor
