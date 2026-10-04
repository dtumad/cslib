/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.WP
public import Cslib.Foundations.Order.Lean
public import Std.WP.EStack

/-!
# Quantitative weakest preconditions

Integrating postconditions against each answer measure gives a core `WPMonad` interpretation.
For measurable postconditions it computes exactly the lower integral of the program's denotation.
The interpretation is an explicit construction, so it can coexist with structural readings.
-/

@[expose] public section

open MeasureTheory Std.WP
open scoped ENNReal

namespace PFunctor.FreeM

universe uA uB

variable {P : PFunctor.{uA, uB}} [∀ op, MeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))

/-- Use the usual order of nonnegative extended reals for quantitative assertions. -/
noncomputable local instance : Lean.Order.CompleteLattice ℝ≥0∞ := .ofMathlib _

/-- Expected postconditions, using the answer measures as the operation semantics. -/
@[instance_reducible]
noncomputable def expectationWP : WPMonad P.FreeM ℝ≥0∞ EStack⟨⟩ :=
  wpMonad (fun op => ⟨fun post _ => ∫⁻ b, post b ∂μ op⟩)
    (fun _ _ _ _ _ _ h => lintegral_mono h)

/-- The quantitative WP equals integration against the native measure semantics. -/
theorem expectationWP_eq_lintegral [∀ op, DiscreteMeasurableSpace (P.B op)]
    {α : Type uB} [MeasurableSpace α] (x : P.FreeM α) (post : α → ℝ≥0∞)
    (hpost : Measurable post) :
    ((expectationWP μ).toWP α).wp x post () = ∫⁻ a, post a ∂denote μ x := by
  induction x with
  | pure a => exact (lintegral_dirac' a hpost).symm
  | lift_bind op cont ih =>
    rw [denote_lift_bind μ _ _ Measurable.of_discrete.aemeasurable,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable hpost.aemeasurable]
    change (∫⁻ b, _ ∂μ op) = _
    exact lintegral_congr fun b => ih b

end PFunctor.FreeM
