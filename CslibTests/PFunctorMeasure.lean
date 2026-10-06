/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Control.Monad.Free
import Cslib.Foundations.Data.PFunctor.Resumption.Cost

/-! Tests for output measures of polynomial programs. -/

namespace CslibTests.PFunctorMeasure

open PFunctor MeasureTheory

private def flips : (y^Bool).FreeM Bool := do
  let b ← FreeM.lift ()
  let c ← FreeM.lift ()
  pure (b && !c)

variable (μ : (a : (y^Bool).A) → Measure ((y^Bool).B a))

-- The output measure of a `do` program, which uses `>>=` and `<$>` rather than the
-- universe-polymorphic `bind` and `map`, unfolds to Giry binds of the response measures.
example : flips.toMeasure μ = (μ ()).bind fun b => (μ ()).map fun c => b && !c := by
  simp [flips]

-- Sequencing programs without unfolding them composes their output measures.
example : (do let b ← flips; let c ← flips; pure (b && c)).toMeasure μ =
    (flips.toMeasure μ).bind fun b => (flips.toMeasure μ).map fun c => b && c := by
  simp

-- The largest number of operations along a path of a `do` program bounds its expected number.
example [∀ a, IsProbabilityMeasure (μ a)] :
    flips.toResumption.expectedCost μ (fun _ => 1) ≤ 2 :=
  (Resumption.expectedCost_toResumption_le μ _ (fun _ => prob_le_one) flips).trans_eq
    (by simp [flips, one_add_one_eq_two])

-- Programs in the free monad of an effect family, which lives one universe up, get a measure
-- semantics by interpreting their operations as polynomial programs.
example {F : Type → Type} (interp : {ι : Type} → F ι → (y^Bool).FreeM ι) :
    Cslib.IsMeasureSemantics (Cslib.FreeM F) fun x => (x.liftM interp).toMeasure μ :=
  (FreeM.isMeasureSemantics_toMeasure μ).comp (Cslib.FreeM.isMonadHom_liftM interp)

end CslibTests.PFunctorMeasure
