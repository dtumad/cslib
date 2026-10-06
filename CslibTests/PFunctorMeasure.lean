/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Control.Monad.Free
import Cslib.Foundations.Data.PFunctor.Resumption.Measure

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

-- Programs in the free monad of an effect family, which lives one universe up, get a measure
-- semantics by interpreting their operations as polynomial programs.
example {F : Type → Type} (interp : {ι : Type} → F ι → (y^Bool).FreeM ι) :
    Cslib.IsMeasureSemantics (Cslib.FreeM F) fun x => (x.liftM interp).toMeasure μ :=
  (FreeM.isMeasureSemantics_toMeasure μ).comp (Cslib.FreeM.isMonadHom_liftM interp)

-- Free programs lifted to resumptions return almost surely; instance search finds this through the
-- lift.
example [∀ a, IsProbabilityMeasure (μ a)] (x : (y^Bool).FreeM Bool) :
    IsProbabilityMeasure ((monadLift x : Resumption (y^Bool) Bool).toMeasure μ) := by
  infer_instance

end CslibTests.PFunctorMeasure
