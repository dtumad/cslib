/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Partial

/-! A partial run inspects only the continuation selected by its reply. -/

open PFunctor

namespace Tests.PFunctorPartial

private abbrev spec : PFunctor := ⟨Bool, fun b => if b then Nat else Bool⟩

private def partialReply : (q : spec.A) → Option (spec.B q)
  | false => some false
  | true => none

private def branch : spec.FreeM Nat :=
  .liftBind false fun b => cond b (.liftBind true .pure) (.pure 7)

example : branch.liftM partialReply = some 7 := rfl

-- The unused request can update state and return a different reply.
private def reply : (q : spec.A) → StateM Nat (spec.B q)
  | false => pure false
  | true => fun n => (n, n + 1)

example (s : Nat) : (branch.liftM reply).run s = (7, s) := by
  apply FreeM.run_liftM_eq_pure_of_liftM_eq_some (m := Id) partialReply reply s _ (v := 7) (by rfl)
  intro q b h
  cases q with
  | false => cases Option.some.inj h; rfl
  | true => contradiction

end Tests.PFunctorPartial
