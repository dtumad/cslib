/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.State
public import Cslib.Foundations.Data.PFunctor.Resumption

/-!
# Threading state through resumptions

Run from a state `s`, a resumption `r` becomes `r.withState s` over `P.withState S`, which passes
the state from each operation to the next and returns the final state with the result. It extends
`PFunctor.FreeM.withState` along `PFunctor.FreeM.toResumption`.
-/

@[expose] public section

universe uA uB uS u

namespace PFunctor

namespace Resumption

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type u}

/-- Run `r` from the state `s`, passing the state through its operations and returning the final
state with the result. -/
def withState (r : Resumption P α) (s : S) : Resumption (P.withState S) (α × S) :=
  corec (fun x : Resumption P α × S => (dest x.1).elim (fun a => .inl (a, x.2))
    fun o => .inr (.mk (o.fst, x.2) fun b => (o.snd b.1, b.2))) (r, s)

@[simp]
theorem withState_pure (a : α) (s : S) : (pure a : Resumption P α).withState s = pure (a, s) := by
  simp [← dest_inj, withState]

@[simp]
theorem withState_lift_bind (a : P.A) (k : P.B a → Resumption P α) (s : S) :
    ((lift a).bind (α := no_index (P.B a)) k).withState s =
      (lift (P := P.withState S) (a, s)).bind fun b => (k b.1).withState b.2 := by
  simp [← dest_inj, withState, PFunctor.map, Function.comp_def]

@[simp]
theorem withState_lift_bind' {α : Type uB} {S : Type uB} (a : P.A) (k : P.B a → Resumption P α)
    (s : S) :
    (Bind.bind (α := no_index (P.B a)) (lift a) k).withState s =
      lift (P := P.withState S) (a, s) >>= fun b => (k b.1).withState b.2 :=
  withState_lift_bind a k s

end Resumption

namespace FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type u}

@[simp]
theorem toResumption_withState (x : P.FreeM α) (s : S) :
    (x.withState s).toResumption = x.toResumption.withState s := by
  induction x generalizing s <;> simp [*]

end FreeM

end PFunctor
