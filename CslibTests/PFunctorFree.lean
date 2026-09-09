/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Polynomial free-monad constructor normalization

Ordinary imports expose the same constructor form in simplification and induction. Named binds
also cover independently universe-polymorphic results, where monadic bind notation is unavailable.
-/

public section

open PFunctor

universe uA uB uX

example {P : PFunctor.{uA, uB}} {X : Type uX}
    (op : P.A) (next : P.B op → FreeM P X) :
    (FreeM.lift op).bind next = FreeM.liftBind op next := by simp

example {P : PFunctor.{uA, uB}} {X Y : Type uX}
    (op : P.A) (next : P.B op → FreeM P X) (f : X → Y) :
    f <$> FreeM.liftBind op next = FreeM.liftBind op (fun answer => f <$> next answer) := by
  simp

example {P : PFunctor.{uA, uB}} {X : Type uX}
    (motive : FreeM P X → Prop) (leaf : ∀ x, motive (pure x))
    (step : ∀ op next, (∀ answer, motive (next answer)) → motive (FreeM.liftBind op next))
    (program : FreeM P X) : motive program := by
  induction program with
  | pure x => exact leaf x
  | lift_bind op next ih =>
      guard_target =ₛ motive (FreeM.liftBind op next)
      exact step op next ih
