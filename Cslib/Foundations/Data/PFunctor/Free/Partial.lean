/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Running a free program with a partial handler

When an optional handler returns a value for a program, it has answered every operation on that
path. A stateful handler which supplies those same answers at a fixed state and preserves it
returns the same value together with that state. In particular a larger partial handler preserves
each successful run.
-/

public section

universe uA uB v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uB}

/-- A handler that returns every assigned reply from `s` without changing `s` replays
a successful partial run, preserving both the result and the state. -/
theorem run_liftM_eq_pure_of_liftM_eq_some {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    {σ : Type uB} (p : (a : P.A) → Option (P.B a)) (h : (a : P.A) → StateT σ m (P.B a))
    (s : σ) (hp : ∀ a b, p a = some b → (h a).run s = pure (b, s))
    {x : P.FreeM α} {v : α} (hx : x.liftM p = some v) : (x.liftM h).run s = pure (v, s) := by
  induction x using FreeM.rec generalizing v with
  | pure a =>
    cases Option.some.inj hx
    rfl
  | liftBind a r ih =>
    obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp hx
    change (h a >>= fun b => (r b).liftM h).run s = pure (v, s)
    rw [StateT.run_bind, hp a b hb, LawfulMonad.pure_bind]
    exact ih b hr

/-- A handler returning each assigned reply purely replays any successful partial run. -/
theorem liftM_eq_pure_of_liftM_eq_some {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    (p : (a : P.A) → Option (P.B a)) (h : (a : P.A) → m (P.B a))
    (hp : ∀ a b, p a = some b → h a = pure b)
    {x : P.FreeM α} {v : α} (hx : x.liftM p = some v) : x.liftM h = pure v := by
  have lifted := run_liftM_eq_pure_of_liftM_eq_some (m := m) p
    (fun a => monadLift (h a)) PUnit.unit (fun a b hb => by simp [hp a b hb]) hx
  have natural :=
    (Cslib.IsMonadHom.monadLiftT (m := m) (n := StateT PUnit m)).map_pfunctorFreeMLiftM h x
  rw [← natural] at lifted
  change (x.liftM h >>= fun a => pure (a, PUnit.unit)) = pure (v, PUnit.unit) at lifted
  have first := congrArg (fun t : m (α × PUnit) => t >>= fun z => pure (f := m) z.1) lifted
  simpa only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind, _root_.bind_pure] using first

/-- An extension of a partial handler preserves every successful run. -/
theorem liftM_eq_some_of_le (p q : (a : P.A) → Option (P.B a))
    (hpq : ∀ a b, p a = some b → q a = some b)
    {x : P.FreeM α} {v : α} (hx : x.liftM p = some v) : x.liftM q = some v :=
  liftM_eq_pure_of_liftM_eq_some p q hpq hx

end PFunctor.FreeM
