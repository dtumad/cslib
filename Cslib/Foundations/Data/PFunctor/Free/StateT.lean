/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Interpreting free programs with a change of state representation

A representation that commutes with each stateful operation preserves the joint output and
final represented state of the entire program.
-/

public section

namespace PFunctor.FreeM

universe uA uB v

/-- If two handlers agree after mapping each reply's final state through `f`, then their
interpretations agree after the same change of state representation. -/
theorem map_state_run_liftM {P : PFunctor.{uA, uB}} {m : Type uB → Type v} [Monad m]
    [LawfulMonad m] {σ τ α : Type uB} (h : (a : P.A) → StateT σ m (P.B a))
    (h' : (a : P.A) → StateT τ m (P.B a)) (f : σ → τ)
    (step : ∀ a s, Prod.map id f <$> (h a).run s = (h' a).run (f s))
    (p : P.FreeM α) (s : σ) :
    Prod.map id f <$> (p.liftM h).run s = (p.liftM h').run (f s) := by
  induction p generalizing s with
  | pure a => simp
  | lift_bind a k ih =>
    simp only [bind_eq_bind, liftM_lift_bind, StateT.run_bind, _root_.map_bind]
    rw [← step a s, bind_map_left]
    exact bind_congr fun r => ih r.1 r.2

end PFunctor.FreeM
