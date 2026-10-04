/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Init.Control.Option

/-! # Trace invariants for stateful handlers -/

public section

namespace PFunctor.FreeM

universe u

variable {P Q : PFunctor.{u, u}} {α State : Type u}

/-- An invariant preserved by each successful handler call holds after an adaptive program.
The invariant may relate the final state to the entire trace, including an existing prefix.
Aborted runs have no successful result and impose no postcondition. -/
theorem trace_liftM_stateT_invariant
    (handler : (op : P.A) → StateT State (OptionT Q.FreeM) (P.B op))
    (invariant : List (Sigma Q.B) → State → Prop)
    (step : ∀ op before state answer state' events, invariant before state →
      MonadAttach.CanReturn (trace ((handler op).run state).run)
        (some (answer, state'), events) → invariant (before ++ events) state')
    (x : P.FreeM α) (before : List (Sigma Q.B)) (state : State)
    (hstate : invariant before state) {a : α} {state' : State} {events : List (Sigma Q.B)}
    (h : MonadAttach.CanReturn (trace ((x.liftM handler).run state).run)
      (some (a, state'), events)) : invariant (before ++ events) state' := by
  induction x generalizing before state a state' events with
  | pure value =>
    have hout : (some (a, state'), events) = (some (value, state), []) := h
    cases hout
    simpa using hstate
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind, StateT.run_bind] at h
    dsimp only [Bind.bind, OptionT.instMonad, OptionT.run, OptionT.bind, OptionT.mk] at h
    rw [bind_eq_bind] at h
    obtain ⟨out, first, rest, hfirst, hrest, rfl⟩ := (canReturn_trace_bind _ _ _).mp h
    cases out with
    | none => cases hrest
    | some out =>
      simpa only [List.append_assoc] using
        ih out.1 (before ++ first) out.2 (step op _ _ _ _ _ hstate hfirst) hrest

end PFunctor.FreeM
