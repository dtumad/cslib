/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot
public import Init.Control.Option

/-!
# Clocked execution with aborting stateful handlers

A failure bit allows a clocked machine to finish without calling a failed handler again.
The final observation rejects that run. This realizes ordinary `StateT S (OptionT m)` without
turning a failed request into a successful result or requiring a default handler state.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {Oracle S : Type} {m : Type → Type*} [Monad m]

/-- Keep a failure bit while a clocked simulation finishes. After failure, replies are empty
and no further handler effects occur; the caller rejects the final observation. -/
def totalizeHandler (handler : Oracle → List Bool → StateT S (OptionT m) (List Bool)) :
    Oracle → List Bool → StateT (S × Bool) m (List Bool) := fun port request (state, active) =>
  if active then do
    let result ← ((handler port request).run state).run
    pure (result.elim ([], state, false) (fun out => (out.1, out.2, true)))
  else pure ([], state, false)

variable {k : ℕ} {State : Type} [DecidableEq Oracle] [LawfulMonad m]

omit [Monad m] [LawfulMonad m] in
/-- Forgetting auxiliary handler state commutes with an entire clocked execution whenever it
commutes with each call. The equality preserves rejection as well as completed snapshots. -/
theorem runSnapshotFromCoins_map_state {T : Type}
    (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → StateT S Option (List Bool))
    (record : Oracle → List Bool → StateT T Option (List Bool)) (forget : T → S)
    (hcall : ∀ port request state,
      (record port request state).map (fun out => (out.1, forget out.2)) =
        handler port request (forget state))
    (coins : List Bool) (snapshot : Snapshot k Bool State Oracle) (state : T) :
    (machine.runSnapshotFromCoins input record coins snapshot state).map
      (fun out => (out.1, forget out.2)) =
        machine.runSnapshotFromCoins input handler coins snapshot (forget state) := by
  induction coins generalizing snapshot state with
  | nil => rfl
  | cons bit coins ih =>
    change (((machine.stepSnapshot input record bit snapshot >>=
      machine.runSnapshotFromCoins input record coins) state).map
        (fun out => (out.1, forget out.2))) =
      (machine.stepSnapshot input handler bit snapshot >>=
        machine.runSnapshotFromCoins input handler coins) (forget state)
    cases hs : snapshot.state with
    | none =>
      simpa only [stepSnapshot, hs, pure_bind] using ih snapshot state
    | some q =>
      simp only [stepSnapshot, hs]
      cases machine.tr q (snapshot.inputSymbol input) snapshot.workSymbols
        snapshot.answerSymbols bit with
      | step action symbol move =>
        simpa only [pure_bind] using ih (snapshot.step input action symbol move) state
      | query port next =>
        simp only [bind_assoc, pure_bind]
        change ((record port (snapshot.channels port).queryBuffer state).bind
          (fun out => machine.runSnapshotFromCoins input record coins
            (snapshot.receive port next out.1) out.2)).map (fun out => (out.1, forget out.2)) =
          (handler port (snapshot.channels port).queryBuffer (forget state)).bind
            (fun out => machine.runSnapshotFromCoins input handler coins
              (snapshot.receive port next out.1) out.2)
        rw [← hcall port (snapshot.channels port).queryBuffer state]
        cases hc : record port (snapshot.channels port).queryBuffer state with
        | none => rfl
        | some out =>
          simpa only [Option.map_some, Option.bind_some] using
            ih (snapshot.receive port next out.1) out.2

omit [Monad m] [LawfulMonad m] in
/-- An invariant preserved by every successful handler call holds after every successful
clocked execution. Rejected calls cannot establish a completed result. -/
theorem runSnapshotFromCoins_preserves
    (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → StateT S Option (List Bool)) (invariant : S → Prop)
    (hcall : ∀ port request state, invariant state → ∀ out,
      handler port request state = some out → invariant out.2)
    (coins : List Bool) (snapshot : Snapshot k Bool State Oracle) (state : S)
    (hstate : invariant state) {out : Snapshot k Bool State Oracle × S}
    (h : machine.runSnapshotFromCoins input handler coins snapshot state = some out) :
    invariant out.2 := by
  induction coins generalizing snapshot state with
  | nil => cases h; exact hstate
  | cons bit coins ih =>
    change (machine.stepSnapshot input handler bit snapshot >>=
      machine.runSnapshotFromCoins input handler coins) state = some out at h
    cases hs : snapshot.state with
    | none =>
      simp only [stepSnapshot, hs, pure_bind] at h
      exact ih snapshot state hstate h
    | some q =>
      simp only [stepSnapshot, hs] at h
      cases ha : machine.tr q (snapshot.inputSymbol input) snapshot.workSymbols
        snapshot.answerSymbols bit with
      | step action symbol move =>
        simp only [ha, pure_bind] at h
        exact ih (snapshot.step input action symbol move) state hstate h
      | query port next =>
        simp only [ha, bind_assoc, pure_bind] at h
        change ((handler port (snapshot.channels port).queryBuffer state).bind
          (fun result => machine.runSnapshotFromCoins input handler coins
            (snapshot.receive port next result.1) result.2)) = some out at h
        obtain ⟨result, hresult, h⟩ := Option.bind_eq_some_iff.mp h
        exact ih (snapshot.receive port next result.1) result.2
          (hcall port _ state hstate result hresult) h

omit [Monad m] [LawfulMonad m] in
/-- Removing the identity base monad does not change any optional result or handler state. -/
theorem runSnapshotFromCoins_optionT_id
    (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → S → Option (List Bool × S)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (state : S) :
    Id.run (((machine.runSnapshotFromCoins (m := StateT S (OptionT Id)) input
      (fun port request st => OptionT.mk (pure (handler port request st))) coins snapshot).run
        state).run) =
      (machine.runSnapshotFromCoins (m := StateT S Option) input handler coins snapshot).run
        state := by
  have hf : Cslib.IsMonadHom (OptionT Id) Option (fun action => action.run.run) := by
    apply Cslib.IsMonadHom.mk'
    · intro α value
      rfl
    · intro α β action cont
      cases action <;> rfl
  exact congrFun (map_runSnapshotFromCoins (hf.stateT S) machine
    (fun port request st => OptionT.mk (pure (handler port request st))) coins snapshot) state

/-- Rejecting a failed final state gives exactly the partial interpreter's whole monadic
computation. Continuing the clock after failure performs no additional handler effects. -/
theorem runSnapshotFromCoins_totalizeHandler
    (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → StateT S (OptionT m) (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (state : S) (active : Bool) :
    (fun out => if out.2.2 then some (out.1, out.2.1) else none) <$>
      (machine.runSnapshotFromCoins input (totalizeHandler handler) coins snapshot).run
        (state, active) =
      if active then ((machine.runSnapshotFromCoins input handler coins snapshot).run state).run
        else pure none := by
  induction coins generalizing snapshot state active with
  | nil => cases active <;> simp [runSnapshotFromCoins]
  | cons bit coins ih =>
    change (fun out => if out.2.2 then some (out.1, out.2.1) else none) <$>
      ((machine.stepSnapshot input (totalizeHandler handler) bit snapshot >>=
        machine.runSnapshotFromCoins input (totalizeHandler handler) coins).run (state, active)) =
      if active then ((machine.stepSnapshot input handler bit snapshot >>=
        machine.runSnapshotFromCoins input handler coins).run state).run else pure none
    cases hs : snapshot.state with
    | none =>
      simpa only [stepSnapshot, hs, pure_bind] using ih snapshot state active
    | some q =>
      simp only [stepSnapshot, hs]
      cases ha : machine.tr q (snapshot.inputSymbol input) snapshot.workSymbols
          snapshot.answerSymbols bit with
      | step action symbol move =>
        simpa only [pure_bind] using ih (snapshot.step input action symbol move) state active
      | query port next =>
        simp only [bind_assoc, pure_bind, StateT.run_bind]
        cases active with
        | false =>
          simpa only [StateT.run, totalizeHandler, Bool.false_eq_true,
            ↓reduceIte, pure_bind] using
            ih (snapshot.receive port next []) state false
        | true =>
          simp only [StateT.run, totalizeHandler, ↓reduceIte, bind_assoc,
            pure_bind, map_bind, OptionT.run_bind, Option.elimM]
          apply bind_congr
          intro result
          cases result with
          | none =>
            simpa only [Option.elim_none, Bool.false_eq_true, ↓reduceIte, StateT.run] using
              ih (snapshot.receive port next []) state false
          | some out =>
            simpa only [Option.elim_some, ↓reduceIte, StateT.run] using
              ih (snapshot.receive port next out.1) out.2 true

end Turing.MultiTapePTM
