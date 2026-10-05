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
