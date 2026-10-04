/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Snapshot
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape

/-! # Saved-coin execution on finite machine snapshots -/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {State Oracle α : Type} [DecidableEq Oracle]
  {m : Type → Type*} [Monad m] {input : List Bool}

/-- One transition on finite data, with an explicit coin and a stateful monadic handler. -/
def stepSnapshot (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → m (List Bool)) (bit : Bool)
    (snapshot : Snapshot k Bool State Oracle) : m (Snapshot k Bool State Oracle) :=
  match snapshot.state with
  | none => pure snapshot
  | some state =>
    match machine.tr state (snapshot.inputSymbol input) snapshot.workSymbols
        snapshot.answerSymbols bit with
    | .step action symbol move => pure (snapshot.step input action symbol move)
    | .query port next => do
      let answer ← handler port (snapshot.channels port).queryBuffer
      pure (snapshot.receive port next answer)

/-- Execute supplied coins without expanding finite snapshots into function-valued tapes. -/
def runSnapshotFromCoins (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) : m (Snapshot k Bool State Oracle) :=
  coins.foldlM (fun snapshot bit => machine.stepSnapshot input handler bit snapshot) snapshot

/-- Interpreting the handler commutes with each saved-coin transition, including its reply. -/
theorem map_stepSnapshot {n : Type → Type*} [Monad n] {f : ∀ {α}, m α → n α}
    (hf : Cslib.IsMonadHom m n f) (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (bit : Bool)
    (snapshot : Snapshot k Bool State Oracle) :
    f (machine.stepSnapshot input handler bit snapshot) =
      machine.stepSnapshot input (fun port request => f (handler port request)) bit snapshot := by
  cases hs : snapshot.state with
  | none => simp only [stepSnapshot, hs, hf.map_pure]
  | some state =>
    simp only [stepSnapshot, hs]
    split <;> simp only [hf.map_pure, hf.map_bind]

/-- Inlining handlers preserves the complete saved-tape execution, before choosing semantics. -/
theorem map_runSnapshotFromCoins {n : Type → Type*} [Monad n] {f : ∀ {α}, m α → n α}
    (hf : Cslib.IsMonadHom m n f) (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) :
    f (machine.runSnapshotFromCoins input handler coins snapshot) =
      machine.runSnapshotFromCoins input (fun port request => f (handler port request))
        coins snapshot := by
  induction coins generalizing snapshot with
  | nil => exact hf.map_pure _
  | cons bit coins ih =>
    simp only [runSnapshotFromCoins] at ih ⊢
    simp only [List.foldlM_cons, hf.map_bind, map_stepSnapshot hf, ih]

variable [LawfulMonad m]

/-- Pausing finite execution retains the complete snapshot and the handler's state. -/
theorem runSnapshotFromCoins_append (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (before after : List Bool)
    (snapshot : Snapshot k Bool State Oracle) :
    machine.runSnapshotFromCoins input handler (before ++ after) snapshot =
      (machine.runSnapshotFromCoins input handler before snapshot >>=
        machine.runSnapshotFromCoins input handler after) := by
  simp only [runSnapshotFromCoins, List.foldlM_append]
  rfl

theorem runSnapshotFromCoins_halted (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (h : snapshot.state = none) :
    machine.runSnapshotFromCoins input handler coins snapshot = pure snapshot := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    simpa only [runSnapshotFromCoins, List.foldlM_cons, stepSnapshot, h, pure_bind] using ih

/-- Finite execution preserves every monadic continuation that depends only on represented data.
In particular, this preserves shared handler state and the exact sequence of oracle effects. -/
theorem runSnapshotFromCoins_bind (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (cfg : Config k Bool State Oracle input)
    (h : snapshot.Represents cfg)
    (observeSnapshot : Snapshot k Bool State Oracle → m α)
    (observeConfig : Config k Bool State Oracle input → m α)
    (hobserve : ∀ snapshot cfg, snapshot.Represents cfg →
      observeSnapshot snapshot = observeConfig cfg) :
    (machine.runSnapshotFromCoins input handler coins snapshot >>= observeSnapshot) =
      (machine.runConfigFromCoins handler coins cfg >>= observeConfig) := by
  induction coins generalizing snapshot cfg with
  | nil => simpa [runSnapshotFromCoins] using hobserve snapshot cfg h
  | cons bit coins ih =>
    cases hs : cfg.tapes.state with
    | none =>
      rw [runSnapshotFromCoins_halted machine handler _ snapshot (h.state.trans hs),
        runConfigFromCoins_halted machine handler _ cfg hs]
      simpa using hobserve snapshot cfg h
    | some state =>
      simp only [runSnapshotFromCoins, List.foldlM_cons, stepSnapshot, h.state, hs,
        h.inputSymbol, h.workSymbols, h.answerSymbols, runConfigFromCoins]
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simp only [pure_bind]
        exact ih _ _ (h.step action symbol move)
      | query port next =>
        simp only [bind_assoc, pure_bind, h.queryBuffer]
        apply bind_congr
        intro answer
        exact ih _ _ (h.receive port next answer)

/-- Finite snapshots expose exactly the original completed output, including clock exhaustion. -/
theorem runSnapshotFromCoins_output (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (cfg : Config k Bool State Oracle input)
    (h : snapshot.Represents cfg) :
    (fun final => if final.state.isNone then some final.output else none) <$>
        machine.runSnapshotFromCoins input handler coins snapshot =
      output? <$> machine.runConfigFromCoins handler coins cfg := by
  simp only [map_eq_pure_bind]
  apply runSnapshotFromCoins_bind _ _ _ _ _ h
  intro snapshot cfg h
  simp only [output?, h.state, h.output]

/-- Stateful deterministic replay is an ordinary fold on the snapshot and private state. -/
theorem runSnapshotFromCoins_stateT {S : Type} (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → StateT S Id (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (state : S) :
    Id.run ((machine.runSnapshotFromCoins input handler coins snapshot).run state) =
      coins.foldl (fun pair bit =>
        Id.run ((machine.stepSnapshot input handler bit pair.1).run pair.2)) (snapshot, state) := by
  induction coins generalizing snapshot state with
  | nil => rfl
  | cons bit coins ih =>
    change Id.run ((machine.runSnapshotFromCoins input handler coins
      (Id.run ((machine.stepSnapshot input handler bit snapshot).run state)).1).run
        (Id.run ((machine.stepSnapshot input handler bit snapshot).run state)).2) = _
    exact ih _ _

/-- Induct over actual transitions while retaining the joint machine and handler state. -/
theorem runSnapshotFromCoins_stateT_spec {S : Type}
    (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → StateT S Id (List Bool)) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (state : S)
    (invariant : ℕ → Snapshot k Bool State Oracle × S → Prop)
    (hinit : invariant 0 (snapshot, state))
    (hstep : ∀ index pair bit, index < coins.length → invariant index pair →
      invariant (index + 1)
        (Id.run ((machine.stepSnapshot input handler bit pair.1).run pair.2))) :
    invariant coins.length
      (Id.run ((machine.runSnapshotFromCoins input handler coins snapshot).run state)) := by
  induction coins generalizing snapshot state invariant with
  | nil => exact hinit
  | cons bit coins ih =>
    let next := Id.run ((machine.stepSnapshot input handler bit snapshot).run state)
    have hn : invariant 1 next := hstep 0 (snapshot, state) bit (by simp) hinit
    exact ih next.1 next.2 (fun index => invariant (index + 1)) hn
      (fun index pair bit hi hs => hstep (index + 1) pair bit (by simpa using hi) hs)

end Turing.MultiTapePTM
