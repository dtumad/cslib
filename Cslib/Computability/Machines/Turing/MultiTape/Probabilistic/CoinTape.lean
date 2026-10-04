/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Execution with saved machine coins

Each live transition consumes one supplied bit, including query submission. Halting ignores
the unused suffix; exhaustion retains the full configuration. Pausing and resuming does not
repeat earlier oracle effects. This operational evaluator is separate from a machine certificate
for its implementation on encoded tapes.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}
  {m : Type → Type*} [Monad m]

/-- Replay supplied private coins. The handler performs exactly the reached oracle calls. -/
def runConfigFromCoins (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) :
    List Bool → Config k Bool State Oracle input → m (Config k Bool State Oracle input)
  | [], cfg => pure cfg
  | bit :: coins, cfg => match cfg.tapes.state with
    | none => pure cfg
    | some state =>
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | .step action symbol move =>
        machine.runConfigFromCoins handler coins (cfg.step action symbol move)
      | .query oracle next => do
        let answer ← handler oracle (cfg.channels oracle).queryBuffer
        machine.runConfigFromCoins handler coins (cfg.receive oracle next answer)

@[simp] theorem runConfigFromCoins_nil (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (cfg : Config k Bool State Oracle input) :
    machine.runConfigFromCoins handler [] cfg = pure cfg := rfl

/-- A halted machine consumes neither the remaining coins nor any further oracle requests. -/
theorem runConfigFromCoins_halted (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (coins : List Bool)
    (cfg : Config k Bool State Oracle input) (h : cfg.tapes.state = none) :
    machine.runConfigFromCoins handler coins cfg = pure cfg := by
  cases coins <;> simp [runConfigFromCoins, h]

/-- Replaying adjacent tape segments preserves the exact sequence of handler effects. -/
theorem runConfigFromCoins_append [LawfulMonad m] (machine : MultiTapePTM k Bool State Oracle)
    (handler : Oracle → List Bool → m (List Bool)) (before after : List Bool)
    (cfg : Config k Bool State Oracle input) :
    machine.runConfigFromCoins handler (before ++ after) cfg =
      (machine.runConfigFromCoins handler before cfg >>=
        machine.runConfigFromCoins handler after) := by
  induction before generalizing cfg with
  | nil => simp
  | cons bit before ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFromCoins, hs, runConfigFromCoins_halted]
    | some state =>
      simp only [List.cons_append, runConfigFromCoins, hs]
      split <;> simp [ih, bind_assoc]

/-- Every fixed-tape path is a path of the original machine with the same transition budget. -/
theorem canReturn_runConfigFrom_of_coins (machine : MultiTapePTM k Bool State Oracle)
    (coins : List Bool) (cfg final : Config k Bool State Oracle input)
    (h : MonadAttach.CanReturn (machine.runConfigFromCoins query coins cfg) final) :
    MonadAttach.CanReturn (machine.runConfigFrom coins.length cfg) final := by
  induction coins generalizing cfg with
  | nil => exact h
  | cons bit coins ih =>
    cases hs : cfg.tapes.state with
    | none => simpa [runConfigFromCoins, hs] using h
    | some state =>
      simp only [runConfigFromCoins, hs] at h
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        rw [ha] at h
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨cfg.step action symbol move, ?_, ih _ h⟩
        simp only [MultiTapePTM.step, hs]
        apply (FreeM.canReturn_bind _ _ _).mpr
        exact ⟨bit, ⟨bit, rfl⟩, by simp [ha]⟩
      | query oracle next =>
        rw [ha] at h
        obtain ⟨answer, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨cfg.receive oracle next answer, ?_, ih _ h⟩
        simp only [MultiTapePTM.step, hs]
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨bit, ⟨bit, rfl⟩, ?_⟩
        rw [ha]
        exact (FreeM.canReturn_bind _ _ _).mpr ⟨answer, ⟨answer, rfl⟩, rfl⟩

/-- A pathwise clock is also valid for each saved tape of that length. -/
theorem HaltsWithin.coins {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg)
    (coins : List Bool) (hlen : coins.length = fuel) (final : Config k Bool State Oracle input)
    (hfinal : MonadAttach.CanReturn (machine.runConfigFromCoins query coins cfg) final) :
    final.tapes.state = none :=
  h final (hlen ▸ canReturn_runConfigFrom_of_coins machine coins cfg final hfinal)

end Turing.MultiTapePTM
