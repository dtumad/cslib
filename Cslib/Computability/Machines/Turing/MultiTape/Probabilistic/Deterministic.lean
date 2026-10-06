/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-! # Deterministic machines inside the fair-coin model -/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- Ignore the private coin and communication channels, retaining the deterministic clock. -/
def ofDeterministic (machine : MultiTapeTM k Bool State) : MultiTapePTM k Bool State Oracle where
  initial := machine.q₀
  tr state symbol work _ _ := .step (machine.tr state symbol work) (fun _ => none) (fun _ => 0)

omit [DecidableEq Oracle] in
@[simp]
theorem tapes_initialConfig_ofDeterministic (machine : MultiTapeTM k Bool State)
    (input : List Bool) :
    ((ofDeterministic machine : MultiTapePTM k Bool State Oracle).initialConfig input).tapes =
      machine.initCfg input :=
  rfl

/-- A deterministic step preserves all communication storage. -/
theorem step_ofDeterministic (machine : MultiTapeTM k Bool State)
    (cfg : Config k Bool State Oracle input) :
    (ofDeterministic machine).step cfg = if cfg.tapes.state.isNone then pure cfg else (do
      let _ ← coin
      pure { cfg with tapes := machine.step cfg.tapes }) := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, hs, ofDeterministic, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    apply bind_congr
    intro bit
    congr 1
    apply Config.ext
    · simp [Config.step, MultiTapeTM.step, hs]
    · funext oracle
      simp [Config.step]

/-- Every coin path reaches the same deterministic configuration. -/
theorem canReturn_ofDeterministic (machine : MultiTapeTM k Bool State) (fuel : ℕ)
    (cfg final : Config k Bool State Oracle input)
    (h : MonadAttach.CanReturn ((ofDeterministic machine).runConfigFrom fuel cfg) final) :
    final = { cfg with tapes := machine.runFrom cfg.tapes fuel } := by
  induction fuel generalizing cfg with
  | zero => exact h
  | succ fuel ih =>
    obtain ⟨mid, hmid, hfinal⟩ := (FreeM.canReturn_bind _ _ _).mp h
    rw [step_ofDeterministic] at hmid
    cases hs : cfg.tapes.state with
    | none =>
      have heq : mid = cfg := by simpa [hs] using hmid
      subst mid
      rw [ih cfg hfinal]
      have hrun (n : ℕ) : machine.runFrom cfg.tapes n = cfg.tapes :=
        machine.runFrom_eq_of_halt cfg.tapes (Nat.zero_le n) hs
      simp only [hrun]
    | some state =>
      simp only [hs, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hmid
      obtain ⟨_, _, hmid⟩ := (FreeM.canReturn_bind _ _ _).mp hmid
      have heq : mid = { cfg with tapes := machine.step cfg.tapes } := hmid
      subst mid
      rw [ih _ hfinal]
      rfl

end Turing.MultiTapePTM
