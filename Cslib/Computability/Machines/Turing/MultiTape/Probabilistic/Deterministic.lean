/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-! # Deterministic machines inside the fair-coin model -/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- Ignore the private coin and communication channels, retaining the deterministic clock. -/
def ofDeterministic (machine : MultiTapeTM k Bool State) : MultiTapePTM k Bool State Oracle where
  initial := machine.q₀
  tr state symbol work _ _ := .step (machine.tr state symbol work) (fun _ => none) (fun _ => 0)

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

variable [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
  {S α : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace α]

/-- A deterministic subroutine passes its reached tapes to the continuation without changing
the shared oracle state. Complete machine configurations need no measurable structure. -/
theorem runKernel_bind_ofDeterministic (machine : MultiTapeTM k Bool State)
    (oracle : Oracle → List Bool → Kernel S (List Bool × S)) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input)
    (next : Config k Bool State Oracle input → (effects Oracle).FreeM α)
    (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((ofDeterministic machine).runConfigFrom fuel cfg >>= next) state =
      FreeM.runKernel (effectKernel oracle)
        (next { cfg with tapes := machine.runFrom cfg.tapes fuel }) state := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    rw [runConfigFrom_succ, step_ofDeterministic]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [Option.isNone_none, ↓reduceIte, pure_bind]
      rw [ih]
      have hrun (n : ℕ) : machine.runFrom cfg.tapes n = cfg.tapes :=
        machine.runFrom_eq_of_halt cfg.tapes (Nat.zero_le n) hs
      simp only [hrun]
    | some control =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, bind_assoc,
        pure_bind]
      rw [runKernel_coin_const, ih]
      rw [show fuel + 1 = 1 + fuel by omega, machine.runFrom_add, machine.runFrom_one]

/-- Discarded coins leave the deterministic result and the external state unchanged. -/
theorem runKernel_ofDeterministic (machine : MultiTapeTM k Bool State)
    (oracle : Oracle → List Bool → Kernel S (List Bool × S)) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) (post : Config k Bool State Oracle input → α)
    (state : S) :
    FreeM.runKernel (effectKernel oracle)
      (post <$> (ofDeterministic machine).runConfigFrom fuel cfg) state =
      Measure.dirac (post { cfg with tapes := machine.runFrom cfg.tapes fuel }, state) := by
  rw [map_eq_pure_bind, runKernel_bind_ofDeterministic, FreeM.runKernel_pure]

end Turing.MultiTapePTM
