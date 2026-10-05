/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Machine
public import Cslib.Foundations.Data.PFunctor.Free.Cost

/-!
# Fair-coin oracle Turing machines

Each live transition reads one fair bit and inspects only the symbols under the tape heads.
Oracle requests are written and replies are read one bit at a time. Submitting a request costs
one transition; the oracle's internal computation is external to this clock.

`runConfigFrom` retains the full configuration when its transition budget is exhausted, so runs
can be paused and resumed. `run` returns `none` on exhaustion and `some output` only on halting.
`HaltsWithin` quantifies over all response paths, independently of any probability measure.

Adapted from Samuel Schlesinger's crypto branch, with `PFunctor.FreeM` as the program language.
The complexity layer imposes finite control and finitely many operation names.
-/

@[expose] public section

namespace Turing

/-- A transition table with one action for each Boolean coin value. -/
abbrev MultiTapePTM (k : ℕ) (Symbol State : Type) (Oracle : Type := Empty) :=
  MultiTapeMachine k Symbol State Oracle (fun α => Bool → α)

namespace MultiTapePTM

open MultiTapeMachine PFunctor

/-- Private coins and named word-valued oracle requests. Names exclude request payloads. -/
abbrev effects (Oracle : Type) : PFunctor :=
  PFunctor.mk Unit (fun _ => Bool) + PFunctor.mk (Oracle × List Bool) (fun _ => List Bool)

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- Request one private random bit. Its probability interpretation is supplied separately. -/
def coin : (effects Oracle).FreeM Bool := FreeM.lift (P := effects Oracle) (.inl ())

/-- Submit one named request. -/
def query (oracle : Oracle) (word : List Bool) : (effects Oracle).FreeM (List Bool) :=
  FreeM.lift (P := effects Oracle) (.inr (oracle, word))

/-- One machine transition; a halted configuration performs no effects. -/
def step (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) :
    (effects Oracle).FreeM (Config k Bool State Oracle input) :=
  match cfg.tapes.state with
  | none => pure cfg
  | some state => do
    let bit ← coin
    match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with
    | .step action symbol move => pure (cfg.step action symbol move)
    | .query oracle next => do
      let answer ← query oracle (cfg.channels oracle).queryBuffer
      pure (cfg.receive oracle next answer)

/-- Run at most `fuel` machine transitions, retaining the complete reached configuration. -/
def runConfigFrom (machine : MultiTapePTM k Bool State Oracle) :
    ℕ → Config k Bool State Oracle input →
      (effects Oracle).FreeM (Config k Bool State Oracle input)
  | 0, cfg => pure cfg
  | fuel + 1, cfg => machine.step cfg >>= machine.runConfigFrom fuel

/-- Extract a completed output, keeping clock exhaustion distinct from an empty output. -/
def output? (cfg : Config k Bool State Oracle input) : Option (List Bool) :=
  if cfg.tapes.state.isNone then some cfg.tapes.output else none

/-- Observe a bounded run, returning `none` on clock exhaustion. -/
def runFrom (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) : (effects Oracle).FreeM (Option (List Bool)) :=
  output? <$> machine.runConfigFrom fuel cfg

/-- Execute from blank work and communication tapes, returning `none` on clock exhaustion. -/
def run (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ) (input : List Bool) :
    (effects Oracle).FreeM (Option (List Bool)) :=
  machine.runFrom fuel (machine.initialConfig input)

@[simp] theorem step_halted (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) (h : cfg.tapes.state = none) :
    machine.step cfg = pure cfg := by simp [step, h]

@[simp] theorem runConfigFrom_zero (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) : machine.runConfigFrom 0 cfg = pure cfg := rfl

theorem runConfigFrom_succ (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) :
    machine.runConfigFrom (fuel + 1) cfg = (machine.step cfg >>= machine.runConfigFrom fuel) := rfl

/-- Splitting the transition budget preserves all interactions and the reached configuration. -/
theorem runConfigFrom_add (machine : MultiTapePTM k Bool State Oracle) (first second : ℕ)
    (cfg : Config k Bool State Oracle input) :
    machine.runConfigFrom (first + second) cfg =
      (machine.runConfigFrom first cfg >>= machine.runConfigFrom second) := by
  induction first generalizing cfg with
  | zero => simp [runConfigFrom]
  | succ first ih =>
    rw [Nat.succ_add, runConfigFrom, runConfigFrom, bind_assoc]
    exact bind_congr ih

@[simp] theorem runConfigFrom_halted (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) (h : cfg.tapes.state = none) :
    machine.runConfigFrom fuel cfg = pure cfg := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [runConfigFrom, h, ih]

/-- Expose a transition while retaining timeout in the output type. -/
theorem runFrom_succ (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) :
    machine.runFrom (fuel + 1) cfg = (match cfg.tapes.state with
    | none => pure (some cfg.tapes.output)
    | some state => do
      let bit ← coin
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | .step action symbol move => machine.runFrom fuel (cfg.step action symbol move)
      | .query oracle next => do
        let answer ← query oracle (cfg.channels oracle).queryBuffer
        machine.runFrom fuel (cfg.receive oracle next answer)) := by
  cases hs : cfg.tapes.state with
  | none => simp [runFrom, runConfigFrom, hs, output?]
  | some state =>
    simp only [runFrom, runConfigFrom, step, hs, map_bind, bind_assoc]
    apply bind_congr
    intro bit
    split <;> simp

/-- Every response path has halted by the supplied transition budget. -/
def HaltsWithin (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input) : Prop :=
  ∀ final, MonadAttach.CanReturn (machine.runConfigFrom fuel cfg) final → final.tapes.state = none

/-- Extending the clock after all paths halt leaves the entire program unchanged. -/
theorem HaltsWithin.runConfigFrom_add {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg) (extra : ℕ) :
    machine.runConfigFrom (fuel + extra) cfg = machine.runConfigFrom fuel cfg := by
  rw [MultiTapePTM.runConfigFrom_add]
  calc
    _ = (machine.runConfigFrom fuel cfg >>= pure) := by
      conv_lhs => rw [← WeaklyLawfulMonadAttach.attach_bind_val]
      conv_rhs => rw [← WeaklyLawfulMonadAttach.attach_bind_val]
      apply bind_congr
      intro final
      exact runConfigFrom_halted machine extra final.val (h final.val final.property)
    _ = _ := bind_pure _

/-- A pathwise termination bound remains valid with more time. -/
theorem HaltsWithin.mono {machine : MultiTapePTM k Bool State Oracle} {fuel fuel' : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg)
    (hle : fuel ≤ fuel') : machine.HaltsWithin fuel' cfg := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  simpa only [HaltsWithin, h.runConfigFrom_add] using h

/-- A single transition emits at most one output bit on every response path. -/
theorem length_output_step_le (machine : MultiTapePTM k Bool State Oracle)
    (cfg final : Config k Bool State Oracle input)
    (h : MonadAttach.CanReturn (machine.step cfg) final) :
    final.tapes.output.length ≤ cfg.tapes.output.length + 1 := by
  cases hs : cfg.tapes.state with
  | none =>
    have heq : final = cfg := by simpa [step, hs] using h
    simp [heq]
  | some state =>
    simp only [step, hs] at h
    obtain ⟨bit, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
    cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with
    | step action symbol move =>
      have heq : final = cfg.step action symbol move := by
        simpa only [ha, FreeM.canReturn_pure] using h
      rw [heq]
      simp only [Config.step, Turing.Action.apply, List.length_append]
      exact Nat.add_le_add_left action.output.length_toList_le _
    | query oracle next =>
      rw [ha] at h
      obtain ⟨answer, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
      have heq : final = cfg.receive oracle next answer := h
      rw [heq]
      simp [Config.receive]

/-- The transition clock bounds explicitly written output, independently of oracle reply sizes. -/
theorem length_output_runConfigFrom_le (machine : MultiTapePTM k Bool State Oracle) (fuel : ℕ)
    (cfg final : Config k Bool State Oracle input)
    (h : MonadAttach.CanReturn (machine.runConfigFrom fuel cfg) final) :
    final.tapes.output.length ≤ cfg.tapes.output.length + fuel := by
  induction fuel generalizing cfg with
  | zero =>
    have heq : final = cfg := h
    simp [heq]
  | succ fuel ih =>
    obtain ⟨mid, hstep, hrun⟩ := (FreeM.canReturn_bind _ _ _).mp h
    have := length_output_step_le machine cfg mid hstep
    have := ih mid hrun
    omega

/-- Every completed output fits within the transition budget used to write it. -/
theorem length_of_canReturn_run (machine : MultiTapePTM k Bool State Oracle)
    (fuel : ℕ) (input word : List Bool)
    (h : MonadAttach.CanReturn (machine.run fuel input) (some word)) : word.length ≤ fuel := by
  obtain ⟨final, hfinal, houtput⟩ := (FreeM.canReturn_map _ _ _).mp h
  cases hs : final.tapes.state with
  | none =>
    have heq : final.tapes.output = word := by simpa [output?, hs] using houtput
    rw [← heq]
    simpa [initialConfig, Cfg.init] using
      length_output_runConfigFrom_le machine fuel (machine.initialConfig input) final hfinal
  | some state => simp [output?, hs] at houtput

end MultiTapePTM

end Turing
