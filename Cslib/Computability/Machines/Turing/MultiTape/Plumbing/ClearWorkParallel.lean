/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Clearing all scratch tapes in parallel

`ClearWork.parallel` applies the two-tape cleanup routine independently to each data/marker
pair. Its finite controller stores one cleanup phase per pair. Finished pairs remain fixed while
the others continue. A shared bound for the individual cleanups therefore bounds the entire
cleanup, with one extra transition to halt, including when there are no work tapes.

`runFrom_localCfg` proves that each pair follows exactly the existing two-tape machine.
`runFrom_parallel` lifts the per-pair cleanup contracts to a full configuration equality,
preserving the input position and output.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.ClearWork

variable {k : ℕ} {input : List Bool}

/-- A halted pair stays fixed while other pairs finish clearing. -/
def action (state : Option (Fin 3)) (symbol : Option Bool) (work : Fin 2 → Option Bool) :
    Action 2 Bool (Fin 3) :=
  match state with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some state => machine.tr state symbol work

private theorem action_inputTape (state : Option (Fin 3)) (symbol : Option Bool)
    (work : Fin 2 → Option Bool) : (action state symbol work).inputTape = 0 := by
  cases state <;> dsimp [action, machine]
  split_ifs <;> rfl

private theorem action_output (state : Option (Fin 3)) (symbol : Option Bool)
    (work : Fin 2 → Option Bool) : (action state symbol work).output = none := by
  cases state <;> dsimp [action, machine]
  split_ifs <;> rfl

private theorem step_eq_action (source : Cfg 2 Bool (Fin 3) input) :
    machine.step source = (action source.state source.inputSymbol source.workTapeSymbols).apply
      source := by
  cases hs : source.state with
  | none =>
    apply Cfg.ext <;> simp [step, action, hs, Action.apply]
  | some state => simp only [step, hs, action]

/-- Clear every data/marker pair simultaneously, leaving finished pairs untouched. -/
def parallel (k : ℕ) : MultiTapeTM (k + k) Bool (Fin k → Option (Fin 3)) where
  q₀ := fun _ => some 0
  tr phases symbol work :=
    let actions := fun i => action (phases i) symbol
      (fun j => if j = 0 then work (i.castAdd k) else work (Fin.natAdd k i))
    { inputTape := 0, workTapes := Fin.addCases (fun i => (actions i).workTapes 0)
        (fun i => (actions i).workTapes 1),
      output := none, state :=
        if ∀ i, (actions i).state = none then none else some (fun i => (actions i).state) }

/-- View one data/marker pair as a two-tape cleanup configuration. -/
def localCfg (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input) (i : Fin k) :
    Cfg 2 Bool (Fin 3) input where
  state := source.state.bind (fun phases => phases i)
  inputPos := source.inputPos
  workTapes := fun j => if j = 0 then source.workTapes (i.castAdd k)
    else source.workTapes (Fin.natAdd k i)
  workTapePos := fun j => if j = 0 then source.workTapePos (i.castAdd k)
    else source.workTapePos (Fin.natAdd k i)
  output := source.output

private theorem localCfg_symbols
    (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input) (i : Fin k) :
    (localCfg source i).workTapeSymbols = fun j =>
      if j = 0 then source.workTapeSymbols (i.castAdd k)
      else source.workTapeSymbols (Fin.natAdd k i) := by
  funext j
  by_cases hj : j = 0 <;> simp [localCfg, Cfg.workTapeSymbols, hj]

private theorem localCfg_inputSymbol (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input)
    (i : Fin k) : (localCfg source i).inputSymbol = source.inputSymbol := rfl

private theorem step_localCfg
    (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input) (i : Fin k) :
    localCfg ((parallel k).step source) i = machine.step (localCfg source i) := by
  cases hs : source.state with
  | none => simp [step, localCfg, hs]
  | some phases =>
    rw [step_apply_of_state hs, step_eq_action, localCfg_symbols, localCfg_inputSymbol]
    simp only [localCfg, hs, Option.bind_some, parallel]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp only [Action.apply_state]
      split_ifs with h
      · exact (h i).symm
      · rfl
    · simp [Action.apply, action_inputTape]
    · funext j
      rcases (show j = 0 ∨ j = 1 by lia) with rfl | rfl <;>
        simp [Action.apply, -Fin.natAdd_eq_addNat]
    · funext j
      rcases (show j = 0 ∨ j = 1 by lia) with rfl | rfl <;>
        simp [Action.apply, -Fin.natAdd_eq_addNat]
    · simp [Action.apply, action_output]

/-- Projecting a parallel run gives exactly the independent two-tape cleanup run. -/
theorem runFrom_localCfg (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input)
    (i : Fin k) (time : ℕ) :
    localCfg ((parallel k).runFrom source time) i =
      machine.runFrom (localCfg source i) time :=
  Function.Semiconj.iterate_right (f := fun source => localCfg source i)
    (fun source => step_localCfg source i) time source

private theorem step_frame (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input) :
    ((parallel k).step source).inputPos = source.inputPos ∧
      ((parallel k).step source).output = source.output := by
  cases hs : source.state <;> simp [step, parallel, hs, Action.apply]

private theorem runFrom_frame
    (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input) (time : ℕ) :
    ((parallel k).runFrom source time).inputPos = source.inputPos ∧
      ((parallel k).runFrom source time).output = source.output := by
  induction time with
  | zero => exact ⟨rfl, rfl⟩
  | succ time ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact ⟨(step_frame _).1.trans ih.1, (step_frame _).2.trans ih.2⟩

private theorem step_haltedLocals (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input)
    (h : ∀ i, (localCfg source i).state = none) :
    (parallel k).step source = source.withState (none : Option (Fin k → Option (Fin 3))) := by
  cases hs : source.state with
  | none =>
    apply Cfg.ext <;> simp [step, hs, Cfg.withState]
  | some phases =>
    have hp : phases = fun _ => none := by
      funext i
      simpa [localCfg, hs] using h i
    subst phases
    simp only [step, hs, parallel, action]
    refine Cfg.ext (by simp [Action.apply, Cfg.withState])
      (by simp [Action.apply, Cfg.withState]) ?_ ?_
      (by simp [Action.apply, Cfg.withState]) <;>
      funext i <;> induction i using Fin.addCases <;>
        simp [Action.apply, Cfg.withState, -Fin.natAdd_eq_addNat]

/-- If every pair is cleared by a common bound, the whole machine halts one step later. -/
theorem runFrom_parallel (source : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input)
    (time : ℕ)
    (h : ∀ i, machine.runFrom (localCfg source i) time =
      cfg input none source.inputPos (fun _ => none) (fun _ => none) 0 source.output) :
    (parallel k).runFrom source (time + 1) =
      ⟨none, source.inputPos, fun _ _ => none, fun _ => 0, source.output⟩ := by
  have hlocal (i : Fin k) :
      localCfg ((parallel k).runFrom source time) i =
        cfg input none source.inputPos (fun _ => none) (fun _ => none) 0 source.output := by
    rw [runFrom_localCfg, h]
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, step_haltedLocals _ (fun i => by
    rw [hlocal]; rfl)]
  refine Cfg.ext rfl (runFrom_frame source time).1 ?_ ?_ (runFrom_frame source time).2
  · funext j
    induction j using Fin.addCases with
    | left i =>
      simpa [localCfg, cfg, Cfg.withState, -Fin.natAdd_eq_addNat] using
        congrArg (fun c => c.workTapes 0) (hlocal i)
    | right i =>
      simpa [localCfg, cfg, Cfg.withState, -Fin.natAdd_eq_addNat] using
        congrArg (fun c => c.workTapes 1) (hlocal i)
  · funext j
    induction j using Fin.addCases with
    | left i =>
      simpa [localCfg, cfg, Cfg.withState, -Fin.natAdd_eq_addNat] using
        congrArg (fun c => c.workTapePos 0) (hlocal i)
    | right i =>
      simpa [localCfg, cfg, Cfg.withState, -Fin.natAdd_eq_addNat] using
        congrArg (fun c => c.workTapePos 1) (hlocal i)


end Turing.MultiTapeTM.ClearWork
