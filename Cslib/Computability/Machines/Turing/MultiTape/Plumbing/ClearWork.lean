/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Clearing a work tape using a record of visited cells

Tape zero contains arbitrary data, including blank gaps. Tape one records a contiguous visited
interval: the origin is marked `true`, other visited cells `false`, and unvisited cells blank.
Both heads occupy the same position in that interval.

The machine scans to the left endpoint, sweeps right while erasing the data and all non-origin
markers, and returns to the origin. It then erases the last marker and halts with both tapes
blank and both heads at zero. Input position and accumulated output are preserved.

This is the cleanup operation needed when a bounded loop repeatedly invokes a machine with
scratch tapes. The companion markers let cleanup cross blank gaps and handle negative head
positions. They must be maintained by the calling simulation; this module does not assume
arbitrary machine output is already in word-holding normal form.

`runFrom_clear` gives the complete configuration and exact execution budget.
`runFrom_clear_le` bounds the budget by `5 * time + 5` when the visited interval lies within
`[-time, time]`. The shared `extendTapes` combinator can place this two-tape routine among
any number of other tapes.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.ClearWork

/-- Clear a data tape and its interval markers, then restore both heads to the origin. -/
def machine : MultiTapeTM 2 Bool (Fin 3) where
  q₀ := 0
  tr phase _ work :=
    if phase = 0 then
      { inputTape := 0, workTapes := fun _ => (none, if work 1 = none then 1 else -1),
        output := none, state := some (if work 1 = none then 1 else 0) }
    else if phase = 1 then
      if work 1 = none then
        { inputTape := 0, workTapes := fun _ => (none, -1), output := none, state := some 2 }
      else
        { inputTape := 0,
          workTapes := fun i => (some (if i = 1 ∧ work 1 = some true then some true else none), 1),
          output := none, state := some 1 }
    else if work 1 = some true then
      { inputTape := 0, workTapes := fun _ => (some none, 0), output := none, state := none }
    else
      { inputTape := 0, workTapes := fun _ => (none, -1), output := none, state := some 2 }

/-- The two synchronized work heads, with an arbitrary input position and output prefix. -/
def cfg (input : List Bool) (state : Option (Fin 3)) (inputPos : Fin (input.length + 2))
    (data marker : ℤ → Option Bool) (position : ℤ) (output : List Bool) :
    Cfg 2 Bool (Fin 3) input :=
  ⟨state, inputPos, (fun i => if i = 0 then data else marker), fun _ => position, output⟩

/-- A contiguous visited interval with a distinguished origin. -/
def marks (lo hi : ℤ) : ℤ → Option Bool :=
  fun z => if lo ≤ z ∧ z ≤ hi then some (decide (z = 0)) else none

variable {input : List Bool} {inputPos : Fin (input.length + 2)}
variable {data marker : ℤ → Option Bool} {position : ℤ} {output : List Bool}

private theorem step_left (h : marker position ≠ none) :
    machine.step (cfg input (some 0) inputPos data marker position output) =
      cfg input (some 0) inputPos data marker (position - 1) output := by
  simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h, sub_eq_add_neg]

private theorem step_turn_right (h : marker position = none) :
    machine.step (cfg input (some 0) inputPos data marker position output) =
      cfg input (some 1) inputPos data marker (position + 1) output := by
  simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h]

private theorem step_sweep (h : marker position ≠ none) :
    machine.step (cfg input (some 1) inputPos data marker position output) =
      cfg input (some 1) inputPos (Function.update data position none)
        (Function.update marker position (if marker position = some true then some true else none))
        (position + 1) output := by
  refine Cfg.ext (by simp [machine, step, cfg, Cfg.workTapeSymbols, h])
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h]) ?_
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h])
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h])
  funext i
  rcases (show i = 0 ∨ i = 1 by lia) with rfl | rfl <;>
    simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h]

private theorem step_turn_left (h : marker position = none) :
    machine.step (cfg input (some 1) inputPos data marker position output) =
      cfg input (some 2) inputPos data marker (position - 1) output := by
  simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h, sub_eq_add_neg]

private theorem step_return (h : marker position ≠ some true) :
    machine.step (cfg input (some 2) inputPos data marker position output) =
      cfg input (some 2) inputPos data marker (position - 1) output := by
  simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h, sub_eq_add_neg]

private theorem step_halt (h : marker position = some true) :
    machine.step (cfg input (some 2) inputPos data marker position output) =
      cfg input none inputPos (Function.update data position none)
        (Function.update marker position none) position output := by
  refine Cfg.ext (by simp [machine, step, cfg, Cfg.workTapeSymbols, h])
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h]) ?_
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h])
    (by simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h])
  funext i
  rcases (show i = 0 ∨ i = 1 by lia) with rfl | rfl <;>
    simp [machine, step, cfg, Action.apply, Cfg.workTapeSymbols, h]

private theorem runFrom_left (lo hi : ℤ) (count : ℕ) (h : lo + count ≤ hi) :
    machine.runFrom (cfg input (some 0) inputPos data (marks lo hi) (lo + count) output)
      (count + 1) =
      cfg input (some 0) inputPos data (marks lo hi) (lo - 1) output := by
  induction count with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [runFrom_one, step_left (by simp [marks]; lia)]
  | succ count ih =>
    rw [runFrom, Function.iterate_succ_apply, ← runFrom]
    rw [step_left (by simp [marks]; lia)]
    convert ih (by lia) using 1
    congr 2
    lia

private def dataTail (data : ℤ → Option Bool) (position : ℤ) : ℤ → Option Bool :=
  fun z => if position ≤ z then data z else none

private def markTail (hi position : ℤ) : ℤ → Option Bool :=
  fun z => if z = 0 then some true else if position ≤ z ∧ z ≤ hi then some false else none

private theorem update_dataTail (data : ℤ → Option Bool) (position : ℤ) :
    Function.update (dataTail data position) position none = dataTail data (position + 1) := by
  funext z
  by_cases h : z = position
  · subst z; simp [dataTail]
  · simp only [Function.update_of_ne h, dataTail]
    have : (position ≤ z) = (position + 1 ≤ z) := by lia
    simp only [this]

private theorem update_markTail (hi position : ℤ) :
    Function.update (markTail hi position) position
      (if markTail hi position position = some true then some true else none) =
        markTail hi (position + 1) := by
  funext z
  by_cases h : z = position
  · subst z
    by_cases hp : position = 0
    · subst position; simp [markTail]
    · by_cases hh : position ≤ hi <;> simp [markTail, hp, hh]
  · simp only [Function.update_of_ne h, markTail]
    have : (position ≤ z) = (position + 1 ≤ z) := by lia
    simp only [this]

private theorem runFrom_sweep (hi position : ℤ) (count : ℕ) (h : position + count ≤ hi + 1) :
    machine.runFrom
      (cfg input (some 1) inputPos (dataTail data position) (markTail hi position) position output)
      count =
      cfg input (some 1) inputPos (dataTail data (position + count))
        (markTail hi (position + count)) (position + count) output := by
  induction count generalizing position with
  | zero => simp
  | succ count ih =>
    have hp : position ≤ hi := by lia
    rw [runFrom, Function.iterate_succ_apply, ← runFrom]
    rw [step_sweep (by by_cases hz : position = 0 <;> simp [markTail, hp, hz]),
      update_dataTail, update_markTail]
    simpa [add_assoc, add_comm, add_left_comm] using ih (position + 1) (by lia)

private def origin : ℤ → Option Bool := fun z => if z = 0 then some true else none

private theorem runFrom_return (count : ℕ) :
    machine.runFrom (cfg input (some 2) inputPos (fun _ => none) origin count output)
      (count + 1) =
      cfg input none inputPos (fun _ => none) (fun _ => none) 0 output := by
  induction count with
  | zero =>
    rw [runFrom_one, step_halt (by simp [origin])]
    congr 1
    · funext z; simp
    · funext z; by_cases hz : z = 0 <;> simp [origin, hz]
  | succ count ih =>
    rw [runFrom, Function.iterate_succ_apply, ← runFrom]
    rw [step_return (by simp [origin]; lia)]
    simpa using ih

/-- Erase the entire visited interval, reset both work heads, and preserve input and output. -/
theorem runFrom_clear (lo hi position : ℤ)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hpos : lo ≤ position ∧ position ≤ hi)
    (hdata : ∀ z, z < lo ∨ hi < z → data z = none) :
    machine.runFrom (cfg input (some machine.q₀) inputPos data (marks lo hi) position output)
      ((position - lo).toNat + (hi - lo).toNat + hi.toNat + 5) =
      cfg input none inputPos (fun _ => none) (fun _ => none) 0 output := by
  let left := (position - lo).toNat
  let width := (hi - lo).toNat + 1
  have hleft : (left : ℤ) = position - lo := Int.toNat_of_nonneg (by lia)
  have hwidth : (width : ℤ) = hi - lo + 1 := by
    simp only [width, Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (by lia : 0 ≤ hi - lo)]
  have hleftRun := runFrom_left (inputPos := inputPos) (data := data) (output := output)
    lo hi left (by lia)
  have hmarks : marks lo hi = markTail hi lo := by
    funext z
    by_cases hz : z = 0
    · subst z; simp [marks, markTail, hlo, hhi]
    · simp [marks, markTail, hz]
  have hdataStart : data = dataTail data lo := by
    funext z
    by_cases hz : lo ≤ z
    · simp [dataTail, hz]
    · simp [dataTail, hz, hdata z (Or.inl (by lia))]
  have hdataEnd : dataTail data (hi + 1) = fun _ => none := by
    funext z
    by_cases hz : hi + 1 ≤ z
    · simp [dataTail, hz, hdata z (Or.inr (by lia))]
    · simp [dataTail, hz]
  have hmarkEnd : markTail hi (hi + 1) = origin := by
    funext z
    simp only [markTail, origin]
    by_cases hz : z = 0
    · simp [hz]
    · have : ¬(hi + 1 ≤ z ∧ z ≤ hi) := by lia
      simp [hz, this]
  have hsweep := runFrom_sweep (inputPos := inputPos) (data := data) (output := output)
    hi lo width (by lia)
  have hloEnd : lo + width = hi + 1 := by lia
  rw [hloEnd, hdataEnd, hmarkEnd] at hsweep
  have htime :
      (position - lo).toNat + (hi - lo).toNat + hi.toNat + 5 =
        (left + 1) + 1 + width + 1 + (hi.toNat + 1) := by simp [left, width]; lia
  rw [htime, runFrom_add _ _ ((left + 1) + 1 + width + 1) (hi.toNat + 1),
    runFrom_add _ _ ((left + 1) + 1 + width) 1,
    runFrom_add _ _ ((left + 1) + 1) width, runFrom_add _ _ (left + 1) 1]
  have hstart : position = lo + left := by lia
  change machine.runFrom
    (machine.runFrom (machine.runFrom (machine.runFrom
      (machine.runFrom (cfg input (some 0) inputPos data (marks lo hi) position output)
        (left + 1)) 1) width) 1) (hi.toNat + 1) = _
  rw [hstart, hleftRun, runFrom_one machine
    (cfg input (some 0) inputPos data (marks lo hi) (lo - 1) output),
    step_turn_right (by simp [marks])]
  have hposStart : lo - 1 + 1 = lo := by lia
  rw [hposStart]
  rw [hmarks, hdataStart, hsweep, runFrom_one]
  rw [step_turn_left (by simp [origin, show hi + 1 ≠ 0 by lia])]
  have hposEnd : hi + 1 - 1 = (hi.toNat : ℤ) := by simp [Int.toNat_of_nonneg hhi]
  rw [hposEnd, runFrom_return]


/-- A visited interval inside `[-time, time]` can be cleared with linear overhead. -/
theorem runFrom_clear_le (lo hi position : ℤ) (time : ℕ)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hpos : lo ≤ position ∧ position ≤ hi)
    (hrange : -(time : ℤ) ≤ lo ∧ hi ≤ time)
    (hdata : ∀ z, z < lo ∨ hi < z → data z = none) :
    machine.runFrom (cfg input (some machine.q₀) inputPos data (marks lo hi) position output)
      (5 * time + 5) =
      cfg input none inputPos (fun _ => none) (fun _ => none) 0 output := by
  have hrun := runFrom_clear (inputPos := inputPos) (output := output)
    lo hi position hlo hhi hpos hdata
  have hbound :
      (position - lo).toNat + (hi - lo).toNat + hi.toNat + 5 ≤ 5 * time + 5 := by
    lia
  rw [runFrom_eq_of_halt _ _ hbound (by rw [hrun]; rfl)]
  exact hrun

end Turing.MultiTapeTM.ClearWork
