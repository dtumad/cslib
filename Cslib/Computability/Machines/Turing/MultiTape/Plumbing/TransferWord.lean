/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Mathlib.Data.Fin.VecNotation
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Transfer a word between work tapes

The three tapes hold a source word, an old destination word, and a blank marker tape.
`TransferWord.machine` replaces the destination by the source and optionally erases the source.
It scans both words to their end, writes a temporary marker for every visited cell, then
erases those markers on the way back. All heads return to zero; the ambient input and output
are preserved. In particular, replacing a long destination by a short word clears its old tail.

The full bound is `2 * max source.length target.length + 2`. The same two control states
work for every word length, and no comparison of alphabet symbols is needed.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.TransferWord

variable {Symbol : Type} {input : List Symbol}

/-- Copy or move a word from tape zero to tape one, using tape two as temporary workspace. -/
def machine (mark : Symbol) (erase : Bool) : MultiTapeTM 3 Symbol Bool where
  q₀ := false
  tr returning _ work :=
    if returning then
      if (work 2).isSome then
        { inputTape := 0,
          workTapes := fun i => (if i = 2 then some none else none, -1),
          output := none, state := some true }
      else
        { inputTape := 0, workTapes := fun _ => (none, 1), output := none, state := none }
    else if (work 0).isNone && (work 1).isNone then
      { inputTape := 0, workTapes := fun _ => (none, -1),
        output := none, state := some true }
    else
      { inputTape := 0,
        workTapes := fun i =>
          (if i = 0 then (if erase then some none else none)
            else if i = 1 then some (work 0) else some (some mark), 1),
        output := none, state := some false }

private def sourceTape (erase : Bool) (source : List Symbol) (position : ℕ) : ℤ → Option Symbol :=
  fun z => if erase && decide (z < position) then none else tapeOfList source z

private def targetTape (source target : List Symbol) (position : ℕ) : ℤ → Option Symbol :=
  fun z => if z < position then tapeOfList source z else tapeOfList target z

private def config (input : List Symbol) (state : Option Bool)
    (source target counter : ℤ → Option Symbol) (position : ℤ) (output : List Symbol) :
    Cfg 3 Symbol Bool input :=
  ⟨state, 1, ![source, target, counter], fun _ => position, output⟩

private def scanConfig (mark : Symbol) (erase : Bool) (source target : List Symbol)
    (position : ℕ) (output : List Symbol) : Cfg 3 Symbol Bool input :=
  config input (some false) (sourceTape erase source position) (targetTape source target position)
    (tapeOfList (List.replicate position mark)) position output

private theorem sourceTape_at (erase : Bool) (source : List Symbol) (position : ℕ) :
    sourceTape erase source position position = source[position]? := by
  simp [sourceTape]

private theorem targetTape_at (source target : List Symbol) (position : ℕ) :
    targetTape source target position position = target[position]? := by
  simp [targetTape]

private theorem update_sourceTape (erase : Bool) (source : List Symbol) (position : ℕ) :
    (if erase then Function.update (sourceTape erase source position) (position : ℤ) none
      else sourceTape erase source position) = sourceTape erase source (position + 1) := by
  cases erase with
  | false => funext z; simp [sourceTape]
  | true =>
    simp only [↓reduceIte]
    funext z
    by_cases hz : z = (position : ℤ)
    · subst z; simp [sourceTape]
    · rw [Function.update_of_ne hz]
      simp only [sourceTape, Bool.true_and, decide_eq_true_eq]
      have h : (z < (position : ℤ)) = (z < (position + 1 : ℕ)) := by lia
      simp only [h]

private theorem update_targetTape (source target : List Symbol) (position : ℕ) :
    Function.update (targetTape source target position) (position : ℤ) source[position]? =
      targetTape source target (position + 1) := by
  funext z
  by_cases hz : z = (position : ℤ)
  · subst z; simp [targetTape]
  · rw [Function.update_of_ne hz]
    simp only [targetTape]
    have h : (z < (position : ℤ)) = (z < (position + 1 : ℕ)) := by lia
    simp only [h]

private theorem step_scan (mark : Symbol) (erase : Bool) (source target : List Symbol)
    (position : ℕ) (output : List Symbol) (h : position < max source.length target.length) :
    (machine mark erase).step
      (scanConfig (input := input) mark erase source target position output) =
      scanConfig mark erase source target (position + 1) output := by
  have hread : ((source[position]?).isNone && (target[position]?).isNone) = false := by
    cases hs : source[position]? with
    | none =>
      have hslen := List.getElem?_eq_none_iff.mp hs
      have ht : position < target.length := by lia
      simp [List.getElem?_eq_getElem ht]
    | some value => simp
  simp only [step, scanConfig, config, machine, Cfg.workTapeSymbols]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sourceTape_at, targetTape_at, hread,
    Bool.false_eq_true, ↓reduceIte]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_
    (by simp [Action.apply]) (by simp [Action.apply])
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by lia) with rfl | rfl | rfl
  · simp only [Action.apply]
    cases erase with
    | false => simpa using update_sourceTape false source position
    | true => simpa using update_sourceTape true source position
  · simpa [Action.apply] using update_targetTape source target position
  · simpa [Action.apply, List.replicate_add] using
      (tapeOfList_append_single (List.replicate position mark) mark).symm

private theorem runFrom_scan (mark : Symbol) (erase : Bool) (source target : List Symbol)
    (output : List Symbol) (position : ℕ) (h : position ≤ max source.length target.length) :
    (machine mark erase).runFrom
      (scanConfig (input := input) mark erase source target 0 output) position =
      scanConfig mark erase source target position output := by
  induction position with
  | zero => rfl
  | succ position ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia)]
    exact step_scan mark erase source target position output (by lia)

private theorem sourceTape_zero (erase : Bool) (source : List Symbol) :
    sourceTape erase source 0 = tapeOfList source := by
  funext z
  cases z <;> simp [sourceTape, tapeOfList]

private theorem targetTape_zero (source target : List Symbol) :
    targetTape source target 0 = tapeOfList target := by
  funext z
  cases z <;> simp [targetTape, tapeOfList]

private theorem sourceTape_end (erase : Bool) (source : List Symbol) (position : ℕ)
    (h : source.length ≤ position) :
    sourceTape erase source position = tapeOfList (if erase then [] else source) := by
  cases erase with
  | false => funext z; simp [sourceTape]
  | true =>
    funext z
    by_cases hz : z < position
    · simp [sourceTape, hz]
    · have hblank := (tapeOfList_eq_none_iff source z).mpr (Or.inr (by lia))
      simp [sourceTape, hz, hblank]

private theorem targetTape_end (source target : List Symbol) (position : ℕ)
    (hs : source.length ≤ position) (ht : target.length ≤ position) :
    targetTape source target position = tapeOfList source := by
  funext z
  by_cases hz : z < position
  · simp [targetTape, hz]
  · have hsblank := (tapeOfList_eq_none_iff source z).mpr (Or.inr (by lia))
    have htblank := (tapeOfList_eq_none_iff target z).mpr (Or.inr (by lia))
    simp [targetTape, hz, hsblank, htblank]

private theorem step_scan_end (mark : Symbol) (erase : Bool) (source target output : List Symbol)
    (position : ℕ) (hs : source.length ≤ position) (ht : target.length ≤ position) :
    (machine mark erase).step
      (scanConfig (input := input) mark erase source target position output) =
      config input (some true) (tapeOfList (if erase then [] else source)) (tapeOfList source)
        (tapeOfList (List.replicate position mark)) (position - 1) output := by
  have hsource : source[position]? = none := List.getElem?_eq_none_iff.mpr hs
  have htarget : target[position]? = none := List.getElem?_eq_none_iff.mpr ht
  simp only [step, machine, scanConfig, config, Cfg.workTapeSymbols,
    Matrix.cons_val_zero, Matrix.cons_val_one, sourceTape_at, targetTape_at,
    hsource, htarget, Option.isNone_none, Bool.and_self, ↓reduceIte]
  simp [Action.apply, sourceTape_end erase source position hs,
    targetTape_end source target position hs ht, sub_eq_add_neg]

private theorem erase_last_counter (mark : Symbol) (count : ℕ) :
    Function.update (tapeOfList (List.replicate (count + 1) mark)) (count : ℤ) none =
      tapeOfList (List.replicate count mark) := by
  rw [show List.replicate (count + 1) mark = List.replicate count mark ++ [mark] by
    simp [List.replicate_add], tapeOfList_append_single]
  funext z
  by_cases hz : z = (count : ℤ)
  · subst z; simp
  · simp [hz]

private theorem step_return (mark : Symbol) (erase : Bool) (source target : ℤ → Option Symbol)
    (count : ℕ) (output : List Symbol) :
    (machine mark erase).step
      (config input (some true) source target (tapeOfList (List.replicate (count + 1) mark))
        count output) =
      config input (some true) source target (tapeOfList (List.replicate count mark))
        (count - 1) output := by
  simp only [step, config, machine, Cfg.workTapeSymbols]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    tapeOfList_ofNat, List.getElem?_replicate,
    Nat.lt_succ_self, ↓reduceIte, Option.isSome_some]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_
    (by simp [Action.apply, sub_eq_add_neg]) (by simp [Action.apply])
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by lia) with rfl | rfl | rfl
  · simp [Action.apply]
  · simp [Action.apply]
  · simpa [Action.apply] using erase_last_counter mark count

private theorem runFrom_return (mark : Symbol) (erase : Bool) (source target : ℤ → Option Symbol)
    (count : ℕ) (output : List Symbol) :
    (machine mark erase).runFrom
      (config input (some true) source target (tapeOfList (List.replicate count mark))
        (count - 1) output) (count + 1) =
      config input none source target (fun _ => none) 0 output := by
  induction count with
  | zero =>
    rw [runFrom_one]
    simp [step, machine, config, Cfg.workTapeSymbols, Action.apply]
  | succ count ih =>
    rw [runFrom, Function.iterate_succ_apply, ← runFrom]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [step_return]
    exact ih

private theorem config_words (source target output : List Symbol) (state : Option Bool) :
    config input state (tapeOfList source) (tapeOfList target) (fun _ => none) 0 output =
      wordsCfg input state ![source, target, []] output := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by lia) with rfl | rfl | rfl <;>
    simp [config, wordsCfg]

/-- Replace a destination word, clear any remaining tail, and restore all heads and workspace. -/
theorem runFrom_machine (mark : Symbol) (erase : Bool) (source target output : List Symbol) :
    (machine mark erase).runFrom
      (wordsCfg input (some (machine mark erase).q₀) ![source, target, []] output)
      (2 * max source.length target.length + 2) =
      wordsCfg input none ![if erase then [] else source, source, []] output := by
  let count := max source.length target.length
  have hstart : wordsCfg input (some (machine mark erase).q₀) ![source, target, []] output =
      scanConfig mark erase source target 0 output := by
    rw [scanConfig, sourceTape_zero, targetTape_zero]
    simpa [machine] using (config_words (input := input) source target output (some false)).symm
  rw [hstart, show 2 * max source.length target.length + 2 = count + ((count + 1) + 1) by
    dsimp [count]; lia]
  rw [runFrom_add, runFrom_scan _ _ _ _ _ _ le_rfl, runFrom, Function.iterate_succ_apply,
    ← runFrom, step_scan_end _ _ _ _ _ _ (le_max_left _ _) (le_max_right _ _), runFrom_return,
    config_words]

end Turing.MultiTapeTM.TransferWord
