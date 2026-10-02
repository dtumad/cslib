/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Copying a unary parameter to the output

`copyParameter k` copies the leading true bits and their false delimiter to the output, then
uses the shared `rewindInput` routine to restore the input head. On
`replicate n true ++ false :: input` it takes `2 * n + 3` steps. It preserves every work tape
and work head, and appends to any existing output.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace CopyParameter

/-- The parameter scan followed by the shared input rewind. -/
abbrev Control := Unit ⊕ RewindState

/-- Copy the leading true bits and their false delimiter, stopping on the delimiter. -/
@[simps] def scan (k : ℕ) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ symbol _ :=
    { inputTape := if symbol = some true then 1 else 0
      workTapes := fun _ => (none, 0)
      output := symbol
      state := if symbol = some true then some () else none }

end CopyParameter

/-- Copy the unary parameter and delimiter, then rewind to the first input cell. -/
def copyParameter (k : ℕ) : MultiTapeTM k Bool CopyParameter.Control :=
  (CopyParameter.scan k).seq (rewindInput k Bool)

namespace CopyParameter

variable {k n : ℕ} {State : Type*} {input : List Bool}
variable (cfg : Cfg k Bool State (List.replicate n true ++ false :: input))

/-- During the scan, only the input head and output prefix change. -/
def forward (index : ℕ) (h : index ≤ n) :
    Cfg k Bool Unit (List.replicate n true ++ false :: input) :=
  { cfg.withState (some ()) with
    inputPos := ⟨index + 1, by simp; omega⟩
    output := cfg.output ++ List.replicate index true }

/-- The completed prefix, with the head still on the delimiter. -/
def finished : Cfg k Bool Unit (List.replicate n true ++ false :: input) :=
  { cfg.withState none with
    inputPos := ⟨n + 1, by simp⟩
    output := cfg.output ++ (List.replicate n true ++ [false]) }

theorem step_forward (index : ℕ) (h : index < n) :
    (scan k).step (forward cfg index (by omega)) =
      forward cfg (index + 1) h := by
  rw [step_apply_of_state (q := ()) rfl,
    inputSymbolInner index (by simp [forward, Nat.add_comm]) (by simp; omega),
    List.getElem_append_left (by simpa using h), List.getElem_replicate]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · apply Fin.ext
    change (moveInputPos (forward cfg index (by omega)).inputPos .pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by simp [forward]; omega)]
    rfl
  · funext i
    simp [scan, Action.apply, forward]
  · simp [scan, Action.apply, forward, List.replicate_add, List.append_assoc]

theorem step_delimiter :
    (scan k).step (forward cfg n le_rfl) = finished cfg := by
  rw [step_apply_of_state (q := ()) rfl,
    inputSymbolInner n (by simp [forward, Nat.add_comm]) (by simp),
    List.getElem_append_right (by simp)]
  simp only [List.length_replicate, Nat.sub_self, List.getElem_cons_zero]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [scan, Action.apply, forward, finished]
  · funext i
    simp [scan, Action.apply, forward, finished]
  · simp [scan, Action.apply, forward, finished, List.append_assoc]

/-- Copy the initial true bits, one per transition. -/
theorem runFrom_forward (steps : ℕ) (h : steps ≤ n) :
    (scan k).runFrom (forward cfg 0 (Nat.zero_le _)) steps = forward cfg steps h := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [runFrom, Function.iterate_succ_apply']
    change (scan k).step ((scan k).runFrom (forward cfg 0 (Nat.zero_le _)) steps) = _
    rw [ih (by omega), step_forward cfg steps (by omega)]

/-- Copy the parameter and delimiter in `n + 1` transitions. -/
theorem runFrom_scan (hhead : cfg.inputPos.val = 1) :
    (scan k).runFrom (cfg.withState (some ())) (n + 1) = finished cfg := by
  have hstart : cfg.withState (some ()) = forward cfg 0 (Nat.zero_le _) := by
    refine Cfg.ext rfl (Fin.ext ?_) rfl rfl (by simp [forward])
    exact hhead
  rw [hstart, runFrom, Function.iterate_succ_apply', ← runFrom,
    runFrom_forward cfg n le_rfl, step_delimiter]

end CopyParameter

/-- Copying the unary parameter costs linear time, restores the input head, and preserves all
work tapes and work heads. The existing output is retained before the copied prefix. -/
theorem runFrom_copyParameter {k n : ℕ} {State : Type*} {input : List Bool}
    (cfg : Cfg k Bool State (List.replicate n true ++ false :: input))
    (hhead : cfg.inputPos.val = 1) :
    (copyParameter k).runFrom (cfg.withState (some (copyParameter k).q₀)) (2 * n + 3) =
      (cfg.withState (none : Option CopyParameter.Control)).withOutput
        (cfg.output ++ (List.replicate n true ++ [false])) := by
  have hcopy := CopyParameter.runFrom_scan cfg hhead
  have hrewind : (rewindInput k Bool).runFrom
      ((CopyParameter.finished cfg).withState (some (rewindInput k Bool).q₀)) (n + 2) =
      (cfg.withState (none : Option RewindState)).withOutput
        (cfg.output ++ (List.replicate n true ++ [false])) := by
    have h := runFrom_rewindInput (CopyParameter.finished cfg).inputPos cfg.workTapes
      cfg.workTapePos (CopyParameter.finished cfg).output
    have hpos : (1 : Fin ((List.replicate n true ++ false :: input).length + 2)) =
        cfg.inputPos := Fin.ext (by simpa using hhead.symm)
    simpa [CopyParameter.finished, Cfg.withState, Cfg.withOutput, hpos] using h
  have hseq := runFrom_seq hcopy rfl hrewind rfl
  simpa [copyParameter, seq, CopyParameter.scan, Sequential.leftCfg, Sequential.rightCfg,
    Cfg.mapState, Cfg.withState, Cfg.withOutput, show n + 1 + (n + 2) = 2 * n + 3 by omega]
    using hseq

end Turing.MultiTapeTM
