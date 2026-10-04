/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Initializing unary counters from the input length

`initializeUnary k` fills each of its `k` work tapes with `input.length + 1` true bits, starting
from blank tapes. It restores the input and work heads and leaves the output unchanged. The exact
run takes `2 * input.length + 2` transitions, independently of the input's contents.

These tapes provide the base for polynomial clocks. Preparing them is ordinary machine work;
their contents are not supplied as part of the initial configuration.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Scan the input while writing a unary word on each tape, then rewind all heads. -/
@[simps] def initializeUnary (k : ℕ) : MultiTapeTM k Bool Bool where
  q₀ := false
  tr rewind symbol _ :=
    match rewind, symbol with
    | false, some _ =>
      { inputTape := 1, workTapes := fun _ => (some (some true), 1),
        output := none, state := some false }
    | false, none =>
      { inputTape := -1, workTapes := fun _ => (some (some true), 0),
        output := none, state := some true }
    | true, some _ =>
      { inputTape := -1, workTapes := fun _ => (none, -1),
        output := none, state := some true }
    | true, none =>
      { inputTape := 1, workTapes := fun _ => (none, 0), output := none, state := none }

namespace InitializeUnary

variable {k : ℕ} (input output : List Bool)

/-- After scanning `index` input symbols, all work heads are at the end of the written prefix. -/
def forward (index : ℕ) (h : index ≤ input.length) : Cfg k Bool Bool input where
  state := some false
  inputPos := ⟨index + 1, by omega⟩
  workTapes := fun _ => tapeOfList (List.replicate index true)
  workTapePos := fun _ => index
  output := output

/-- While rewinding, the input head and all work heads have the same nonnegative position. -/
def backward (index : ℕ) (h : index ≤ input.length) : Cfg k Bool Bool input where
  state := some true
  inputPos := ⟨index, by omega⟩
  workTapes := fun _ => tapeOfList (List.replicate (input.length + 1) true)
  workTapePos := fun _ => index
  output := output

theorem step_forward (index : ℕ) (h : index < input.length) :
    (initializeUnary k).step (forward input output index (by omega)) =
      forward input output (index + 1) h := by
  rw [step_apply_of_state (q := false) rfl,
    inputSymbolInner index (by simp [forward, Nat.add_comm]) h]
  refine Cfg.ext rfl ?_ ?_ ?_ (by simp [initializeUnary, Action.apply, forward])
  · apply Fin.ext
    change (moveInputPos (forward input output index (by omega)).inputPos .pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by simp [forward]; omega)]
    rfl
  · funext i
    have hrep : List.replicate (index + 1) true = List.replicate index true ++ [true] := by
      simp [List.replicate_add]
    simp [initializeUnary, Action.apply, forward, hrep, tapeOfList_append_single]
  · funext i
    simp [initializeUnary, Action.apply, forward]

theorem step_end :
    (initializeUnary k).step (forward input output input.length le_rfl) =
      backward input output input.length le_rfl := by
  rw [step_apply_of_state (q := false) rfl,
    inputSymbol_eq_none_of_boundary (Or.inr rfl)]
  refine Cfg.ext rfl ?_ ?_ ?_ (by simp [initializeUnary, Action.apply, forward, backward])
  · apply Fin.ext
    change (moveInputPos (forward input output input.length le_rfl).inputPos .neg).val = _
    rw [moveInputPos_neg_of_ne_left _ (by simp [forward, Fin.ext_iff])]
    simp [forward, backward]
  · funext i
    have hrep : List.replicate (input.length + 1) true =
        List.replicate input.length true ++ [true] := by simp [List.replicate_add]
    simp [initializeUnary, Action.apply, forward, backward, hrep, tapeOfList_append_single]
  · funext i
    simp [initializeUnary, Action.apply, forward, backward]

theorem step_backward (index : ℕ) (h : index + 1 ≤ input.length) :
    (initializeUnary k).step (backward input output (index + 1) h) =
      backward input output index (by omega) := by
  rw [step_apply_of_state (q := true) rfl,
    inputSymbolInner index (by simp [backward, Nat.add_comm]) (by omega)]
  refine Cfg.ext rfl ?_ ?_ ?_ (by simp [initializeUnary, Action.apply, backward])
  · apply Fin.ext
    change (moveInputPos (backward input output (index + 1) h).inputPos .neg).val = _
    rw [moveInputPos_neg_of_ne_left _ (by simp [backward, Fin.ext_iff])]
    simp [backward]
  · rfl
  · funext i
    simp [initializeUnary, Action.apply, backward]

theorem step_start :
    (initializeUnary k).step (backward input output 0 (Nat.zero_le _)) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true) output := by
  rw [step_apply_of_state (q := true) rfl,
    inputSymbol_eq_none_of_boundary (Or.inl rfl)]
  refine Cfg.ext rfl ?_ rfl ?_ (by simp [initializeUnary, Action.apply, backward, wordsCfg])
  · apply Fin.ext
    change (moveInputPos (backward input output 0 (Nat.zero_le _)).inputPos .pos).val = _
    rw [moveInputPos_pos_of_ne_right _ (by simp [backward])]
    rfl
  · funext i
    simp [initializeUnary, Action.apply, backward, wordsCfg]

/-- The forward scan writes one true bit per input symbol. -/
theorem runFrom_forward (steps : ℕ) (h : steps ≤ input.length) :
    (initializeUnary k).runFrom (forward input output 0 (Nat.zero_le _)) steps =
      forward input output steps h := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [runFrom, Function.iterate_succ_apply']
    change (initializeUnary k).step
      ((initializeUnary k).runFrom (forward input output 0 (Nat.zero_le _)) steps) = _
    rw [ih (by omega), step_forward input output steps (by omega)]

/-- Rewinding restores every head and halts, without changing the counter words. -/
theorem runFrom_backward (index : ℕ) (h : index ≤ input.length) :
    (initializeUnary k).runFrom (backward input output index h) (index + 1) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true) output := by
  induction index with
  | zero => exact step_start input output
  | succ index ih =>
    rw [runFrom, Function.iterate_succ_apply]
    rw [step_backward input output index h]
    exact ih (by omega)

end InitializeUnary

/-- Preparing `input.length + 1` unary cells on each blank tape takes linear time, restores
every head, and leaves the existing output untouched. -/
theorem runFrom_initializeUnary (k : ℕ) (input output : List Bool) :
    (initializeUnary k).runFrom (wordsCfg input (some false) (fun _ => []) output)
      (2 * input.length + 2) =
      wordsCfg input none (fun _ => List.replicate (input.length + 1) true) output := by
  have hstart : wordsCfg input (some false) (fun _ => []) output =
      InitializeUnary.forward (k := k) input output 0 (Nat.zero_le _) := by
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    rfl
  have hscan : (initializeUnary k).runFrom
      (InitializeUnary.forward input output 0 (Nat.zero_le _)) (input.length + 1) =
      InitializeUnary.backward input output input.length le_rfl := by
    rw [runFrom, Function.iterate_succ_apply']
    change (initializeUnary k).step ((initializeUnary k).runFrom
      (InitializeUnary.forward input output 0 (Nat.zero_le _)) input.length) = _
    rw [InitializeUnary.runFrom_forward input output input.length le_rfl, InitializeUnary.step_end]
  rw [hstart, show 2 * input.length + 2 = (input.length + 1) + (input.length + 1) by omega,
    runFrom, Function.iterate_add_apply]
  change (initializeUnary k).runFrom ((initializeUnary k).runFrom
    (InitializeUnary.forward input output 0 (Nat.zero_le _)) (input.length + 1))
    (input.length + 1) = _
  rw [hscan, InitializeUnary.runFrom_backward]

end Turing.MultiTapeTM
