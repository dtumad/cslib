/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TrackWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWorkParallel
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputPrefix

/-!
# Restoring scratch tapes after a computation

`restoreWork` compiles an arbitrary halting binary machine into a routine that returns with
all work tapes blank, every work head at zero, and the input head at its starting position.
The output is unchanged. The construction has fixed finite control whenever the source does.

The source is simulated with companion tapes recording its visited intervals. The recorded
intervals are then cleared in parallel, and the shared input rewind restores the input head.
A source bound of `time` becomes `7 * time + input.length + 9`, including initialization,
simulation, cleanup, and the input rewind. No clock or clean workspace is supplied for free.

`runFrom_restoreWork_output` gives a full configuration contract with an arbitrary output
prefix. It is the reusable-call interface needed by bounded loops invoking a certified
polynomial-time computation repeatedly.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM

variable {k : ℕ} {State : Type} {input : List Bool}

namespace RestoreWork

private theorem runFrom_cleanup (source : Cfg k Bool State input) (lo hi : Fin k → ℤ) (time : ℕ)
    (h : TrackWork.Valid source lo hi time) :
    (ClearWork.parallel k).runFrom
      ((TrackWork.ready source (fun i => ClearWork.marks (lo i) (hi i))).withState
        (some (ClearWork.parallel k).q₀)) (5 * time + 6) =
      ⟨none, source.inputPos, fun _ _ => none, fun _ => 0, source.output⟩ := by
  apply ClearWork.runFrom_parallel _ (5 * time + 5)
  intro i
  have hcfg :
      ClearWork.localCfg
        ((TrackWork.ready source (fun i => ClearWork.marks (lo i) (hi i))).withState
          (some (ClearWork.parallel k).q₀)) i =
      ClearWork.cfg input (some ClearWork.machine.q₀) source.inputPos (source.workTapes i)
        (ClearWork.marks (lo i) (hi i)) (source.workTapePos i) source.output := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;>
      funext j <;> rcases (show j = 0 ∨ j = 1 by lia) with rfl | rfl <;>
        simp [ClearWork.localCfg, ClearWork.cfg, TrackWork.ready, TrackWork.cfg, Cfg.withState,
          -Fin.natAdd_eq_addNat]
  rw [hcfg]
  obtain ⟨hlo, hhi, hlower, hupper, hleft, hright, hdata⟩ := h i
  exact ClearWork.runFrom_clear_le (lo i) (hi i) (source.workTapePos i) time
    hlo hhi ⟨hleft, hright⟩ ⟨hlower, hupper⟩ hdata

end RestoreWork

/-- Preserve a machine's output while restoring all scratch tapes and heads before halting. -/
def restoreWork (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + k) Bool
      (Option (State ⊕ Option State) ⊕ ((Fin k → Option (Fin 3)) ⊕ RewindState)) :=
  (TrackWork.machine tm).seq
    ((ClearWork.parallel k).seq ((rewindInput Bool).extendTapes (noTapes (k + k))))

/-- The complete computation, cleanup, and input rewind have linear overhead. -/
theorem runFrom_restoreWork (tm : MultiTapeTM k Bool State) (time : ℕ)
    (hhalt : (tm.runFrom (tm.initCfg input) time).state = none) :
    tm.restoreWork.runFrom (tm.restoreWork.initCfg input) (7 * time + input.length + 9) =
      wordsCfg input none (fun _ => []) (tm.runFrom (tm.initCfg input) time).output := by
  obtain ⟨lo, hi, hvalid, htrack⟩ := TrackWork.runFrom_machine tm input time
  let source := tm.runFrom (tm.initCfg input) time
  let mid := TrackWork.ready source (fun i => ClearWork.marks (lo i) (hi i))
  let clean : Cfg (k + k) Bool (Fin k → Option (Fin 3)) input :=
    ⟨none, source.inputPos, fun _ _ => none, fun _ => 0, source.output⟩
  have hmid : mid.Halted := by
    simp only [Cfg.Halted, mid, TrackWork.ready, TrackWork.cfg, source, hhalt, Option.map_none]
  have hclear : (ClearWork.parallel k).runFrom
      (mid.withState (some (ClearWork.parallel k).q₀)) (5 * time + 6) = clean :=
    RestoreWork.runFrom_cleanup source lo hi time hvalid
  have hrewind : ((rewindInput Bool).extendTapes (noTapes (k + k))).runFrom
      (clean.withState (some ((rewindInput Bool).extendTapes (noTapes (k + k))).q₀))
        (input.length + 2) =
        wordsCfg input none (fun _ => []) source.output := by
    have hr := runFrom_rewindInput_noTapes source.inputPos (fun _ : Fin (k + k) => fun _ => none)
      (fun _ => 0) source.output
    have hbound : source.inputPos.val - 1 + 2 ≤ input.length + 2 := by
      have := source.inputPos.isLt
      lia
    change ((rewindInput Bool).extendTapes (noTapes (k + k))).runFrom
      ⟨some ((rewindInput Bool).extendTapes (noTapes (k + k))).q₀, source.inputPos,
        fun _ _ => none, fun _ => 0, source.output⟩ _ = _
    rw [runFrom_eq_of_halt _ _ hbound (by rw [hr]), hr]
    simp [wordsCfg]
  have htail :
      ((ClearWork.parallel k).seq ((rewindInput Bool).extendTapes (noTapes (k + k)))).runFrom
        (mid.withState
          (some ((ClearWork.parallel k).seq ((rewindInput Bool).extendTapes (noTapes (k + k)))).q₀))
        ((5 * time + 6) + (input.length + 2)) =
      wordsCfg input none (fun _ => []) source.output := by
    simpa [Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState, Cfg.withState, wordsCfg, seq]
      using runFrom_seq hclear rfl hrewind rfl
  have hresult := runFrom_seq htrack hmid htail rfl
  have htime : (2 * time + 1) + ((5 * time + 6) + (input.length + 2)) =
      7 * time + input.length + 9 := by lia
  simpa [restoreWork, Sequential.leftCfg, Sequential.rightCfg, Cfg.mapState, wordsCfg,
    htime, source, seq] using hresult

/-- A restored routine appends its result to any existing output and leaves a fresh workspace. -/
theorem runFrom_restoreWork_output (tm : MultiTapeTM k Bool State) (time : ℕ)
    (hhalt : (tm.runFrom (tm.initCfg input) time).state = none) (output : List Bool) :
    tm.restoreWork.runFrom
      (wordsCfg input (some tm.restoreWork.q₀) (fun _ => []) output)
      (7 * time + input.length + 9) =
      wordsCfg input none (fun _ => [])
        (output ++ (tm.runFrom (tm.initCfg input) time).output) := by
  simpa [wordsCfg, Cfg.prependOutput] using
    (runFrom_prependOutput tm.restoreWork output (tm.restoreWork.initCfg input)
      (7 * time + input.length + 9)).trans
        (congrArg (Cfg.prependOutput · output) (runFrom_restoreWork tm time hhalt))

end Turing.MultiTapeTM
