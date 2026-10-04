/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Machine.Replay
import CslibTests.MachineRuntime

/-! Checks for finite snapshots, joint-state replay, and its uniform machine certificate. -/

open Turing Turing.MultiTapeMachine Turing.MultiTapePTM Turing.MultiTapeTM

namespace MachineSnapshot

-- Negative positions, retained blanks, and overwriting a cell agree with the two-sided tape.
example : (((Tape.Snapshot.ofList [some true]).move .neg).write (some false)).move .pos =
    (⟨[some false], some true, []⟩ : Tape.Snapshot (Option Bool)) := by decide
example : ((⟨[some false], some true, []⟩ : Tape.Snapshot (Option Bool)).write none).move .neg =
    ⟨[], some false, [none]⟩ := by decide

open MachineRuntime

def adaptiveSnapshotResult (coins : Word) : Option Word × (Cache × Log) :=
  let (snapshot, state) := (adaptiveMachine.runSnapshotFromCoins [] cached coins
    (Snapshot.initial adaptiveMachine.initial)).run ([], [])
  (if snapshot.state.isNone then some snapshot.output else none, state)

-- The correspondence preserves the shared cache and the complete call log for every coin tape.
example (coins : Word) : adaptiveSnapshotResult coins = adaptiveResult coins := by
  have h := runSnapshotFromCoins_output adaptiveMachine cached coins
    (Snapshot.initial adaptiveMachine.initial) (adaptiveMachine.initialConfig [])
    (Snapshot.represents_initial _ _)
  exact congrArg (fun action => Id.run (action.run ([], []))) h

example : adaptiveSnapshotResult [false, true, false, true, false] =
    (some [true], ([([false], true), ([], false)],
      [(false, []), (true, [false]), (false, [false])])) := by decide

-- Resuming finite snapshots preserves pending requests and does not repeat prefix calls.
example (before after : Word) :
    adaptiveMachine.runSnapshotFromCoins [] cached (before ++ after)
        (Snapshot.initial adaptiveMachine.initial) =
      (adaptiveMachine.runSnapshotFromCoins [] cached before
        (Snapshot.initial adaptiveMachine.initial) >>=
          adaptiveMachine.runSnapshotFromCoins [] cached after) :=
  runSnapshotFromCoins_append _ _ _ _ _

def pending : Snapshot 0 Bool Unit Bool where
  state := some ()
  inputPos := 1
  workTapes := Fin.elim0
  output := [true]
  channels port := ⟨[port], Tape.Snapshot.ofList [some (!port)]⟩

-- Only the selected channel is cleared, and its reply head starts at the new word's first bit.
example : ((pending.receive true () [false, true]).channels true).queryBuffer = [] := by decide
example : (pending.receive true () [false, true]).answerSymbols true = some false := by decide
example : (pending.receive true () [false, true]).channels false = pending.channels false := rfl
example : (pending.receive true () [false, true]).output = [true] := by decide

abbrev logEncoding : List Word ↪ Word := listEncoding wordEncoding

def echoLog (_ : Fin 1) (request : Word) (log : List Word) : Word × List Word :=
  (request, request :: log)

theorem echoLog_poly (port : Fin 1) : IsPolyTime (pairEncoding wordEncoding logEncoding)
    (fun pair => pairEncoding wordEncoding logEncoding (echoLog port pair.1 pair.2)) :=
  (isPolyTime_fst _ _).pair ((isPolyTime_fst _ _).list_cons (isPolyTime_snd _ _))

-- A single certified replay machine handles arbitrarily long coin words and growing call logs.
-- The proof derives its space bound from request lengths; it assumes no simulation clock.
example : IsPolyTime wordEncoding (fun coins =>
    pairEncoding (machineSnapshotEncoding 0 1 (finiteEncoding (Fin 2))) logEncoding
      (Id.run ((bufferedSource.runSnapshotFromCoins (m := StateT (List Word) Id) []
        (fun port request log => pure (echoLog port request log)) coins
          (Snapshot.initial bufferedSource.initial)).run []))) := by
  let start := Snapshot.initial (k := 0) (Symbol := Bool) (Oracle := Fin 1) bufferedSource.initial
  let size := (machineSnapshotEncoding 0 1 (finiteEncoding (Fin 2)) start).length
  apply isPolyTime_runSnapshotFromCoins_of_growth bufferedSource echoLog echoLog_poly
    (snapshot := fun _ => start)
    (isPolyTime_const _ _) (isPolyTime_const _ []) (isPolyTime_input wordEncoding)
    (isPolyTime_const _ []) (fun _ _ => True) (fun _ => trivial)
    (reply := fun n => size + n) (growth := fun n => 2 * (size + n) + 1)
    (by fun_prop) (by fun_prop)
  intro coins port request log hrequest _
  refine ⟨trivial, hrequest, ?_⟩
  change (listEncoding wordEncoding (request :: log)).length ≤ _
  simp only [logEncoding, listEncoding_cons, length_pairEncoding, wordEncoding,
    Function.Embedding.refl_apply]
  change request.length ≤ size + coins.length at hrequest
  omega

end MachineSnapshot
