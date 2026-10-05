/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Replay
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Rewind

/-!
# A uniform machine certificate for adaptive rewinding

The selector inspects the first joint result. Three uses of the certified interpreter implement
the first execution, replay of its prefix, and the second suffix. A common representation invariant
covers both suffixes. Selecting the point, resetting handler state, and copying the fixed private
tape all have machine certificates; no replay or rewind clock is assumed.
-/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {α State S : Type} {k ports : ℕ} [Finite State]
  {input : α → Word} {control : State ↪ Word} {stateEncoding : S ↪ Word}

/-- Adaptive rewinding is uniformly polynomial time for certified handlers, selection, and restart.
The invariant counts source transitions from the original start in each execution. Restarting
preserves it at the selected position, so both runs use the same representation-size bound. -/
theorem isPolyTime_rewindSnapshotFromCoins
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Word × S)
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => pairEncoding wordEncoding stateEncoding (handler port pair.1 pair.2)))
    (choose : Snapshot k Bool State (Fin ports) × S → ℕ) (restart : S → S)
    (hchoose : IsPolyTime (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
      (fun pair => unaryEncoding (choose pair)))
    (hrestart : IsPolyTime stateEncoding (fun st => stateEncoding (restart st)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word} {state : α → S}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    (invariant : α → ℕ → Snapshot k Bool State (Fin ports) × S → Prop)
    (hinit : ∀ a, invariant a 0 (snapshot a, state a))
    (hstep : ∀ a index pair bit, index < (coins a).length → invariant a index pair →
      invariant a (index + 1)
        (Id.run ((machine.stepSnapshot (m := StateT S Id) (word a)
          (fun port request st => pure (handler port request st)) bit pair.1).run pair.2)))
    (hreset : ∀ a index pair, index ≤ (coins a).length → invariant a index pair →
      invariant a index (pair.1, restart pair.2))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ a index pair, index ≤ (coins a).length → invariant a index pair →
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding pair).length ≤
        size (input a).length) :
    IsPolyTime input (fun a =>
      pairEncoding (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
        (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
        (machine.rewindSnapshotFromCoins (word a) handler (coins a) (snapshot a) (state a)
          choose restart)) := by
  let run (a : α) (tape : Word) (pair : Snapshot k Bool State (Fin ports) × S) :=
    Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
      (fun port request st => pure (handler port request st)) tape pair.1).run pair.2)
  have hrun (a : α) (tape : Word) (pair : Snapshot k Bool State (Fin ports) × S) (index : ℕ)
      (hbudget : index + tape.length ≤ (coins a).length) (hinv : invariant a index pair) :
      invariant a (index + tape.length) (run a tape pair) := by
    apply runSnapshotFromCoins_stateT_spec machine _ tape pair.1 pair.2
      (fun consumed => invariant a (index + consumed)) (by simpa using hinv)
    intro consumed current bit hi hcurrent
    simpa only [Nat.add_assoc] using
      hstep a (index + consumed) current bit (by omega) hcurrent
  have hfirst := isPolyTime_runSnapshotFromCoins machine handler hhandler hs hw hc hst hpoly
    (fun a consumed hconsumed => hsize a consumed.length _ hconsumed.length_le (by
      simpa using hrun a consumed (snapshot a, state a) 0
        (by simpa using hconsumed.length_le) (hinit a)))
  let first (a : α) := run a (coins a) (snapshot a, state a)
  have hindex := hchoose.comp_encoded (f := first) hfirst
  have hbefore := isPolyTime_runSnapshotFromCoins machine handler hhandler hs hw
    (hc.take hindex) hst hpoly (fun a consumed hconsumed => by
      have hlen := hconsumed.length_le.trans (List.take_prefix _ _).length_le
      exact hsize a consumed.length _ hlen (by
        simpa using hrun a consumed (snapshot a, state a) 0 (by simpa using hlen) (hinit a)))
  let saved (a : α) := run a ((coins a).take (choose (first a))) (snapshot a, state a)
  have hsecond := isPolyTime_runSnapshotFromCoins machine handler hhandler hbefore.fst hw
    (hc.drop hindex) (hrestart.comp_encoded (f := fun a => (saved a).2) hbefore.snd) hpoly
    (fun a consumed hconsumed => by
      have hbeforeLength := (List.take_prefix (choose (first a)) (coins a)).length_le
      have hbudget : ((coins a).take (choose (first a))).length + consumed.length ≤
          (coins a).length := by
        have := hconsumed.length_le
        simp only [List.length_drop, List.length_take] at *
        omega
      apply hsize a _ _ hbudget
      apply hrun a consumed ((saved a).1, restart (saved a).2) _ hbudget
      apply hreset a _ (saved a) hbeforeLength
      simpa using hrun a ((coins a).take (choose (first a))) (snapshot a, state a) 0
        (by simp) (hinit a))
  exact hfirst.pair hsecond

omit [Finite State] in
/-- A certified aborting interpreter supports adaptive replay without a successful fallback.
The three calls retain the original coin suffix; absent results remain absent throughout. -/
theorem isPolyTime_rewindSnapshotFromCoins?
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Option (Word × S))
    (hrun : IsPolyTime (pairEncoding wordEncoding (pairEncoding wordEncoding
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)))
      (fun arg => optionEncoding (pairEncoding (machineSnapshotEncoding k ports control)
        stateEncoding) ((machine.runSnapshotFromCoins (m := StateT S Option) arg.1 handler
          arg.2.1 arg.2.2.1).run arg.2.2.2)))
    (choose : Snapshot k Bool State (Fin ports) × S → ℕ) (restart : S → S)
    (hchoose : IsPolyTime (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
      (fun pair => unaryEncoding (choose pair)))
    (hrestart : IsPolyTime stateEncoding (fun st => stateEncoding (restart st)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word} {state : α → S}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => stateEncoding (state a))) :
    IsPolyTime input (fun a => optionEncoding
      (pairEncoding (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
        (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding))
      (machine.rewindSnapshotFromCoins? (word a) handler (coins a) (snapshot a) (state a)
        choose restart)) := by
  let run (a : α) (tape : Word) (pair : Snapshot k Bool State (Fin ports) × S) :=
    (machine.runSnapshotFromCoins (m := StateT S Option) (word a) handler tape pair.1).run pair.2
  let first (a : α) := run a (coins a) (snapshot a, state a)
  let index (a : α) := choose ((first a).getD (snapshot a, state a))
  let saved (a : α) := run a ((coins a).take (index a)) (snapshot a, state a)
  let second (a : α) := run a ((coins a).drop (index a))
    ((saved a).getD (snapshot a, state a) |>.1,
      restart ((saved a).getD (snapshot a, state a)).2)
  have hfirst : IsPolyTime input (fun a => optionEncoding
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding) (first a)) :=
    hrun.comp_encoded (hw.pair (hc.pair (hs.pair hst)))
  have hindex := hchoose.comp_encoded (hfirst.option_getD (hs.pair hst))
  have hsaved : IsPolyTime input (fun a => optionEncoding
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding) (saved a)) :=
    hrun.comp_encoded (hw.pair ((hc.take hindex).pair (hs.pair hst)))
  have hrestored := hsaved.option_getD (hs.pair hst)
  have hsecond : IsPolyTime input (fun a => optionEncoding
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding) (second a)) :=
    hrun.comp_encoded (hw.pair ((hc.drop hindex).pair
      (hrestored.fst.pair (hrestart.comp_encoded hrestored.snd))))
  convert hsaved.option_isSome.cond (hfirst.option_pair hsecond)
    (isPolyTime_const input []) using 1
  funext a
  dsimp +instances only [rewindSnapshotFromCoins?, first, saved, index, second, run]
  cases hfirst : (machine.runSnapshotFromCoins (m := StateT S Option) (word a) handler
      (coins a) (snapshot a)).run (state a) with
  | none =>
    simp [Option.map₂]
  | some first =>
    dsimp +instances only [Option.getD, Bind.bind, Option.bind]
    cases (machine.runSnapshotFromCoins (m := StateT S Option) (word a) handler
      ((coins a).take (choose first)) (snapshot a)).run (state a) with
    | none => rfl
    | some saved =>
      dsimp +instances only [Option.getD]
      cases (machine.runSnapshotFromCoins (m := StateT S Option) (word a) handler
        ((coins a).drop (choose first)) saved.1).run (restart saved.2) <;> rfl

end Turing.MultiTapeTM
