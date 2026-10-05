/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Step
public import Cslib.Computability.PolynomialTime.Machine.Bounds
import Mathlib.Data.Fintype.Order

/-!
# Uniform deterministic replay with shared handler state

One fixed simulator reads an encoded random tape, source snapshot, input, and handler state.
The stateful handlers have actual deterministic machine certificates. A polynomial bound on
reachable encoded configurations closes the existing fold compiler, charging for repeated copying
and handler calls. The bound is about data size, not an assumed simulation runtime.
-/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {α State S : Type} {k ports : ℕ} [Finite State]
  {input : α → Word} {control : State ↪ Word} {stateEncoding : S ↪ Word}

/-- Replay is uniformly polynomial time when reachable snapshots and shared handler state have
polynomial encoded size. The supplied coin word determines the number of simulated transitions. -/
theorem isPolyTime_runSnapshotFromCoins
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Word × S)
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => pairEncoding wordEncoding stateEncoding (handler port pair.1 pair.2)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word} {state : α → S}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ a consumed, consumed <+: coins a →
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
        (Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
          (fun port request st => pure (handler port request st)) consumed (snapshot a)).run
            (state a)))).length ≤ size (input a).length) :
    IsPolyTime input (fun a => pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
      (Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
        (fun port request st => pure (handler port request st)) (coins a) (snapshot a)).run
          (state a)))) := by
  let outcome := pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
  let frame := pairEncoding wordEncoding outcome
  let runStep (word : Word) (pair : Snapshot k Bool State (Fin ports) × S) (bit : Bool) :=
    Id.run ((machine.stepSnapshot (m := StateT S Id) word
      (fun port request st => pure (handler port request st)) bit pair.1).run pair.2)
  let advance (pair : Word × Snapshot k Bool State (Fin ports) × S) (bit : Bool) :=
    (pair.1, runStep pair.1 pair.2 bit)
  have hframe := isPolyTime_fst frame boolEncoding
  have hnext := isPolyTime_stepSnapshot machine handler hhandler
    hframe.snd.fst hframe.fst hframe.snd.snd (isPolyTime_snd frame boolEncoding)
  have hstep : IsPolyTime (pairEncoding frame boolEncoding)
      (fun pair => frame (advance pair.1 pair.2)) := hframe.fst.pair hnext
  have htrace (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports)) (state : S) :
      coins.foldl advance (word, snapshot, state) =
        (word, Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) word
          (fun port request st => pure (handler port request st)) coins snapshot).run state)) := by
    rw [runSnapshotFromCoins_stateT]
    induction coins generalizing snapshot state with
    | nil => rfl
    | cons bit coins ih =>
      change coins.foldl advance (word, runStep word (snapshot, state) bit) = _
      exact ih (runStep word (snapshot, state) bit).1 (runStep word (snapshot, state) bit).2
  obtain ⟨c, d, hword⟩ := hw.length_le
  have hfold := hc.foldl_encoded (stateEncoding := frame) (step := advance)
    (hw.pair (hs.pair hst)) hstep
    (size := fun n => 2 * (c * (n + 1) ^ d) + size n + 1) (by fun_prop) (by
      intro a index _
      rw [htrace]
      simp only [frame, length_pairEncoding, wordEncoding, Function.Embedding.refl_apply]
      have := hsize a ((coins a).take index) (List.take_prefix _ _)
      have := hword a
      dsimp only [outcome]
      omega)
  simpa only [htrace] using hfold.snd

/-- Certified handlers with polynomial replies and per-call state growth give a uniform replay
machine. Only data-size bounds remain as hypotheses; simulation and copying costs are derived. -/
theorem isPolyTime_runSnapshotFromCoins_of_growth
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Word × S)
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => pairEncoding wordEncoding stateEncoding (handler port pair.1 pair.2)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word} {state : α → S}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    (invariant : α → S → Prop) (hinit : ∀ a, invariant a (state a))
    {reply growth : ℕ → ℕ} (hreply : PolynomiallyBounded reply)
    (hgrowth : PolynomiallyBounded growth)
    (hcall : ∀ a port request st,
      request.length ≤ (machineSnapshotEncoding k ports control (snapshot a)).length +
        (coins a).length → invariant a st →
      invariant a (handler port request st).2 ∧
        (handler port request st).1.length ≤ reply (input a).length ∧
        (stateEncoding (handler port request st).2).length ≤
          (stateEncoding st).length + growth (input a).length) :
    IsPolyTime input (fun a => pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
      (Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
        (fun port request st => pure (handler port request st)) (coins a) (snapshot a)).run
          (state a)))) := by
  obtain ⟨bound, hcontrol⟩ := Finite.exists_le (fun state => (control state).length)
  obtain ⟨ci, di, hi⟩ := (hs.pair hst).length_le
  obtain ⟨cc, dc, hcoins⟩ := hc.length_le
  let delta (n : ℕ) :=
    2 * (2 * bound + 56 * k + 24 * ports + 6 + 20 * ports * (reply n + 1)) + growth n
  apply isPolyTime_runSnapshotFromCoins machine handler hhandler hs hw hc hst
    (size := fun n => ci * (n + 1) ^ di + cc * (n + 1) ^ dc * delta n) (by
      dsimp only [delta]
      fun_prop)
  intro a consumed hconsumed
  have hbound := runSnapshotFromCoins_bound machine (word a) consumed handler (snapshot a) (state a)
    hcontrol (length_query_le_machineSnapshotEncoding (control := control) (snapshot a))
    (invariant a) (hinit a) (fun port request st hq hinv =>
      hcall a port request st (hq.trans (Nat.add_le_add_left hconsumed.length_le _)) hinv)
  exact hbound.2.2.trans (Nat.add_le_add (hi a)
    (Nat.mul_le_mul_right (delta (input a).length) (hconsumed.length_le.trans (hcoins a))))

end Turing.MultiTapeTM
