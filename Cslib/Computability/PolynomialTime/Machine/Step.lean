/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot
public import Mathlib.Data.Fintype.Pi

/-!
# Certified simulation of a communicating machine transition

The source's finite transition table is fixed before the input. A selected query calls a certified
deterministic handler on the request and its current private state. Reading the source's tapes,
dispatching the transition, copying the successor snapshot, and updating shared state are charged
through the deterministic machine compiler.
-/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {α State S : Type} {k ports : ℕ} [Finite State]
  {input : α → Word} {control : State ↪ Word} {stateEncoding : S ↪ Word}

/-- A finite transition table with certified stateful handlers has an actual polynomial-time
implementation on encoded snapshots. This is a certificate for one simulated transition;
bounded execution additionally needs an invariant controlling intermediate representation sizes. -/
theorem isPolyTime_stepSnapshot
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Word × S)
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => pairEncoding wordEncoding stateEncoding (handler port pair.1 pair.2)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word : α → Word}
    {state : α → S} {bit : α → Bool}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word)
    (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    (hb : IsPolyTime input (fun a => boolEncoding (bit a))) :
    IsPolyTime input (fun a => pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
      (Id.run ((machine.stepSnapshot (m := StateT S Id) (word a)
        (fun port request st => pure (handler port request st)) (bit a) (snapshot a)).run
          (state a)))) := by
  let Key := Option State × Option Bool × (Fin k → Option Bool) ×
    (Fin ports → Option Bool) × Bool
  let execute (key : Key) (a : α) : Snapshot k Bool State (Fin ports) × S :=
    match key.1 with
    | none => (snapshot a, state a)
    | some q =>
      match machine.tr q key.2.1 key.2.2.1 key.2.2.2.1 key.2.2.2.2 with
      | .step action symbol move => ((snapshot a).step (word a) action symbol move, state a)
      | .query port next =>
        let out := handler port ((snapshot a).channels port).queryBuffer (state a)
        ((snapshot a).receive port next out.1, out.2)
  have hkey := hs.machineSnapshot_state.pair ((hs.machineSnapshot_inputSymbol hw).pair
    (hs.machineSnapshot_workSymbols.pair (hs.machineSnapshot_answerSymbols.pair hb)))
  have hbody := hkey.finite_cases
    (branch := fun key a => pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
      (execute key a)) (by
        rintro ⟨q, cell, work, answers, bit⟩
        cases q with
        | none => exact hs.pair hst
        | some q =>
          cases ha : machine.tr q cell work answers bit with
          | step action symbol move =>
            simpa only [execute, ha] using (hs.machineSnapshot_step hw action symbol move).pair hst
          | query port next =>
            have hcall := (hhandler port).comp_pair (left := wordEncoding) (right := stateEncoding)
              (f := fun request st =>
                pairEncoding wordEncoding stateEncoding (handler port request st))
              (hs.machineSnapshot_channels.tuple_apply port).channel_query hst
            simpa only [execute, ha, wordEncoding, Function.Embedding.refl_apply] using
              (hs.machineSnapshot_receive
                (isPolyTime_const input (finiteEncoding (Fin ports) port))
                (isPolyTime_const input (control next)) hcall.fst).pair hcall.snd)
  convert hbody using 1
  funext a
  simp only [stepSnapshot, execute]
  cases (snapshot a).state with
  | none => rfl
  | some q =>
    dsimp only
    cases machine.tr q ((snapshot a).inputSymbol (word a)) (snapshot a).workSymbols
        (snapshot a).answerSymbols (bit a) <;> rfl

end Turing.MultiTapeTM
