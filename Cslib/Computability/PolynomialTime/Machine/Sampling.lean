/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Replay
public import Cslib.Computability.PolynomialTime.Sampling

/-!
# Randomized execution through certified deterministic handlers

A finite private tape is sampled and passed to the certified snapshot interpreter. Handler
randomness may be stored in its initial state, independently of the source machine's tape.
The interpreter charges for both handler calls and copying all reachable state.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeTM MultiTapeMachine PFunctor

variable {Oracle α State S : Type} [Finite Oracle] {k ports : ℕ} [Finite State]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  {input : α ↪ Word} {control : State ↪ Word} {stateEncoding : S ↪ Word}

/-- Sampling the private tape and executing the actual interpreter has one uniform polynomial
machine certificate. The remaining bound concerns reachable data sizes, not execution time. -/
theorem isPPT_runSnapshotFromSampledCoins
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Word × S)
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => pairEncoding wordEncoding stateEncoding (handler port pair.1 pair.2)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word : α → Word}
    {state : α → S} {count : α → ℕ}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ a coins consumed, consumed <+: coins →
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
        (Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
          (fun port request st => pure (handler port request st)) consumed (snapshot a)).run
            (state a)))).length ≤ size (pairEncoding input wordEncoding (a, coins)).length) :
    IsPPT (Oracle := Oracle) input
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding) (fun a =>
        (fun coins => Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) (word a)
          (fun port request st => pure (handler port request st)) coins (snapshot a)).run
            (state a))) <$> (List.replicate (count a) ()).mapM (fun _ => coin)) := by
  have henv := isPolyTime_fst input wordEncoding
  have hcoins := isPolyTime_snd input wordEncoding
  apply (isPPT_sampleBits_of_isPolyTime hcount).map_with
  exact isPolyTime_runSnapshotFromCoins machine handler hhandler
    (hs.comp_encoded henv) (hw.comp_encoded henv) hcoins (hst.comp_encoded henv)
    hpoly (fun pair => hsize pair.1 pair.2)

end Turing.MultiTapePTM
