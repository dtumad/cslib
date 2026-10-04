/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot

/-!
# Rewinding a machine with a fixed private tape

The first result chooses a transition at which to rewind. Replaying the prefix restores both
the finite machine snapshot and the handler state. The second suffix reads the same private
coins as the first suffix. `restart` changes only the handler state, for example by replacing
its remaining oracle-answer tape while retaining the cache at the fork point.

Handlers are deterministic here: their random tapes belong to their explicit state. This makes
replaying the prefix and restoring its saved state exactly interchangeable. In particular,
replay does not repeat effects on an external mutable oracle.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {State Oracle S : Type} [DecidableEq Oracle]

/-- Run once, replay the selected prefix, and run a second suffix with the original private
coins. Both complete joint results are retained. An index past the end selects the final state.
The caller can represent an unsuccessful selection separately in its final observation. -/
def rewindSnapshotFromCoins (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → S → List Bool × S) (coins : List Bool)
    (snapshot : Snapshot k Bool State Oracle) (state : S)
    (choose : Snapshot k Bool State Oracle × S → ℕ) (restart : S → S) :
    (Snapshot k Bool State Oracle × S) × (Snapshot k Bool State Oracle × S) :=
  let run (tape : List Bool) (start : Snapshot k Bool State Oracle × S) :=
    Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
      (fun port request st => pure (handler port request st)) tape start.1).run start.2)
  let first := run coins (snapshot, state)
  let index := choose first
  let saved := run (coins.take index) (snapshot, state)
  (first, run (coins.drop index) (saved.1, restart saved.2))

/-- Replaying a prefix restores exactly the joint state saved after that prefix. The private
tape cursor is restored by retaining the suffix `coins.drop index`. -/
theorem runSnapshotFromCoins_take_drop (machine : MultiTapePTM k Bool State Oracle)
    (input : List Bool) (handler : Oracle → List Bool → S → List Bool × S)
    (coins : List Bool) (snapshot : Snapshot k Bool State Oracle) (state : S) (index : ℕ) :
    Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
      (fun port request st => pure (handler port request st)) coins snapshot).run state) =
      let saved := Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
        (fun port request st => pure (handler port request st)) (coins.take index) snapshot).run
          state)
      Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
        (fun port request st => pure (handler port request st)) (coins.drop index) saved.1).run
          saved.2) := by
  conv_lhs => rw [← List.take_append_drop index coins]
  rw [runSnapshotFromCoins_append]
  rfl

/-- With unchanged handler state, rewinding reproduces the entire result, including caches,
pending requests, timeout, and output. The selected position may depend on the first run. -/
theorem rewindSnapshotFromCoins_id (machine : MultiTapePTM k Bool State Oracle)
    (input : List Bool) (handler : Oracle → List Bool → S → List Bool × S)
    (coins : List Bool) (snapshot : Snapshot k Bool State Oracle) (state : S)
    (choose : Snapshot k Bool State Oracle × S → ℕ) :
    machine.rewindSnapshotFromCoins input handler coins snapshot state choose id =
      let first := Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
        (fun port request st => pure (handler port request st)) coins snapshot).run state)
      (first, first) := by
  dsimp only [rewindSnapshotFromCoins, id_eq]
  congr 1
  exact (runSnapshotFromCoins_take_drop machine input handler coins snapshot state _).symm

end Turing.MultiTapePTM
