/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Replay
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareReplay
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Deterministic replay from an encoded input pair

`replayInput machine` starts with blank work tapes, decodes the coin word and ordinary input,
and runs the replay controller through the shared deterministic input-redirection compiler.
Preparation includes writing and rewinding both words and installing the input boundary flag.

For `c` coins and an input of length `n`, the complete machine halts within `6 * c + 3 * n + 12`
transitions and produces exactly the shared machine's fixed-coin output. This bound is linear
in the encoded input length and holds even when the source machine never halts.
-/

@[expose] public section

namespace Turing.OracleTM
open Cslib MultiTapeTM
variable {k : ℕ} {State : Type}

/-- Decode the stored coins and input, then replay with local empty-answer queries. -/
def replayInput (machine : OracleTM k State) :
    MultiTapeTM (k + 3) Bool (PrepareReplay.ReadyControl ⊕ Option State) :=
  (PrepareReplay.prepare k).seq machine.replay.inputFromTape

/-- The prepared tapes are exactly the shared input adapter's initial layout. -/
theorem prepared_eq_inCfg (machine : OracleTM k State) (coins input : List Bool) :
    PrepareReplay.prepared k coins input (some (some machine.initial)) =
      inCfg true (Replay.config (machine.initialConfig input) (tapeOfList coins) 0)
        (PrepareReplay.encode coins input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change _ = (inCfg true _ _).workTapes (i.castSucc.castAdd 2)
      simp [PrepareReplay.prepared, inCfg_workTapes_castAdd, Replay.config, initialConfig,
        Cfg.init]
    | right i =>
      fin_cases i
      · change _ = (inCfg true _ _).workTapes ((Fin.last k).castAdd 2)
        simp [PrepareReplay.prepared, inCfg_workTapes_castAdd, Replay.config]
      · change _ = (inCfg true _ _).workTapes (Fin.natAdd (k + 1) 0)
        simp [PrepareReplay.prepared]
      · change _ = (inCfg true _ _).workTapes (Fin.natAdd (k + 1) 1)
        simp [PrepareReplay.prepared, PrepareInput.flag]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change _ = (inCfg true _ _).workTapePos (i.castSucc.castAdd 2)
      simp [PrepareReplay.prepared, Replay.config, initialConfig, Cfg.init]
    | right i =>
      fin_cases i
      · change _ = (inCfg true _ _).workTapePos ((Fin.last k).castAdd 2)
        simp [PrepareReplay.prepared, Replay.config]
      · change _ = (inCfg true _ _).workTapePos (Fin.natAdd (k + 1) 0)
        simp [PrepareReplay.prepared, Replay.config, initialConfig, Cfg.init]
      · change _ = (inCfg true _ _).workTapePos (Fin.natAdd (k + 1) 1)
        simp [PrepareReplay.prepared, Replay.config, initialConfig, Cfg.init]

/-- The complete replay machine halts with the fixed-coin output in linear time.
The bound includes all tape preparation and applies to every supplied coin word. -/
theorem runFrom_replayInput (machine : OracleTM k State) (coins input : List Bool) :
    let final := machine.replayInput.runFrom
      (machine.replayInput.initCfg (PrepareReplay.encode coins input))
      (6 * coins.length + 3 * input.length + 12)
    final.state = none ∧
      final.output = MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) coins input := by
  let source := Replay.config (machine.initialConfig input) (tapeOfList coins) 0
  let final := inCfg true
    (Replay.stopped (Replay.result machine coins (machine.initialConfig input))
      (tapeOfList coins) coins.length) (PrepareReplay.encode coins input)
  have hsimulate : machine.replay.inputFromTape.runFrom
      ((PrepareReplay.prepared k coins input (none : Option PrepareReplay.ReadyControl)).withState
        (some machine.replay.inputFromTape.q₀)) (coins.length + 1) = final := by
    have hstart : (PrepareReplay.prepared k coins input
        (none : Option PrepareReplay.ReadyControl)).withState
        (some machine.replay.inputFromTape.q₀) =
      inCfg true source (PrepareReplay.encode coins input) := by
      simpa only [PrepareReplay.prepared, Cfg.withState, inputFromTape, replay, source] using
        prepared_eq_inCfg machine coins input
    rw [hstart, runFrom_inCfg, runFrom_replay]
  have hrun := runFrom_seq (PrepareReplay.runFrom_prepare k coins input) rfl
    hsimulate (show final.state = none from rfl)
  have htime : 5 * coins.length + 3 * input.length + 11 + (coins.length + 1) =
      6 * coins.length + 3 * input.length + 12 := by omega
  rw [htime] at hrun
  change machine.replayInput.runFrom
      (machine.replayInput.initCfg (PrepareReplay.encode coins input)) _ = _ at hrun
  dsimp only
  rw [hrun]
  exact ⟨rfl, rfl⟩

end Turing.OracleTM
