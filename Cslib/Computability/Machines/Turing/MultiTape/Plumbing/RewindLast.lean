/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork

/-!
# Rewinding a completed output word

`rewindLast k` specializes the shared `rewindWork` machine to the final binary work tape. It takes
`word.length + 2` steps, works for the empty word, and preserves every tape, the input head, all
other work heads, and the output. The implementation and its execution proof come from the general
work-tape routine.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Rewind the last work tape without writing to it. -/
abbrev rewindLast (k : ℕ) : MultiTapeTM (k + 1) Bool RewindWorkState :=
  rewindWork Bool (Fin.last k)

/-- Only the control state and the last head's position change during rewinding. -/
def RewindLast.config {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg (k + 1) Bool State input) (state : Option RewindWorkState) (position : ℤ) :
    Cfg (k + 1) Bool RewindWorkState input :=
  { cfg.withState state with workTapePos := Function.update cfg.workTapePos (Fin.last k) position }

/-- Rewinding preserves all data and every other head, and halts with the last head at zero. -/
theorem runFrom_rewindLast {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg (k + 1) Bool State input) (word : List Bool)
    (hword : cfg.workTapes (Fin.last k) = tapeOfList word)
    (hposition : cfg.workTapePos (Fin.last k) = word.length) :
    (rewindLast k).runFrom (cfg.withState (some .start)) (word.length + 2) =
      RewindLast.config cfg none 0 := by
  simpa [rewindLast, rewindWork, RewindLast.config, Cfg.withState, ← hposition] using
    runFrom_rewindWork_none cfg.inputPos cfg.workTapes cfg.workTapePos cfg.output
      hword (p := word.length) le_rfl

end Turing.MultiTapeTM
