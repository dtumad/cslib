/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Copying an input with one appended symbol

This routine sequences the shared input-copy machine with one output instruction. The complete
cost is `input.length + 2`, including the final symbol. No work tapes are needed.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*}

namespace CopyAppend

/-- Emit one symbol and halt, preserving the input head. -/
def finish (symbol : Symbol) : MultiTapeTM 0 Symbol Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := 0, workTapes := Fin.elim0, output := some symbol, state := none }

end CopyAppend

/-- Copy the input and then append a fixed symbol. -/
def copyAppend (symbol : Symbol) : MultiTapeTM 0 Symbol (Unit ⊕ Unit) :=
  copy.seq (CopyAppend.finish symbol)

/-- The complete execution reuses the copy and sequencing contracts. -/
theorem runFrom_copyAppend (symbol : Symbol) (input : List Symbol) :
    (copyAppend symbol).runFrom ((copyAppend symbol).initCfg input) (input.length + 2) =
      Sequential.rightCfg ((Copy.cfg input none input.length).withOutput (input ++ [symbol])) := by
  have hfinish : (CopyAppend.finish symbol).runFrom
      ((Copy.cfg input none input.length).withState (some ())) 1 =
      (Copy.cfg input none input.length).withOutput (input ++ [symbol]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [runFrom_one, step, CopyAppend.finish, Copy.cfg, Cfg.withState, Cfg.withOutput,
        Action.apply]
  have h := runFrom_seq (Copy.runFrom_full input) rfl hfinish rfl
  simpa [copyAppend, seq, Sequential.leftCfg, initCfg, Cfg.init, Cfg.mapState,
    Nat.add_assoc] using h

end Turing.MultiTapeTM
