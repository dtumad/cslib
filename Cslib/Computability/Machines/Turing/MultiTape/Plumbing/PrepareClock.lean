/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PolynomialClock
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindLast

/-!
# Preparing a polynomial clock on blank tapes

The first `k` work tapes are reserved for the source machine. The next `degree` tapes hold the
scratch counters, and the final tape receives the unary budget. Preparation restores every head
and leaves the input, source tapes, and output untouched.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PolynomialClock

/-- Finite control for constructing and rewinding a budget. -/
abbrev PrepareControl (coefficient degree : ℕ) :=
  (Bool ⊕ Control coefficient degree) ⊕ RewindWorkState

/-- Construct the budget on the last tape, then rewind it. -/
def prepare (k coefficient degree : ℕ) :
    MultiTapeTM (k + degree + 1) Bool (PrepareControl coefficient degree) :=
  (((polynomialClock coefficient degree).extendTapes (Fin.natAddEmb k)).outputToTape).seq
    (rewindLast (k + degree))

/-- Tape contents after preparation: blank source tapes, scratch counters, and the budget. -/
def preparedWords (k coefficient degree length : ℕ) : Fin (k + degree + 1) → List Bool :=
  Fin.lastCases (List.replicate (coefficient * (length + 1) ^ degree) true)
    (Fin.addCases (fun _ : Fin k => []) (fun _ => List.replicate (length + 1) true))

/-- Time charged for generation and for rewinding the budget. -/
def prepareTime (coefficient degree length : ℕ) : ℕ :=
  (6 ^ degree * (coefficient + 1) + 2) * (length + 1) ^ (degree + 1) +
    coefficient * (length + 1) ^ degree + 2

private theorem partialInv_natAdd_castAdd (k degree : ℕ) (i : Fin k) :
    partialInv (Fin.natAddEmb k) (Fin.castAdd degree i) = none := by
  apply partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at this
  have := i.isLt
  omega

private theorem partialInv_natAdd_natAdd (k degree : ℕ) (i : Fin degree) :
    partialInv (Fin.natAddEmb k) (Fin.natAdd k i) = some i :=
  partialInv_embed (Fin.natAddEmb k) i

private theorem embed_words (k degree : ℕ) {State : Type} (input : List Bool)
    (state : Option State) (word output : List Bool) :
    embed (Fin.natAddEmb k) (wordsCfg input state (fun _ : Fin degree => word) output)
      (fun _ _ => none) (fun _ => 0) =
      wordsCfg input state (Fin.addCases (fun _ : Fin k => []) (fun _ => word)) output := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [embed, wordsCfg, partialInv_natAdd_castAdd]
  | right i => simp [embed, wordsCfg, partialInv_natAdd_natAdd]

/-- Starting with ordinary blank work tapes, preparation halts with the clock ready to consume. -/
theorem runFrom_prepare (k coefficient degree : ℕ) (input : List Bool) :
    (prepare k coefficient degree).runFrom
      (Cfg.init (prepare k coefficient degree).q₀ input)
      (prepareTime coefficient degree input.length) =
      wordsCfg input none (preparedWords k coefficient degree input.length) [] := by
  let generator := (polynomialClock coefficient degree).extendTapes (Fin.natAddEmb k)
  let initial : Cfg (k + degree) Bool (Bool ⊕ Control coefficient degree) input :=
    Cfg.init generator.q₀ input
  let generated : Cfg (k + degree) Bool (Bool ⊕ Control coefficient degree) input :=
    wordsCfg input none
      (Fin.addCases (fun _ : Fin k => []) (fun _ => List.replicate (input.length + 1) true))
      (List.replicate (coefficient * (input.length + 1) ^ degree) true)
  let time := (6 ^ degree * (coefficient + 1) + 2) * (input.length + 1) ^ (degree + 1)
  have hinit : initial = embed (Fin.natAddEmb k)
      (wordsCfg input (some (polynomialClock coefficient degree).q₀) (fun _ => []) [])
      (fun _ _ => none) (fun _ => 0) := by
    rw [embed_words]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    induction i using Fin.addCases <;> simp [initial, Cfg.init, wordsCfg]
  have hgenerate : generator.runFrom initial time = generated := by
    rw [hinit, runFrom_embed, runFrom_polynomialClock_bound, List.nil_append, embed_words]
  have hwrite : generator.outputToTape.runFrom (outCfg initial) time = outCfg generated := by
    rw [runFrom_outCfg, hgenerate]
  have hrewind := runFrom_rewindLast (outCfg generated) generated.output
    (outCfg_workTapes_last generated) (outCfg_workTapePos_last generated)
  change (rewindLast (k + degree)).runFrom
    ((outCfg generated).withState (some (rewindLast (k + degree)).q₀))
    (generated.output.length + 2) = _ at hrewind
  have hseq := runFrom_seq hwrite rfl hrewind rfl
  have hstart : Sequential.leftCfg (rewindLast (k + degree)) (outCfg initial) =
      Cfg.init (prepare k coefficient degree).q₀ input := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
      simp [outCfg, initial, Cfg.init, Sequential.leftCfg, Cfg.mapState]
  rw [hstart] at hseq
  have hfinal : Sequential.rightCfg (State₀ := Bool ⊕ Control coefficient degree)
      (RewindLast.config (outCfg generated) none 0) =
      wordsCfg input none (preparedWords k coefficient degree input.length) [] := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
      simp [Sequential.rightCfg, Cfg.mapState, RewindLast.config, Cfg.withState, outCfg,
        generated, wordsCfg, preparedWords]
  rw [hfinal] at hseq
  simpa only [prepare, prepareTime, time, generated, wordsCfg, List.length_replicate,
    Nat.add_assoc] using hseq

end Turing.MultiTapeTM.PolynomialClock
