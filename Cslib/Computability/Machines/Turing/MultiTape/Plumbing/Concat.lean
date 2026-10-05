/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputPrefix
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Data.Fin.Embedding

/-!
# Concatenating the outputs of two machines

`concat tm₀ tm₁` runs `tm₀`, rewinds the input head, and runs `tm₁` on a disjoint block of
initially blank work tapes. Both write to the same append-only output tape, producing the
concatenation of their outputs without storing an intermediate result.

The construction and fresh-tape handoff are adapted from Christian Reitwiessner's
`concat-combinator` branch to the current `extendTapes`, `rewindInput` and `runFrom_seq` APIs.
The runtime contract accepts padded halting bounds: the combined bound is the sum of the two
bounds plus `input.length + 2` for the rewind. This module proves time and output correctness;
it does not yet port the branch's additional space bound.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type*}

/-- The block of work tapes used by the first machine. -/
def concatTapeLeft (k₀ k₁ : ℕ) : Fin k₀ ↪ Fin (k₀ + k₁) := Fin.castAddEmb k₁

/-- The block of work tapes used by the second machine. -/
def concatTapeRight (k₀ k₁ : ℕ) : Fin k₁ ↪ Fin (k₀ + k₁) := Fin.natAddEmb k₀

/-- The first machine never touches the second machine's work tapes. -/
lemma concatTapeRight_notMem_range_left (j : Fin k₁) :
    concatTapeRight k₀ k₁ j ∉ Set.range (concatTapeLeft k₀ k₁) := by
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp only [concatTapeLeft, concatTapeRight, Fin.castAddEmb_apply, Fin.natAddEmb_apply,
    Fin.val_castAdd, Fin.val_natAdd] at hval
  have := i.isLt
  omega

/-- Run the first machine on its work tapes and restore the input head to its initial position. -/
def concatPrefix (k₁ : ℕ) (tm₀ : MultiTapeTM k₀ Symbol State₀) :
    MultiTapeTM (k₀ + k₁) Symbol (State₀ ⊕ RewindState) :=
  (tm₀.extendTapes (concatTapeLeft k₀ k₁)).seq
    ((rewindInput Symbol).extendTapes (noTapes (k₀ + k₁)))

/-- Run two machines on the same input and concatenate their outputs. -/
def concat (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁) :
    MultiTapeTM (k₀ + k₁) Symbol ((State₀ ⊕ RewindState) ⊕ State₁) :=
  (concatPrefix k₁ tm₀).seq (tm₁.extendTapes (concatTapeRight k₀ k₁))

namespace Concat

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
  {input : List Symbol}

/-- The first machine's final tapes and output, with the input head restored. -/
def prefixCfg (t₀ : ℕ) : Cfg (k₀ + k₁) Symbol (State₀ ⊕ RewindState) input :=
  let cfg := embed (concatTapeLeft k₀ k₁) (tm₀.runFrom (tm₀.initCfg input) t₀)
    (fun _ _ => none) (fun _ => 0)
  Sequential.rightCfg (⟨none, 1, cfg.workTapes, cfg.workTapePos, cfg.output⟩ :
    Cfg (k₀ + k₁) Symbol RewindState input)

/-- Copying no data, the shared rewind restores the input head within the input-length bound. -/
theorem runFrom_prefix {t₀ : ℕ}
    (hhalt : (tm₀.runFrom (tm₀.initCfg input) t₀).state = none) :
    (concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input)
        (t₀ + (input.length + 2)) = prefixCfg tm₀ (k₁ := k₁) t₀ := by
  let mid := embed (concatTapeLeft k₀ k₁) (tm₀.runFrom (tm₀.initCfg input) t₀)
    (fun _ _ => none) (fun _ => 0)
  let rewound : Cfg (k₀ + k₁) Symbol RewindState input :=
    ⟨none, 1, mid.workTapes, mid.workTapePos, mid.output⟩
  have hrewind : ((rewindInput Symbol).extendTapes (noTapes (k₀ + k₁))).runFrom
      (mid.withState (some ((rewindInput Symbol).extendTapes (noTapes (k₀ + k₁))).q₀))
      (mid.inputPos.val - 1 + 2) = rewound :=
    runFrom_rewindInput_noTapes mid.inputPos mid.workTapes mid.workTapePos mid.output
  have hbound : mid.inputPos.val - 1 + 2 ≤ input.length + 2 := by
    have := mid.inputPos.isLt
    omega
  have hrewind' : ((rewindInput Symbol).extendTapes (noTapes (k₀ + k₁))).runFrom
      (mid.withState (some ((rewindInput Symbol).extendTapes (noTapes (k₀ + k₁))).q₀))
        (input.length + 2) = rewound := by
    rw [runFrom_eq_of_halt _ _ hbound (by rw [hrewind]), hrewind]
  have h := runFrom_seq (runFrom_extendTapes tm₀ (concatTapeLeft k₀ k₁) input t₀)
    hhalt hrewind' rfl
  simpa only [concatPrefix, initCfg_seq, prefixCfg, rewound, mid] using h

/-- The continuation receives its own blank tapes, the original input and all accumulated output. -/
theorem handoff_eq (t₀ : ℕ) (out : List Symbol)
    (hout : (tm₀.runFrom (tm₀.initCfg input) t₀).output = out) :
    (prefixCfg tm₀ (k₁ := k₁) t₀).withState
        (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀) =
      (embed (concatTapeRight k₀ k₁) (tm₁.initCfg input)
        (prefixCfg tm₀ (k₁ := k₁) (input := input) t₀).workTapes
        (prefixCfg tm₀ (k₁ := k₁) (input := input) t₀).workTapePos).prependOutput out := by
  have houtH : ((prefixCfg tm₀ (k₁ := k₁) t₀).withState
      (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)).output = out := hout
  rw [← houtH]
  refine eq_embed_initCfg (concatTapeRight k₀ k₁) tm₁ _ rfl rfl ?_ ?_
  · intro j
    simp [prefixCfg, Sequential.rightCfg, Cfg.mapState, Cfg.withState, embed,
      partialInv_eq_none _ (concatTapeRight_notMem_range_left j)]
  · intro j
    simp [prefixCfg, Sequential.rightCfg, Cfg.mapState, Cfg.withState, embed,
      partialInv_eq_none _ (concatTapeRight_notMem_range_left j)]

end Concat

/-- The two outputs are concatenated, with only an input rewind added to their time bounds. -/
theorem runFrom_concat (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input out₀ out₁ : List Symbol} {t₀ t₁ : ℕ}
    (hhalt₀ : (tm₀.runFrom (tm₀.initCfg input) t₀).state = none)
    (hout₀ : (tm₀.runFrom (tm₀.initCfg input) t₀).output = out₀)
    (hhalt₁ : (tm₁.runFrom (tm₁.initCfg input) t₁).state = none)
    (hout₁ : (tm₁.runFrom (tm₁.initCfg input) t₁).output = out₁) :
    let final := (tm₀.concat tm₁).runFrom ((tm₀.concat tm₁).initCfg input)
      (t₀ + t₁ + input.length + 2)
    final.state = none ∧ final.output = out₀ ++ out₁ := by
  let mid := Concat.prefixCfg tm₀ (k₁ := k₁) (input := input) t₀
  let final := (embed (concatTapeRight k₀ k₁) (tm₁.runFrom (tm₁.initCfg input) t₁)
    mid.workTapes mid.workTapePos).prependOutput out₀
  have hsecond : (tm₁.extendTapes (concatTapeRight k₀ k₁)).runFrom
      (mid.withState (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)) t₁ = final := by
    rw [Concat.handoff_eq tm₀ tm₁ t₀ out₀ hout₀, runFrom_prependOutput, runFrom_embed]
  have hfinal : final.state = none := hhalt₁
  have hrun := runFrom_seq (Concat.runFrom_prefix tm₀ hhalt₀) rfl hsecond hfinal
  have htime : t₀ + (input.length + 2) + t₁ = t₀ + t₁ + input.length + 2 := by omega
  rw [htime, ← initCfg_seq] at hrun
  change ((tm₀.concat tm₁).runFrom _ _).state = none ∧
    ((tm₀.concat tm₁).runFrom _ _).output = _
  simp only [concat]
  rw [hrun]
  refine ⟨?_, congrArg (out₀ ++ ·) hout₁⟩
  change final.state.map Sum.inr = none
  rw [hfinal]
  rfl

end Turing.MultiTapeTM
