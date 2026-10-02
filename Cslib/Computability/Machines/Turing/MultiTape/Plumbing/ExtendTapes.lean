/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Inv
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Extending a machine with additional work tapes

`extendTapes tm e`, for an embedding `e : Fin k ↪ Fin k'`, runs `tm` inside a machine with more
work tapes. The tapes selected by `e` are used by `tm`: target tape `e j` plays the role of source
tape `j`. The remaining tapes are left unchanged.

The configuration map `embed e cfg extraTapes extraPos` places `cfg` on the selected tapes and
initialises the remaining tapes from `extraTapes` and `extraPos`.

The main lemmas show that one step and an entire run of the larger machine mirror the corresponding
step and run of `tm`.

## Main definitions

* `Turing.MultiTapeTM.partialInv`: the partial inverse of the tape embedding.
* `Turing.MultiTapeTM.extendTapes`: the machine with reindexed work tapes.
* `Turing.MultiTapeTM.embed`: the corresponding configuration map.

## Main results

* `Turing.MultiTapeTM.step_embed` and `Turing.MultiTapeTM.runFrom_embed`: the one-step and run-level
  mirroring lemmas.
* `Turing.MultiTapeTM.workTapePos_embed_of_not_range`: the extra tapes never move.
* `Turing.MultiTapeTM.spaceUsed_embed_le`: the resulting space bound.
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The computable analogue of `Function.partialInv` for an embedding `e`: `partialInv e l = some j`
when `e j = l` (such `j` is unique by injectivity), and `none` when `l` lies outside the range of
`e`. -/
@[expose] public def partialInv (e : Fin k ↪ Fin k') (l : Fin k') : Option (Fin k) :=
  if h : l ∈ Set.range e then some (e.invOfMemRange ⟨l, h⟩) else none

/-- `partialInv e` is a partial inverse of `e`. -/
public lemma partialInv_isPartialInv (e : Fin k ↪ Fin k') :
    Function.IsPartialInv e (partialInv e) := fun j l => by
  grind [partialInv, Function.Embedding.left_inv_of_invOfMemRange,
    Function.Embedding.right_inv_of_invOfMemRange]

/-- `tm` run on the tapes selected by the embedding `e`, leaving other tapes untouched: work tape
`e j` plays the role of `tm`'s tape `j`, and any tape outside `range e` is never written and never
moves. -/
@[expose] public def extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    MultiTapeTM k' Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work (e j)
    { inputTape := a.inputTape
      workTapes := fun l => match partialInv e l with
        | some j => a.workTapes j
        | none => (none, 0)
      output := a.output
      state := a.state }

/-- A configuration of `tm`, embedded: tape `j` goes to tape `e j`, the tapes outside `range e`
carry the given `extraTapes` contents and `extraPos` head positions. -/
@[expose] public def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input :=
  ⟨cfg.state, cfg.inputPos,
    fun l => match partialInv e l with
      | some j => cfg.workTapes j
      | none => extraTapes l,
    fun l => match partialInv e l with
      | some j => cfg.workTapePos j
      | none => extraPos l,
    cfg.output⟩

/-- The partial inverse recovers the source tape of an embedded tape. -/
@[simp]
public lemma partialInv_embed (e : Fin k ↪ Fin k') (j : Fin k) : partialInv e (e j) = some j :=
  (partialInv_isPartialInv e).eq j

/-- Outside the range of `e`, the partial inverse is undefined. -/
public lemma partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (hl : l ∉ Set.range e) :
    partialInv e l = none :=
  dite_eq_right hl

/-- If the partial inverse is `some j`, then `e j = l`. -/
public lemma partialInv_eq_some (e : Fin k ↪ Fin k') {l : Fin k'} {j : Fin k}
    (h : partialInv e l = some j) : e j = l :=
  (partialInv_isPartialInv e j l).mp h

@[simp]
public lemma embed_inputSymbol (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (embed e cfg extraTapes extraPos).inputSymbol = cfg.inputSymbol := rfl

@[simp]
public lemma embed_workTapes_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapes (e j) = cfg.workTapes j := by
  simp [embed]

@[simp]
public lemma embed_workTapePos_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapePos (e j) = cfg.workTapePos j := by
  simp [embed]

@[simp]
public lemma embed_workTapeSymbols_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapeSymbols (e j) = cfg.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- Reindexing is a step-semiconjugation: the reindexed machine acts on the embedded tapes exactly
as `tm` does, and never touches the extra tapes. -/
public lemma step_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) :
    (tm.extendTapes e).step (embed e cfg extraTapes extraPos)
      = embed e (tm.step cfg) extraTapes extraPos := by
  cases hq : cfg.state with
  | none => simp [embed, hq]
  | some q =>
    rw [step_apply_of_state (cfg := embed e cfg extraTapes extraPos) hq, step_apply_of_state hq]
    simp only [extendTapes, embed_inputSymbol, embed_workTapeSymbols_embed]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [Action.apply, embed] <;>
      cases partialInv e l <;> simp

/-- The reindexed run mirrors the original, with the extra tapes held fixed throughout. -/
public lemma runFrom_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n
      = embed e (tm.runFrom cfg n) extraTapes extraPos :=
  (Function.Semiconj.iterate_right (f := (embed e · extraTapes extraPos))
    (fun c => (step_embed tm e c extraTapes extraPos).symm) n cfg).symm

/-- A tape outside the embedding retains its supplied contents. -/
@[simp] public lemma workTapes_embed_of_notMem_range (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) {j : Fin k'} (hj : j ∉ Set.range e) :
    (embed e cfg extraTapes extraPos).workTapes j = extraTapes j := by
  simp [embed, partialInv_eq_none e hj]

/-- A tape outside the embedding retains its supplied head position. -/
@[simp] public lemma workTapePos_embed_of_notMem_range (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) {j : Fin k'} (hj : j ∉ Set.range e) :
    (embed e cfg extraTapes extraPos).workTapePos j = extraPos j := by
  simp [embed, partialInv_eq_none e hj]

/-- The extended machine starts with blank native and extra tapes. -/
public lemma initCfg_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) :
    (tm.extendTapes e).initCfg input =
      embed e (tm.initCfg input) (fun _ _ => none) (fun _ => 0) := by
  apply Cfg.ext <;> try rfl
  · funext j
    cases hi : partialInv e j <;> simp [embed, hi]
  · funext j
    cases hi : partialInv e j <;> simp [embed, hi]

/-- Starting with blank work tapes commutes with tape extension. -/
public lemma runFrom_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) (n : ℕ) :
    (tm.extendTapes e).runFrom ((tm.extendTapes e).initCfg input) n =
      embed e (tm.runFrom (tm.initCfg input) n) (fun _ _ => none) (fun _ => 0) := by
  rw [initCfg_extendTapes, runFrom_embed]

/-- A machine can start on a fresh block of tapes while retaining all other tapes and output.
Adapted from the `concat-combinator` branch's `ExtendTapes.eq_embed_initCfg` contract. -/
public lemma eq_embed_initCfg (e : Fin k ↪ Fin k') (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k' Symbol State input) (hstate : cfg.state = some tm.q₀) (hpos : cfg.inputPos = 1)
    (hblank : ∀ i, cfg.workTapes (e i) = fun _ => none)
    (hzero : ∀ i, cfg.workTapePos (e i) = 0) :
    cfg = (embed e (tm.initCfg input) cfg.workTapes cfg.workTapePos).prependOutput cfg.output := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simpa [embed] using hstate
  · simpa [embed] using hpos
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      simpa [Cfg.prependOutput, embed] using hblank i
    · simp [Cfg.prependOutput, embed, partialInv_eq_none e hj]
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      simpa [Cfg.prependOutput, embed] using hzero i
    · simp [Cfg.prependOutput, embed, partialInv_eq_none e hj]
  · simp [embed]

/-- Embedding selected word tapes and keeping the remaining words reconstructs the configuration. -/
public theorem embed_wordsCfg (e : Fin k ↪ Fin k') (state : Option State)
    (words : Fin k' → List Symbol) (output : List Symbol) :
    embed e (wordsCfg input state (words ∘ e) output)
      (fun i => tapeOfList (words i)) (fun _ => 0) =
      wordsCfg input state words output := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    cases h : partialInv e i with
  | none => simp [embed, wordsCfg, h]
  | some j =>
    have he := partialInv_eq_some e h
    simp [embed, wordsCfg, h, he]

/-- A word-level run lifts through a tape embedding when all unselected words are preserved. -/
public theorem runFrom_extendTapes_words (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (words words' : Fin k' → List Symbol) (output output' : List Symbol) (time : ℕ)
    (h : tm.runFrom (wordsCfg input (some tm.q₀) (words ∘ e) output) time =
      wordsCfg input none (words' ∘ e) output')
    (hframe : ∀ i, i ∉ Set.range e → words' i = words i) :
    (tm.extendTapes e).runFrom
      (wordsCfg input (some (tm.extendTapes e).q₀) words output) time =
      wordsCfg input none words' output' := by
  change (tm.extendTapes e).runFrom (wordsCfg input (some tm.q₀) words output) time = _
  rw [← embed_wordsCfg e (some tm.q₀) words output, runFrom_embed, h]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    cases hp : partialInv e i with
  | none =>
    have hi : i ∉ Set.range e := by
      rintro ⟨j, rfl⟩
      simp at hp
    simp [embed, wordsCfg, hp, hframe i hi]
  | some j =>
    have he := partialInv_eq_some e hp
    simp [embed, wordsCfg, hp, he]

section Space

/-- The head of a tape outside `range e` never leaves its starting position. -/
public lemma workTapePos_embed_of_not_range (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) {l : Fin k'} (hl : l ∉ Set.range e) :
    ((tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n).workTapePos l
      = extraPos l := by
  rw [runFrom_embed]
  simp only [embed, partialInv_eq_none e hl]

/-- **Space bound for a reindexed run.** The embedded tapes contribute the space used by `tm`, while
each of the remaining `k' - k` tapes never moves and contributes at most one cell. -/
public lemma spaceUsed_embed_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n
      ≤ tm.spaceUsed cfg n + (k' - k) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding e cfg _ 1
    (fun m _ j => by rw [runFrom_embed, embed_workTapePos_embed])
    fun l hl => spaceUsedByTape_le_one _ fun m _ => by
      rw [workTapePos_embed_of_not_range tm e cfg extraTapes extraPos m hl]
      simp only [embed, partialInv_eq_none e hl]

end Space

end Turing.MultiTapeTM
