/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
public import Mathlib.Tactic.FinCases
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput

/-!
# Preparing an input and random tape for deterministic replay

The pair encoding tags every bit of the coin word with `true`, then places a `false` delimiter
before the ordinary input word. A three-state parser copies the two words to fresh work tapes.
Shared work-head rewinds restore both words, `PrepareInput.markBoundary` installs the virtual
input's left marker, and the shared input rewind restores the real input head.

Starting with blank work tapes, preparation takes `5 * coins.length + 3 * input.length + 11`
transitions. The first `k` work tapes stay blank. The next three hold the coins, virtual input,
and input boundary flag, all with heads at zero. This is the layout used by deterministic
replay followed by the shared input-redirection compiler.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PrepareReplay

/-- Tag each coin so that `false` can delimit the coin word. -/
def tagged (left : List Bool) : List Bool := left.flatMap fun bit => [true, bit]
/-- Encode the coin word and ordinary input as one binary input. -/
def encode (left right : List Bool) : List Bool := tagged left ++ false :: right

/-- Tagging uses two bits per coin. -/
@[simp] theorem length_tagged (left : List Bool) : (tagged left).length = 2 * left.length := by
  induction left with
  | nil => simp [tagged]
  | cons b bs ih => simp [tagged, List.length_flatMap] at *; omega

/-- The pair encoding has linear length. -/
@[simp] theorem length_encode (left right : List Bool) :
    (encode left right).length = 2 * left.length + right.length + 1 := by
  simp [encode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Read a tag, a coin, or the untagged ordinary input. -/
inductive ParseState | tag | coin | input deriving DecidableEq
instance : Fintype ParseState := ⟨{.tag, .coin, .input}, by intro q; cases q <;> simp⟩

/-- Copy the two encoded words onto fresh tapes, reserving a third tape for the boundary flag. -/
def parser (k : ℕ) : MultiTapeTM (k + 3) Bool ParseState where
  q₀ := .tag
  tr q symbol _ :=
    match q with
    | .tag =>
      { inputTape := 1, workTapes := fun _ => (none, 0), output := none
        state := some (if symbol = some true then .coin else .input) }
    | .coin =>
      { inputTape := 1
        workTapes := Fin.append (fun _ => (none, 0))
          ![(some symbol, 1), (none, 0), (none, 0)]
        output := none, state := some .tag }
    | .input =>
      { inputTape := if symbol.isSome then 1 else 0
        workTapes := Fin.append (fun _ => (none, 0))
          ![(none, 0), (if symbol.isSome then some symbol else none,
            if symbol.isSome then 1 else 0), (none, 0)]
        output := none, state := if symbol.isSome then some .input else none }

/-- A parser configuration with the copied prefixes and heads at their write frontiers. -/
def config {word : List Bool} (k : ℕ) (q : Option ParseState)
    (position : ℕ) (hpos : position ≤ word.length) (left right : List Bool) :
    Cfg (k + 3) Bool ParseState word where
  state := q
  inputPos := ⟨position + 1, by omega⟩
  workTapes := Fin.append (fun _ _ => none) ![tapeOfList left, tapeOfList right, fun _ => none]
  workTapePos := Fin.append (fun _ => 0) ![(left.length : ℤ), (right.length : ℤ), 0]
  output := []

/-- The parser reads the cell at its logical position, including the final blank. -/
theorem inputSymbol_config {word : List Bool} (k : ℕ) (q : Option ParseState)
    (position : ℕ) (hpos : position ≤ word.length) (left right : List Bool) :
    (config k q position hpos left right).inputSymbol = word[position]? := by
  by_cases h : position < word.length
  · rw [inputSymbolInner position (by simp [config, Nat.add_comm]) h,
      List.getElem?_eq_getElem h]
  · have heq : position = word.length := by omega
    subst position
    rw [inputSymbol_eq_none_of_boundary (Or.inr rfl)]
    simp

/-- A true tag is followed by one coin bit. -/
theorem step_tag {word : List Bool} (k : ℕ) (i : ℕ) (hi : i < word.length)
    (left right : List Bool) (hs : word[i]? = some true) :
    (parser k).step (config k (some .tag) i (by omega) left right) =
      config k (some .coin) (i + 1) hi left right := by
  rw [step_apply_of_state rfl, inputSymbol_config, hs]
  refine Cfg.ext rfl (Fin.ext ?_) rfl ?_ rfl
  · change (moveInputPos (⟨i + 1, by omega⟩ : Fin (word.length + 2)) .pos).val = i + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simp [parser, Action.apply, config]

/-- The false delimiter starts the ordinary input word. -/
theorem step_delimiter {word : List Bool} (k : ℕ) (i : ℕ) (hi : i < word.length)
    (left right : List Bool) (hs : word[i]? = some false) :
    (parser k).step (config k (some .tag) i (by omega) left right) =
      config k (some .input) (i + 1) hi left right := by
  rw [step_apply_of_state rfl, inputSymbol_config, hs]
  refine Cfg.ext rfl (Fin.ext ?_) rfl ?_ rfl
  · change (moveInputPos (⟨i + 1, by omega⟩ : Fin (word.length + 2)) .pos).val = i + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simp [parser, Action.apply, config]

/-- Copy one coin to its work tape. -/
theorem step_coin {word : List Bool} (k : ℕ) (i : ℕ) (hi : i < word.length)
    (left right : List Bool) (b : Bool) (hs : word[i]? = some b) :
    (parser k).step (config k (some .coin) i (by omega) left right) =
      config k (some .tag) (i + 1) hi (left ++ [b]) right := by
  rw [step_apply_of_state rfl, inputSymbol_config, hs]
  refine Cfg.ext rfl (Fin.ext ?_) ?_ ?_ rfl
  · change (moveInputPos (⟨i + 1, by omega⟩ : Fin (word.length + 2)) .pos).val = i + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    induction j using Fin.addCases with
    | left j => simp [parser, Action.apply, config]
    | right j => fin_cases j <;> simp [parser, Action.apply, config, tapeOfList_append_single]
  · funext j
    induction j using Fin.addCases with
    | left j => simp [parser, Action.apply, config]
    | right j => fin_cases j <;> simp [parser, Action.apply, config]

/-- Copy one ordinary input bit to its work tape. -/
theorem step_input {word : List Bool} (k : ℕ) (i : ℕ) (hi : i < word.length)
    (left right : List Bool) (b : Bool) (hs : word[i]? = some b) :
    (parser k).step (config k (some .input) i (by omega) left right) =
      config k (some .input) (i + 1) hi left (right ++ [b]) := by
  rw [step_apply_of_state rfl, inputSymbol_config, hs]
  refine Cfg.ext rfl (Fin.ext ?_) ?_ ?_ rfl
  · change (moveInputPos (⟨i + 1, by omega⟩ : Fin (word.length + 2)) .pos).val = i + 1 + 1
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    induction j using Fin.addCases with
    | left j => simp [parser, Action.apply, config]
    | right j => fin_cases j <;> simp [parser, Action.apply, config, tapeOfList_append_single]
  · funext j
    induction j using Fin.addCases with
    | left j => simp [parser, Action.apply, config]
    | right j => fin_cases j <;> simp [parser, Action.apply, config]

/-- Halt at the blank cell after the input. -/
theorem step_end {word : List Bool} (k : ℕ) (left right : List Bool) :
    (parser k).step (config k (some .input) word.length le_rfl left right) =
      config k none word.length le_rfl left right := by
  rw [step_apply_of_state rfl, inputSymbol_config]
  simp only [List.getElem?_length]
  refine Cfg.ext rfl (by simp [parser, Action.apply, config]) ?_ ?_ rfl <;>
    funext j <;> induction j using Fin.addCases with
  | left j => simp [parser, Action.apply, config]
  | right j => fin_cases j <;> simp [parser, Action.apply, config]


/-- The encoded pair determines both words uniquely. -/
@[simp] theorem encode_inj {left right left' right' : List Bool} :
    encode left right = encode left' right' ↔ left = left' ∧ right = right' := by
  induction left generalizing left' with
  | nil => cases left' <;> simp [encode, tagged]
  | cons b bs ih =>
    cases left' with
    | nil => simp [encode, tagged]
    | cons b' bs' => simpa [encode, tagged, and_assoc] using
        (show b = b' ∧ encode bs right = encode bs' right' ↔
          b = b' ∧ bs = bs' ∧ right = right' by rw [ih])

/-- Every even cell of a tagged word is its tag. -/
theorem tagged_even (left : List Bool) (i : ℕ) (hi : i < left.length) :
    (tagged left)[2 * i]? = some true := by
  induction left generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [tagged]
    | succ i => simpa [tagged, Nat.mul_add, Nat.add_assoc] using ih i (by simpa using hi)

/-- Every odd cell of a tagged word is its original bit. -/
theorem tagged_odd (left : List Bool) (i : ℕ) (hi : i < left.length) :
    (tagged left)[2 * i + 1]? = left[i]? := by
  induction left generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [tagged]
    | succ i => simpa [tagged, Nat.mul_add, Nat.add_assoc] using ih i (by simpa using hi)

/-- Locate a coin's tag within the full encoding. -/
theorem encode_tag (left right : List Bool) (i : ℕ) (hi : i < left.length) :
    (encode left right)[2 * i]? = some true := by
  rw [encode, List.getElem?_append_left (by simp; omega)]
  exact tagged_even left i hi

/-- Locate a coin bit within the full encoding. -/
theorem encode_coin (left right : List Bool) (i : ℕ) (hi : i < left.length) :
    (encode left right)[2 * i + 1]? = some left[i] := by
  rw [encode, List.getElem?_append_left (by simp; omega), tagged_odd left i hi,
    List.getElem?_eq_getElem hi]

/-- The coin prefix is immediately followed by the delimiter. -/
theorem encode_delimiter (left right : List Bool) :
    (encode left right)[2 * left.length]? = some false := by
  simp [encode]

/-- The remaining input cells are the ordinary input word. -/
theorem encode_input (left right : List Bool) (j : ℕ) :
    (encode left right)[2 * left.length + 1 + j]? = right[j]? := by
  simp [encode, List.getElem?_append_right, Nat.add_assoc, Nat.add_comm 1 j]

/-- Two transitions parse one tagged coin. -/
theorem step_pair (k : ℕ) (left right : List Bool) (i : ℕ) (hi : i < left.length) :
    (parser k).runFrom (config (word := encode left right) k (some .tag) (2 * i)
        (by simp; omega) (left.take i) []) 2 =
      config k (some .tag) (2 * (i + 1)) (by simp; omega) (left.take (i + 1)) [] := by
  rw [runFrom_add _ _ 1 1, runFrom_one, runFrom_one,
    step_tag k (2 * i) (by simp; omega) _ _ (encode_tag left right i hi),
    step_coin k (2 * i + 1) (by simp; omega) _ _ _ (encode_coin left right i hi)]
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  congr 1

/-- Parsing `i` coins costs exactly `2 * i` transitions. -/
theorem runFrom_coins (k : ℕ) (left right : List Bool) (i : ℕ) (hi : i ≤ left.length) :
    (parser k).runFrom ((parser k).initCfg (encode left right)) (2 * i) =
      config k (some .tag) (2 * i) (by simp; omega) (left.take i) [] := by
  induction i with
  | zero =>
    simp only [Nat.mul_zero, runFrom_zero, List.take_zero]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
      induction j using Fin.addCases with
    | left j => simp [config, initCfg, Cfg.init]
    | right j => fin_cases j <;> simp [config, initCfg, Cfg.init]
  | succ i ih =>
    conv_lhs => rw [Nat.mul_add, runFrom_add, ih (by omega)]
    exact step_pair k left right i (by omega)

/-- The untagged input is copied one bit per transition. -/
theorem runFrom_input (k : ℕ) (left right : List Bool) (j : ℕ) (hj : j ≤ right.length) :
    (parser k).runFrom
        (config (word := encode left right) k (some .input) (2 * left.length + 1)
          (by simp) left []) j =
      config k (some .input) (2 * left.length + 1 + j) (by simp; omega)
        left (right.take j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [runFrom_add, ih (by omega), runFrom_one,
      step_input k _ (by simp; omega) _ _ _ (by
        rw [encode_input, List.getElem?_eq_getElem (by omega)])]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega : j < right.length)]
    simp only [Option.toList_some]
    congr 1

/-- Parsing takes one transition per encoded bit and one final halting transition. -/
theorem runFrom_parser (k : ℕ) (left right : List Bool) :
    (parser k).runFrom ((parser k).initCfg (encode left right))
        ((encode left right).length + 1) =
      config k none (encode left right).length le_rfl left right := by
  rw [show (encode left right).length + 1 =
      2 * left.length + (1 + (right.length + 1)) by simp [Nat.add_assoc]; omega,
    runFrom_add, runFrom_coins k left right left.length le_rfl,
    List.take_length, runFrom_add, runFrom_one,
    step_delimiter k _ (by simp) _ _ (encode_delimiter left right),
    runFrom_add, runFrom_input k left right right.length le_rfl,
    List.take_length, runFrom_one]
  simpa [length_encode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    step_end (word := encode left right) k left right


/-- The parser, two work rewinds, boundary marker, and input rewind have finite control. -/
abbrev ReadyControl := ParseState ⊕ (RewindWorkState ⊕ (RewindWorkState ⊕ (Bool ⊕ RewindState)))

/-- Parse the pair, rewind both words, mark the virtual input boundary, and restore the input. -/
def prepare (k : ℕ) : MultiTapeTM (k + 3) Bool ReadyControl :=
  (parser k).seq ((rewindWork Bool (Fin.natAdd k 0)).seq
    ((rewindWork Bool (Fin.natAdd k 1)).seq
      ((PrepareInput.markBoundary (k + 2)).seq (rewindInput (k + 3) Bool))))

/-- The ready layout: blank source work tapes, coins, input, and its boundary flag. -/
def prepared {State : Type} (k : ℕ) (left right : List Bool) (q : Option State) :
    Cfg (k + 3) Bool State (encode left right) where
  state := q
  inputPos := 1
  workTapes := Fin.append (fun _ _ => none)
    ![tapeOfList left, tapeOfList right, PrepareInput.flag]
  workTapePos := fun _ => 0
  output := []

/-- Every preparation step is included in the linear bound, starting from blank work tapes. -/
theorem runFrom_prepare (k : ℕ) (left right : List Bool) :
    (prepare k).runFrom ((prepare k).initCfg (encode left right))
        (5 * left.length + 3 * right.length + 11) =
      prepared k left right none := by
  let parsed := config (word := encode left right) k none (encode left right).length
    le_rfl left right
  let first : Cfg (k + 3) Bool RewindWorkState (encode left right) :=
    { parsed.withState none with
      workTapePos := Function.update parsed.workTapePos
        (Fin.natAdd k 0) 0 }
  let second : Cfg (k + 3) Bool RewindWorkState (encode left right) :=
    { first.withState none with
      workTapePos := Function.update first.workTapePos
        (Fin.natAdd k 1) 0 }
  let marked : Cfg (k + 3) Bool Bool (encode left right) :=
    { second.withState none with
      workTapes := Function.update second.workTapes (Fin.last (k + 2))
        (Function.update (second.workTapes (Fin.last (k + 2))) (-1) (some true)) }
  have hlast : (Fin.last (k + 2) : Fin (k + 3)) = Fin.natAdd k (2 : Fin 3) := by
    apply Fin.ext
    simp
  have hbefore (j : Fin k) (i : Fin 3) : j.castAdd 3 ≠ Fin.natAdd k i := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hparse := runFrom_parser k left right
  have hfirst : (rewindWork Bool (Fin.natAdd k 0)).runFrom
      (parsed.withState (some .start)) (left.length + 2) = first := by
    have hpos : parsed.workTapePos (Fin.natAdd k 0) = (left.length : ℤ) := by
      simp [parsed, config]
    have hheads : Function.update parsed.workTapePos (Fin.natAdd k 0) (left.length : ℤ) =
        parsed.workTapePos := by rw [← hpos, Function.update_eq_self]
    simpa only [hheads, first, Cfg.withState, rewindWork] using
      (runFrom_rewindWork_none (i := Fin.natAdd k 0) parsed.inputPos parsed.workTapes
        parsed.workTapePos parsed.output (w := left) (by simp [parsed, config])
        (p := left.length) le_rfl)
  have hsecond : (rewindWork Bool (Fin.natAdd k 1)).runFrom
      (first.withState (some .start)) (right.length + 2) = second := by
    have hpos : first.workTapePos (Fin.natAdd k 1) = (right.length : ℤ) := by
      simp [first, parsed, config]
    have hheads : Function.update first.workTapePos (Fin.natAdd k 1) (right.length : ℤ) =
        first.workTapePos := by rw [← hpos, Function.update_eq_self]
    simpa only [hheads, second, Cfg.withState, rewindWork] using
      (runFrom_rewindWork_none (i := Fin.natAdd k 1) first.inputPos first.workTapes
        first.workTapePos first.output (w := right) (by simp [first, parsed, config, Cfg.withState])
        (p := right.length) le_rfl)
  have hmark : (PrepareInput.markBoundary (k + 2)).runFrom
      (second.withState (some false)) 2 = marked := by
    apply PrepareInput.runFrom_markBoundary second
    simp [second, first, parsed, config, hlast]
  have hrewind : (rewindInput (k + 3) Bool).runFrom
      (marked.withState (some (rewindInput (k + 3) Bool).q₀))
        ((encode left right).length + 2) =
      prepared k left right (none : Option RewindState) := by
    have h := runFrom_rewindInput marked.inputPos marked.workTapes marked.workTapePos marked.output
    change (rewindInput (k + 3) Bool).runFrom
      (marked.withState (some (rewindInput (k + 3) Bool).q₀)) _ = _ at h
    have hpos : marked.inputPos.val - 1 + 2 = (encode left right).length + 2 := rfl
    rw [hpos] at h
    rw [h]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
      induction j using Fin.addCases with
    | left j =>
      simp [marked, second, first, parsed, config, prepared, Cfg.withState, hlast, hbefore]
    | right j =>
      fin_cases j <;> simp [marked, second, first, parsed, config, prepared,
        Cfg.withState, PrepareInput.flag, hlast]
  have htail := runFrom_seq hmark rfl hrewind rfl
  have hmiddle := runFrom_seq hsecond rfl
    (by simpa [Sequential.leftCfg, Cfg.mapState, Cfg.withState, seq, rewindWork,
      PrepareInput.markBoundary, parsed] using htail)
    (by rfl)
  have hcoins := runFrom_seq hfirst rfl
    (by simpa [Sequential.leftCfg, Cfg.mapState, Cfg.withState, seq, rewindWork,
      PrepareInput.markBoundary, parsed] using hmiddle)
    (by rfl)
  have hall := runFrom_seq (tm₁ := (rewindWork Bool (Fin.natAdd k 0)).seq
      ((rewindWork Bool (Fin.natAdd k 1)).seq
        ((PrepareInput.markBoundary (k + 2)).seq (rewindInput (k + 3) Bool)))) hparse rfl
    (by simpa [Sequential.leftCfg, Cfg.mapState, Cfg.withState, seq, rewindWork,
      PrepareInput.markBoundary, parsed] using hcoins)
    (by rfl)
  have htime : (encode left right).length + 1 +
      (left.length + 2 + (right.length + 2 + (2 + ((encode left right).length + 2)))) =
      5 * left.length + 3 * right.length + 11 := by simp; omega
  simp only [length_encode] at htime hall
  rw [htime] at hall
  simpa only [prepare, initCfg_seq, Sequential.rightCfg, prepared, Cfg.mapState,
    Option.map_none] using hall

end Turing.MultiTapeTM.PrepareReplay
