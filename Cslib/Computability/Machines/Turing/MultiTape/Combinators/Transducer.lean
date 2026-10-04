/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Automata.Transducers.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Realizing deterministic word transducers

A word transducer with output blocks of length at most `width` compiles to a machine with no
work tapes. Each input symbol, and the final output block, uses `width + 1` transitions.
The extra transition advances the input head or halts. Empty output blocks require no special
case, and the final output is included in the runtime bound.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Transducer

open Cslib.Automata

variable {Symbol State : Type*}

/-- The output block associated with an input symbol, or with the end of input. -/
def block (transducer : DeterministicTransducer Symbol Symbol State) (state : State) :
    Option Symbol → List Symbol
  | some symbol => transducer.output state symbol
  | none => transducer.finish state

/-- Emit each block in a fixed number of transitions before advancing to the next symbol. -/
def machine (transducer : DeterministicTransducer Symbol Symbol State) (width : ℕ) :
    MultiTapeTM 0 Symbol (State × Fin (width + 1)) where
  q₀ := (transducer.initial, 0)
  tr state symbol _ :=
    if h : state.2.val < width then
      { inputTape := 0, workTapes := Fin.elim0,
        output := (block transducer state.1 symbol)[state.2.val]?,
        state := some (state.1, ⟨state.2.val + 1, by lia⟩) }
    else
      match symbol with
      | some symbol =>
        { inputTape := 1, workTapes := Fin.elim0, output := none,
          state := some (transducer.next state.1 symbol, 0) }
      | none =>
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

private def config (width : ℕ) (input : List Symbol)
    (state : Option (State × Fin (width + 1))) (position : ℕ) (output : List Symbol) :
    Cfg 0 Symbol (State × Fin (width + 1)) input :=
  ⟨state, ⟨min (position + 1) (input.length + 1), by lia⟩, Fin.elim0, Fin.elim0, output⟩

private theorem config_inputSymbol {width : ℕ} {input : List Symbol}
    (state : Option (State × Fin (width + 1))) (position : ℕ) (output : List Symbol)
    (hp : position ≤ input.length) :
    (config width input state position output).inputSymbol = input[position]? := by
  by_cases h : position < input.length
  · rw [inputSymbolInner position (by simp [config]; lia) h, List.getElem?_eq_getElem h]
  · have heq : position = input.length := by lia
    subst position
    rw [inputSymbol_eq_none_of_boundary (Or.inr (by simp [config]))]
    simp

private theorem step_emit (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (input : List Symbol) (state : State) (position index : ℕ)
    (output : List Symbol) (hp : position ≤ input.length) (hi : index < width) :
    (machine transducer width).step
      (config width input (some (state, ⟨index, by lia⟩)) position
        (output ++ (block transducer state input[position]?).take index)) =
      config width input (some (state, ⟨index + 1, by lia⟩)) position
        (output ++ (block transducer state input[position]?).take (index + 1)) := by
  rw [step_apply_of_state rfl, config_inputSymbol _ _ _ hp]
  apply Cfg.ext_zero_tapes
  · simp [machine, hi, Action.apply, config]
  · simp [machine, hi, Action.apply, config]
  · simp only [machine, hi, ↓reduceDIte, Action.apply, config]
    rw [List.take_add_one, List.append_assoc]

private theorem runFrom_emit (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (input : List Symbol) (state : State) (position : ℕ) (output : List Symbol)
    (hp : position ≤ input.length)
    (hw : (block transducer state input[position]?).length ≤ width) :
    (machine transducer width).runFrom
      (config width input (some (state, 0)) position output) width =
      config width input (some (state, Fin.last width)) position
        (output ++ block transducer state input[position]?) := by
  have hscan (index : ℕ) (hi : index ≤ width) :
      (machine transducer width).runFrom
        (config width input (some (state, 0)) position output) index =
        config width input (some (state, ⟨index, by lia⟩)) position
          (output ++ (block transducer state input[position]?).take index) := by
    induction index with
    | zero => simp
    | succ index ih =>
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia)]
      exact step_emit transducer width input state position index output hp (by lia)
  simpa only [List.take_of_length_le hw, Fin.last] using hscan width le_rfl

private theorem step_advance (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (input : List Symbol) (state : State) (position : ℕ) (output : List Symbol)
    (hp : position < input.length) :
    (machine transducer width).step
      (config width input (some (state, Fin.last width)) position output) =
      config width input (some (transducer.next state input[position], 0)) (position + 1)
        output := by
  rw [step_apply_of_state rfl, config_inputSymbol _ _ _ (by lia),
    List.getElem?_eq_getElem hp]
  apply Cfg.ext_zero_tapes
  · simp [machine, Action.apply, config]
  · apply Fin.ext
    simp [machine, Action.apply, config, moveInputPos]
    lia
  · simp [machine, Action.apply, config]

private theorem step_finish (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (input : List Symbol) (state : State) (output : List Symbol) :
    (machine transducer width).step
      (config width input (some (state, Fin.last width)) input.length output) =
      config width input none input.length output := by
  rw [step_apply_of_state rfl, config_inputSymbol _ _ _ le_rfl]
  apply Cfg.ext_zero_tapes <;> simp [machine, Action.apply, config]

private theorem runFrom_suffix (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (hw : ∀ state symbol, (block transducer state symbol).length ≤ width)
    (input remaining : List Symbol) (state : State) (position : ℕ) (output : List Symbol)
    (hp : position ≤ input.length) (hremaining : input.drop position = remaining) :
    (machine transducer width).runFrom
      (config width input (some (state, 0)) position output)
      ((width + 1) * (remaining.length + 1)) =
      config width input none input.length (output ++ transducer.evalFrom state remaining) := by
  induction remaining generalizing state position output with
  | nil =>
    have hposition : position = input.length :=
      le_antisymm hp (List.drop_eq_nil_iff.mp hremaining)
    subst position
    simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [runFrom_add, runFrom_emit transducer width input state _ output le_rfl (hw _ _),
      runFrom_one, step_finish]
    simp [block, DeterministicTransducer.evalFrom]
  | cons symbol remaining ih =>
    have hlength := congrArg List.length hremaining
    simp only [List.length_drop, List.length_cons] at hlength
    have hpos : position < input.length := by lia
    have hread : input[position]? = some symbol := by
      calc
        input[position]? = (input.drop position)[0]? := by simp
        _ = some symbol := by rw [hremaining]; rfl
    have hsymbol : input[position] = symbol := by
      simpa only [List.getElem?_eq_getElem hpos, Option.some.injEq] using hread
    have htail : input.drop (position + 1) = remaining := by
      simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using
        congrArg (List.drop 1) hremaining
    have hfirst : (machine transducer width).runFrom
        (config width input (some (state, 0)) position output) (width + 1) =
        config width input (some (transducer.next state symbol, 0)) (position + 1)
          (output ++ transducer.output state symbol) := by
      rw [runFrom_add, runFrom_emit transducer width input state _ output hp (hw _ _),
        runFrom_one, step_advance _ _ _ _ _ _ hpos, hread, hsymbol]
      rfl
    rw [show (width + 1) * ((symbol :: remaining).length + 1) =
        (width + 1) + (width + 1) * (remaining.length + 1) by
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; lia,
      runFrom_add, hfirst, ih _ _ _ (by lia) htail]
    simp [DeterministicTransducer.evalFrom, List.append_assoc]

/-- The compiled machine realizes the transducer in linear time and zero work space. -/
theorem computesInTimeAndSpace (transducer : DeterministicTransducer Symbol Symbol State)
    (width : ℕ) (hw : ∀ state symbol, (block transducer state symbol).length ≤ width)
    (input : List Symbol) :
    ComputesInTimeAndSpace (machine transducer width) input (transducer.eval input)
      ((width + 1) * (input.length + 1)) 0 := by
  have hinit : (machine transducer width).initCfg input =
      config width input (some (transducer.initial, 0)) 0 [] := by
    apply Cfg.ext_zero_tapes <;> simp [initCfg, Cfg.init, machine, config]
  have hrun := runFrom_suffix transducer width hw input input transducer.initial 0 []
    (by lia) (by simp)
  rw [← hinit] at hrun
  refine ⟨?_, ?_, (machine transducer width).spaceUsed_zero_tapes_eq_zero _ _ rfl⟩
  · rw [hrun]
    rfl
  · rw [hrun]
    rfl

end Turing.MultiTapeTM.Transducer
