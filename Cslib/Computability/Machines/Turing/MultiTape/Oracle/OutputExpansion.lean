/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Simulation

/-!
# Replacing each output bit by a fixed word

`expandOutput machine code` implements `List.flatMap code` on a machine's output. The two
codewords are fixed independently of the input and security parameter. They may have different
lengths, including zero.

One source transition is implemented by a block of `max |code false| |code true| + 2` transitions.
The first transition performs the source action and saves its output bit in finite control; the
remaining transitions emit the codeword and pad the block. Thus even a source run stopped by its
external clock has exactly the intended output. Oracle queries and private oracle states are
preserved, and the construction uses no additional work tapes.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State OracleState : Type} {input : List Bool}

namespace OutputExpansion

/-- The maximum length of the two fixed codewords. -/
def width (code : Bool → List Bool) : ℕ := max (code false).length (code true).length

/-- An absent source output contributes the empty word. -/
def block (code : Bool → List Bool) (bit : Option Bool) : List Bool := bit.toList.flatMap code

theorem length_block_le (code : Bool → List Bool) (bit : Option Bool) :
    (block code bit).length ≤ width code := by
  cases bit with
  | none => simp [block]
  | some bit => cases bit <;> simp [block, width]

/-- The source state, or a finite buffer containing a bit and its next output position. -/
abbrev Control (State : Type) (width : ℕ) :=
  State ⊕ (Option State × Option Bool × Fin (width + 1))

/-- A source configuration at the boundary between simulation blocks. -/
def config (width : ℕ) (cfg : Config k State input) (output : List Bool) :
    Config k (Control State width) input :=
  { cfg with tapes := { cfg.tapes.mapState (Option.map Sum.inl) with output := output } }

/-- A configuration partway through emitting the buffered codeword. -/
def pending (width : ℕ) (cfg : Config k State input) (bit : Option Bool)
    (index : Fin (width + 1)) (output : List Bool) : Config k (Control State width) input :=
  { cfg with tapes := { cfg.tapes.withState (some (.inr (cfg.tapes.state, bit, index))) with
      output := output } }

end OutputExpansion

open OutputExpansion

/-- Replace each output bit by its fixed codeword, using a constant number of transitions per
source transition. The buffer and index are part of finite control. -/
@[simps! initial] def expandOutput (machine : OracleTM k State) (code : Bool → List Bool) :
    OracleTM k (Control State (width code)) :=
  Turing.OracleTM.mk (.inl machine.initial) fun state symbol work answer coin =>
    match state with
    | .inl state =>
      match machine.transition state symbol work answer coin with
      | .step action bit move =>
        .step { action with output := none, state := some (.inr (action.state, action.output, 0)) }
          bit move
      | .query next => .query (.inr (some next, none, 0))
    | .inr (next, bit, index) =>
      .step
        { inputTape := 0
          workTapes := fun _ => (none, 0)
          output := (block code bit)[index.val]?
          state := if h : index.val + 1 < width code + 1 then
            some (.inr (next, bit, ⟨index.val + 1, h⟩)) else next.map .inl } none 0

/-- The transition table in the compact single-operation interface. -/
@[simp] theorem expandOutput_transition (machine : OracleTM k State) (code : Bool → List Bool) :
    (expandOutput machine code).transition =
  fun state symbol work answer coin =>
    match state with
    | .inl state =>
      match machine.transition state symbol work answer coin with
      | .step action bit move =>
        .step { action with output := none, state := some (.inr (action.state, action.output, 0)) }
          bit move
      | .query next => .query (.inr (some next, none, 0))
    | .inr (next, bit, index) =>
      .step
        { inputTape := 0
          workTapes := fun _ => (none, 0)
          output := (block code bit)[index.val]?
          state := if h : index.val + 1 < width code + 1 then
            some (.inr (next, bit, ⟨index.val + 1, h⟩)) else next.map .inl } none 0 := by
  funext state symbol work answer coin
  simp only [expandOutput, Turing.OracleTM.transition_mk]

namespace OutputExpansion

@[simp] theorem config_state (width : ℕ) (cfg : Config k State input) (output : List Bool) :
    (config width cfg output).tapes.state = cfg.tapes.state.map Sum.inl := rfl

@[simp] theorem config_inputSymbol (width : ℕ) (cfg : Config k State input) (output : List Bool) :
    (config width cfg output).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (width : ℕ) (cfg : Config k State input)
    (output : List Bool) : (config width cfg output).tapes.workTapeSymbols =
      cfg.tapes.workTapeSymbols := rfl

@[simp] theorem config_answerSymbol (width : ℕ) (cfg : Config k State input)
    (output : List Bool) : (config width cfg output).answerSymbol = cfg.answerSymbol := rfl

@[simp] theorem config_queryBuffer (width : ℕ) (cfg : Config k State input)
    (output : List Bool) : (config width cfg output).queryBuffer = cfg.queryBuffer := rfl

@[simp] theorem config_output (width : ℕ) (cfg : Config k State input) (output : List Bool) :
    (config width cfg output).tapes.output = output := rfl

@[simp] theorem pending_state (width : ℕ) (cfg : Config k State input) (bit : Option Bool)
    (index : Fin (width + 1)) (output : List Bool) :
    (pending width cfg bit index output).tapes.state =
      some (.inr (cfg.tapes.state, bit, index)) := rfl

/-- A padding transition changes only the finite buffer index and emitted output. -/
theorem step_pending (width : ℕ) (cfg : Config k State input) (bit emitted : Option Bool)
    (index index' : Fin (width + 1)) (output : List Bool) :
    (pending width cfg bit index output).step
      { inputTape := 0, workTapes := fun _ => (none, 0), output := emitted,
        state := some (.inr (cfg.tapes.state, bit, index')) } none 0 =
      pending width cfg bit index' (output ++ emitted.toList) := by
  simp [pending, Config.step, Action.apply, Cfg.withState]

/-- The last padding transition returns to the source control state, possibly halted. -/
theorem step_pending_last (width : ℕ) (cfg : Config k State input) (bit emitted : Option Bool)
    (index : Fin (width + 1)) (output : List Bool) :
    (pending width cfg bit index output).step
      { inputTape := 0, workTapes := fun _ => (none, 0), output := emitted,
        state := cfg.tapes.state.map Sum.inl } none 0 =
      config width cfg (output ++ emitted.toList) := by
  simp [pending, config, Config.step, Action.apply, Cfg.withState, Cfg.mapState]

/-- Emitting a buffered codeword is deterministic and does not call or modify the oracle. -/
theorem runState_pending (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (bit : Option Bool) (remaining : ℕ) (s : OracleState) :
    ∀ (index : Fin (width code + 1)) (output : List Bool), index.val + remaining = width code + 1 →
      OracleComp.runState oracle
        ((machine.expandOutput code).runConfigFrom remaining
          (pending (width code) cfg bit index output)) s =
        PMF.pure (config (width code) cfg (output ++ (block code bit).drop index.val), s) := by
  induction remaining with
  | zero => intro index output h; have := index.isLt; omega
  | succ remaining ih =>
    intro index output h
    simp only [runConfigFrom_succ, pending_state, expandOutput_transition]
    by_cases hi : index.val + 1 < width code + 1
    · simp only [hi, ↓reduceDIte, step_pending, OracleComp.uniform,
        OracleComp.runState_sample_bind]
      simp only [ih ⟨index.val + 1, hi⟩
        (output ++ (block code bit)[index.val]?.toList) (by simp; omega), PMF.bind_const]
      congr 2
      rw [List.append_assoc, ← List.drop_eq_getElem?_toList_append]
    · have hlast : index.val = width code := by have := index.isLt; omega
      have hremaining : remaining = 0 := by omega
      subst remaining
      simp only [hi, ↓reduceDIte, step_pending_last, runConfigFrom_zero,
        OracleComp.uniform, OracleComp.runState_sample_bind, OracleComp.runState_pure,
        PMF.bind_const]
      have hlength : (block code bit).length ≤ index.val := by
        simpa [hlast] using length_block_le code bit
      simp [List.getElem?_eq_none hlength, List.drop_eq_nil_of_le hlength]

/-- A complete buffer flush appends precisely the saved bit's codeword. -/
theorem runState_pending_zero (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (bit : Option Bool) (output : List Bool) (s : OracleState) :
    OracleComp.runState oracle
      ((machine.expandOutput code).runConfigFrom (width code + 1)
        (pending (width code) cfg bit 0 output)) s =
      PMF.pure (config (width code) cfg (output ++ block code bit), s) := by
  simpa using runState_pending machine code oracle cfg bit (width code + 1) s 0 output (by simp)

theorem step_config (width : ℕ) (cfg : Config k State input) (output : List Bool)
    (action : Action k Bool State) (bit : Option Bool) (move : SignType) :
    (config width cfg output).step
      { action with output := none, state := some (.inr (action.state, action.output, 0)) }
      bit move = pending width (cfg.step action bit move) action.output 0 output := by
  simp [config, pending, Config.step, Action.apply, Cfg.mapState, Cfg.withState]

theorem receive_config (width : ℕ) (cfg : Config k State input) (output : List Bool)
    (next : State) (answer : List Bool) :
    (config width cfg output).receive (.inr (some next, none, 0)) answer =
      pending width (cfg.receive next answer) none 0 output := rfl

/-- One fixed-length block simulates one source transition, including any oracle query. -/
theorem runState_block (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (cfg : Config k State input)
    (s : OracleState) :
    OracleComp.runState oracle
      ((machine.expandOutput code).runConfigFrom (width code + 2)
        (config (width code) cfg (cfg.tapes.output.flatMap code))) s =
      (OracleComp.runState oracle (machine.runConfigFrom 1 cfg) s).map
        (fun (final, s') => (config (width code) final (final.tapes.output.flatMap code), s')) := by
  cases hs : cfg.tapes.state with
  | none => simp [hs, PMF.pure_map]
  | some state =>
    conv_lhs => rw [runConfigFrom_succ]
    conv_rhs => rw [runConfigFrom_succ]
    simp only [config_state, hs, Option.map_some, config_inputSymbol,
      config_workTapeSymbols, config_answerSymbol, expandOutput_transition, OracleComp.uniform,
      OracleComp.runState_sample_bind, PMF.map_bind]
    congr 1
    funext coin
    cases ha : machine.transition state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbol coin with
    | step action bit move =>
      simp only
      rw [step_config, runState_pending_zero]
      simp [Config.step, Action.apply, block, List.flatMap_append, PMF.pure_map]
    | query next =>
      simp only [config_queryBuffer, OracleComp.runState_bind, OracleComp.runState_query,
        PMF.map_bind]
      congr 1
      funext result
      rw [receive_config, runState_pending_zero]
      simp [block, Config.receive, PMF.pure_map]

end OutputExpansion

/-- Output expansion preserves every clocked run, including the complete oracle state. -/
theorem runState_runConfigFrom_expandOutput (machine : OracleTM k State)
    (code : Bool → List Bool) (oracle : List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle
      ((machine.expandOutput code).runConfigFrom ((width code + 2) * fuel)
        (config (width code) cfg (cfg.tapes.output.flatMap code))) s =
      (OracleComp.runState oracle (machine.runConfigFrom fuel cfg) s).map
        (fun (final, s') => (config (width code) final (final.tapes.output.flatMap code), s')) :=
  runState_runConfigFrom_mul machine (machine.expandOutput code)
    (fun cfg => config (width code) cfg (cfg.tapes.output.flatMap code))
    (width code + 2) oracle (runState_block machine code oracle) fuel cfg s

/-- The expanded output is the concatenation of the codewords for the source output bits. -/
theorem runState_runFrom_expandOutput (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (cfg : Config k State input) (s : OracleState) :
    OracleComp.runState oracle
      ((machine.expandOutput code).runFrom ((width code + 2) * fuel)
        (config (width code) cfg (cfg.tapes.output.flatMap code))) s =
      (OracleComp.runState oracle (machine.runFrom fuel cfg) s).map
        (fun (word, s') => (word.flatMap code, s')) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_expandOutput machine code oracle fuel cfg s)
  simpa [runFrom_eq_map_runConfigFrom, OracleComp.runState_map, PMF.map_comp,
    Function.comp_def] using h

/-- Output expansion from the initial configuration, with an explicit constant slowdown. -/
theorem runState_run_expandOutput (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (input : List Bool) (s : OracleState) :
    OracleComp.runState oracle ((machine.expandOutput code).run ((width code + 2) * fuel) input) s =
      (OracleComp.runState oracle (machine.run fuel input) s).map
        (fun (word, s') => (word.flatMap code, s')) :=
  runState_runFrom_expandOutput machine code oracle fuel (machine.initialConfig input) s

/-- The corresponding output-distribution equation for a memoryless oracle. -/
theorem eval_run_expandOutput (machine : OracleTM k State) (code : Bool → List Bool)
    (oracle : List Bool → PMF (List Bool)) (fuel : ℕ) (input : List Bool) :
    OracleComp.eval oracle ((machine.expandOutput code).run ((width code + 2) * fuel) input) =
      (OracleComp.eval oracle (machine.run fuel input)).map (List.flatMap code) := by
  have h := congrArg (PMF.map Prod.fst) (runState_run_expandOutput machine code
    (fun q (s : Unit) => (oracle q).map (fun a => (a, s))) fuel input ())
  simp only [OracleComp.runState_stateless, PMF.map_comp] at h
  simpa [Function.comp_def, PMF.map] using h

end Turing.OracleTM
