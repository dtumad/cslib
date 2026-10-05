/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Machine
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.Tape.Snapshot

/-!
# Finite snapshots of communicating machines

Work and answer tapes are represented relative to their current heads. Query buffers, output,
input position, and control state remain explicit finite data. `Represents` relates a snapshot to
the original configuration; no finiteness claim is made about arbitrary function-valued tapes.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}

/-- Finite communication data, including the current position on the answer tape. -/
@[ext] structure ChannelSnapshot (Symbol : Type) where
  /-- The next request being written. -/
  queryBuffer : List Symbol
  /-- The previous reply, represented around its current head. -/
  answer : Tape.Snapshot (Option Symbol)
deriving Inhabited

/-- All finite data needed to resume a machine. -/
@[ext] structure Snapshot (k : ℕ) (Symbol State Oracle : Type) where
  /-- Current control, or `none` after halting. -/
  state : Option State
  /-- The clamped input position, with the left boundary at zero. -/
  inputPos : ℕ
  /-- Work tapes, each represented around its own head. -/
  workTapes : Fin k → Tape.Snapshot (Option Symbol)
  /-- Output written so far. -/
  output : List Symbol
  /-- Communication buffers and answer tapes. -/
  channels : Oracle → ChannelSnapshot Symbol
deriving Inhabited

namespace Snapshot

/-- The snapshot and original configuration have exactly the same observable tape contents. -/
structure Represents (snapshot : Snapshot k Symbol State Oracle)
    (cfg : Config k Symbol State Oracle input) : Prop where
  /-- Control is preserved. -/
  state : snapshot.state = cfg.tapes.state
  /-- Input positions are preserved. -/
  inputPos : snapshot.inputPos = cfg.tapes.inputPos.val
  /-- Work cells are preserved relative to the current head. -/
  workTapes : ∀ i offset, (snapshot.workTapes i).toTape.nth offset =
    cfg.tapes.workTapes i (cfg.tapes.workTapePos i + offset)
  /-- Output is preserved. -/
  output : snapshot.output = cfg.tapes.output
  /-- Partially written requests are preserved. -/
  queryBuffer : ∀ port, (snapshot.channels port).queryBuffer = (cfg.channels port).queryBuffer
  /-- Reply cells are preserved relative to the current answer head. -/
  answer : ∀ port offset, (snapshot.channels port).answer.toTape.nth offset =
    tapeOfList (cfg.channels port).answer ((cfg.channels port).answerPos + offset)

/-- Start with blank work and communication tapes. -/
def initial (state : State) : Snapshot k Symbol State Oracle where
  state := some state
  inputPos := 1
  workTapes _ := Tape.Snapshot.ofList []
  output := []
  channels _ := ⟨[], Tape.Snapshot.ofList []⟩

private theorem nth_ofList (word : List Symbol) (position : ℤ) :
    (Tape.Snapshot.ofList (word.map some)).toTape.nth position = tapeOfList word position := by
  rw [Tape.Snapshot.toTape_ofList]
  cases position with
  | ofNat n =>
    simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    cases word[n]? <;> rfl
  | negSucc n =>
    simp [Tape.mk₁, Tape.mk₂, Tape.mk', Tape.nth, ListBlank.nth_mk,
      List.getI_eq_getElem?_getD]
    rfl

/-- The finite initial state represents the ordinary blank initialization. -/
theorem represents_initial (state : State) (input : List Symbol) :
    (initial (k := k) (Oracle := Oracle) state).Represents
      ({ tapes := Cfg.init state input } : Config k Symbol State Oracle input) := by
  refine ⟨rfl, rfl, ?_, rfl, fun _ => rfl, ?_⟩
  · intro i offset
    simpa [initial] using nth_ofList ([] : List Symbol) offset
  · intro port offset
    simpa [initial] using nth_ofList ([] : List Symbol) offset

/-- Read the input without including either boundary as an actual symbol. -/
def inputSymbol (snapshot : Snapshot k Symbol State Oracle) (input : List Symbol) : Option Symbol :=
  if snapshot.inputPos = 0 then none else input[snapshot.inputPos - 1]?

/-- Read the head cell of each work tape. -/
def workSymbols (snapshot : Snapshot k Symbol State Oracle) : Fin k → Option Symbol :=
  fun i => (snapshot.workTapes i).head

/-- Read the head cell of each reply tape. -/
def answerSymbols (snapshot : Snapshot k Symbol State Oracle) : Oracle → Option Symbol :=
  fun port => (snapshot.channels port).answer.head

theorem Represents.inputSymbol {snapshot : Snapshot k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle input} (h : snapshot.Represents cfg) :
    snapshot.inputSymbol input = cfg.tapes.inputSymbol := by
  simp only [Snapshot.inputSymbol, h.inputPos, Cfg.inputSymbol]
  split_ifs <;> grind

theorem Represents.workSymbols {snapshot : Snapshot k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle input} (h : snapshot.Represents cfg) :
    snapshot.workSymbols = cfg.tapes.workTapeSymbols := by
  funext i
  simpa [Snapshot.workSymbols, Cfg.workTapeSymbols] using h.workTapes i 0

theorem Represents.answerSymbols {snapshot : Snapshot k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle input} (h : snapshot.Represents cfg) :
    snapshot.answerSymbols = cfg.answerSymbols := by
  funext port
  have ha := h.answer port 0
  simp only [add_zero, Tape.nth_zero, Tape.Snapshot.toTape_head] at ha
  rw [Snapshot.answerSymbols, ha]
  simp only [Config.answerSymbols, Channel.answerSymbol]
  cases (cfg.channels port).answerPos <;> simp [tapeOfList]

/-- Move the input head with the same clamping as the source machine. -/
def moveInput (position length : ℕ) : SignType → ℕ
  | .neg => position - 1
  | .zero => position
  | .pos => min (position + 1) (length + 1)

theorem moveInput_eq (position : Fin (input.length + 2)) (direction : SignType) :
    moveInput position.val input.length direction = (moveInputPos position direction).val := by
  have h := val_moveInputPos_eq position direction
  cases direction <;> simp only [moveInput, SignType.cast] at * <;> omega

/-- Apply an ordinary action using only the finite representation. -/
def step (snapshot : Snapshot k Symbol State Oracle) (input : List Symbol)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) : Snapshot k Symbol State Oracle where
  state := action.state
  inputPos := moveInput snapshot.inputPos input.length action.inputTape
  workTapes i := ((action.workTapes i).1.elim (snapshot.workTapes i)
    (fun symbol => (snapshot.workTapes i).write symbol)).move (action.workTapes i).2
  output := snapshot.output ++ action.output.toList
  channels port := ⟨(snapshot.channels port).queryBuffer ++ (symbol port).toList,
    (snapshot.channels port).answer.move (move port)⟩

/-- Install a reply on one port, preserving the other buffers and tapes. -/
def receive [DecidableEq Oracle] (snapshot : Snapshot k Symbol State Oracle)
    (port : Oracle) (next : State) (answer : List Symbol) : Snapshot k Symbol State Oracle :=
  { snapshot with
    state := some next
    channels := Function.update snapshot.channels port
      ⟨[], Tape.Snapshot.ofList (answer.map some)⟩ }

/-- Each ordinary transition appends at most one symbol to each pending request. -/
theorem length_query_step_le (snapshot : Snapshot k Symbol State Oracle) (input : List Symbol)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) (port : Oracle) :
    ((snapshot.step input action symbol move).channels port).queryBuffer.length ≤
      (snapshot.channels port).queryBuffer.length + 1 := by
  simp only [step, List.length_append]
  cases symbol port <;> simp

/-- Submitting a request clears only that request's buffer. -/
theorem length_query_receive_le [DecidableEq Oracle] (snapshot : Snapshot k Symbol State Oracle)
    (port other : Oracle) (next : State) (answer : List Symbol) :
    ((snapshot.receive port next answer).channels other).queryBuffer.length ≤
      (snapshot.channels other).queryBuffer.length := by
  by_cases he : other = port <;> simp [receive, he]

/-- Local machine actions preserve the representation of every tape and buffer. -/
theorem Represents.step {snapshot : Snapshot k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle input} (h : snapshot.Represents cfg)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (snapshot.step input action symbol move).Represents (cfg.step action symbol move) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Snapshot.step, Config.step, Turing.Action.apply, h.inputPos] using
      moveInput_eq (input := input) cfg.tapes.inputPos action.inputTape
  · intro i offset
    cases hw : (action.workTapes i).1 with
    | none =>
      simpa [Snapshot.step, hw, Tape.Snapshot.nth_move, Config.step, Turing.Action.apply,
        add_assoc, add_left_comm, add_comm] using
          h.workTapes i (offset + ((action.workTapes i).2.cast : ℤ))
    | some value =>
      simp only [Snapshot.step, hw, Option.elim_some, Tape.Snapshot.nth_move,
        Tape.Snapshot.nth_write, Config.step, Turing.Action.apply, Function.update_apply]
      split_ifs with hzero hpos hpos
      · rfl
      · omega
      · omega
      · simpa [add_assoc, add_left_comm, add_comm] using
          h.workTapes i (offset + ((action.workTapes i).2.cast : ℤ))
  · exact congrArg (· ++ action.output.toList) h.output
  · intro port
    simp only [Snapshot.step, Config.step, h.queryBuffer]
  · intro port offset
    simp only [Snapshot.step, Tape.Snapshot.nth_move, h.answer, Config.step]
    congr 1
    omega

/-- Installing a reply preserves the representation and starts its head at position zero. -/
theorem Represents.receive [DecidableEq Oracle] {snapshot : Snapshot k Symbol State Oracle}
    {cfg : Config k Symbol State Oracle input} (h : snapshot.Represents cfg)
    (port : Oracle) (next : State) (answer : List Symbol) :
    (snapshot.receive port next answer).Represents (cfg.receive port next answer) := by
  refine ⟨rfl, h.inputPos, h.workTapes, h.output, ?_, ?_⟩
  · intro other
    by_cases he : other = port
    · subst other; simp [Snapshot.receive, Config.receive]
    · simpa [Snapshot.receive, Config.receive, he] using h.queryBuffer other
  · intro other offset
    by_cases he : other = port
    · subst other
      simpa [Snapshot.receive, Config.receive] using nth_ofList answer offset
    · simpa [Snapshot.receive, Config.receive, he] using h.answer other offset

end Snapshot
end Turing.MultiTapeMachine
