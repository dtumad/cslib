/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Snapshot

/-! # Polynomial-time operations on complete machine snapshots -/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine

variable {α State : Type} {input : α → Word} {k ports : ℕ} {control : State ↪ Word}

/-- A binary cell is either blank or one bit. -/
abbrev cellEncoding : Option Bool ↪ Word := optionEncoding boolEncoding

/-- A channel's unfinished request and its current reply tape. -/
def channelEncoding : ChannelSnapshot Bool ↪ Word where
  toFun channel := pairEncoding wordEncoding (snapshotEncoding cellEncoding)
    (channel.queryBuffer, channel.answer)
  inj' := by
    intro a b h
    have hab := (pairEncoding wordEncoding (snapshotEncoding cellEncoding)).injective h
    exact ChannelSnapshot.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- Encode finite control, the unary input head, and every stored cell and communication buffer. -/
def machineSnapshotEncoding (k ports : ℕ) (control : State ↪ Word) :
    Snapshot k Bool State (Fin ports) ↪ Word where
  toFun snapshot :=
    pairEncoding (optionEncoding control) (pairEncoding unaryEncoding
      (pairEncoding (tupleEncoding k (snapshotEncoding cellEncoding))
        (pairEncoding wordEncoding (tupleEncoding ports channelEncoding))))
      (snapshot.state, snapshot.inputPos, snapshot.workTapes, snapshot.output, snapshot.channels)
  inj' := by
    intro a b h
    have hab := (pairEncoding (optionEncoding control) (pairEncoding unaryEncoding
      (pairEncoding (tupleEncoding k (snapshotEncoding cellEncoding))
        (pairEncoding wordEncoding (tupleEncoding ports channelEncoding))))).injective h
    exact Snapshot.ext (congrArg Prod.fst hab) (congrArg (fun x => x.2.1) hab)
      (congrArg (fun x => x.2.2.1) hab) (congrArg (fun x => x.2.2.2.1) hab)
      (congrArg (fun x => x.2.2.2.2) hab)

/-- Assemble the complete snapshot from efficiently computed components. -/
theorem IsPolyTime.machineSnapshot
    {state : α → Option State} {position : α → ℕ}
    {work : α → Fin k → Tape.Snapshot (Option Bool)} {output : α → Word}
    {channels : α → Fin ports → ChannelSnapshot Bool}
    (hstate : IsPolyTime input (fun a => optionEncoding control (state a)))
    (hposition : IsPolyTime input (fun a => unaryEncoding (position a)))
    (hwork : IsPolyTime input (fun a => tupleEncoding k (snapshotEncoding cellEncoding) (work a)))
    (houtput : IsPolyTime input output)
    (hchannels : IsPolyTime input (fun a => tupleEncoding ports channelEncoding (channels a))) :
    IsPolyTime input (fun a => machineSnapshotEncoding k ports control
      ⟨state a, position a, work a, output a, channels a⟩) :=
  hstate.pair (hposition.pair (hwork.pair (houtput.pair hchannels)))

private theorem IsPolyTime.machineSnapshot_data
    {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a =>
      pairEncoding (optionEncoding control) (pairEncoding unaryEncoding
        (pairEncoding (tupleEncoding k (snapshotEncoding cellEncoding))
          (pairEncoding wordEncoding (tupleEncoding ports channelEncoding))))
        ((snapshot a).state, (snapshot a).inputPos, (snapshot a).workTapes,
          (snapshot a).output, (snapshot a).channels)) := hs

/-- Read finite control. -/
theorem IsPolyTime.machineSnapshot_state {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => optionEncoding control (snapshot a).state) :=
  hs.machineSnapshot_data.fst

/-- Read the unary input head. -/
theorem IsPolyTime.machineSnapshot_position {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => unaryEncoding (snapshot a).inputPos) :=
  hs.machineSnapshot_data.snd.fst

/-- Read all work tapes. -/
theorem IsPolyTime.machineSnapshot_work {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => tupleEncoding k (snapshotEncoding cellEncoding)
      (snapshot a).workTapes) := hs.machineSnapshot_data.snd.snd.fst

/-- Read the accumulated output. -/
theorem IsPolyTime.machineSnapshot_output {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => (snapshot a).output) := hs.machineSnapshot_data.snd.snd.snd.fst

/-- Read all communication data. -/
theorem IsPolyTime.machineSnapshot_channels {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => tupleEncoding ports channelEncoding (snapshot a).channels) :=
  hs.machineSnapshot_data.snd.snd.snd.snd

/-- Assemble a channel, charging for its query and answer data. -/
theorem IsPolyTime.channel {query : α → Word} {answer : α → Tape.Snapshot (Option Bool)}
    (hq : IsPolyTime input query)
    (ha : IsPolyTime input (fun a => snapshotEncoding cellEncoding (answer a))) :
    IsPolyTime input (fun a => channelEncoding ⟨query a, answer a⟩) := hq.pair ha

/-- Read the pending query. -/
theorem IsPolyTime.channel_query {channel : α → ChannelSnapshot Bool}
    (hc : IsPolyTime input (fun a => channelEncoding (channel a))) :
    IsPolyTime input (fun a => (channel a).queryBuffer) :=
  (show IsPolyTime input (fun a => pairEncoding wordEncoding (snapshotEncoding cellEncoding)
    ((channel a).queryBuffer, (channel a).answer)) from hc).fst

/-- Read the reply tape, including its head position. -/
theorem IsPolyTime.channel_answer {channel : α → ChannelSnapshot Bool}
    (hc : IsPolyTime input (fun a => channelEncoding (channel a))) :
    IsPolyTime input (fun a => snapshotEncoding cellEncoding (channel a).answer) :=
  (show IsPolyTime input (fun a => pairEncoding wordEncoding (snapshotEncoding cellEncoding)
    ((channel a).queryBuffer, (channel a).answer)) from hc).snd

/-- Initialize a reply tape from a computed word. -/
theorem IsPolyTime.answerSnapshot {word : α → Word} (hw : IsPolyTime input word) :
    IsPolyTime input (fun a => snapshotEncoding cellEncoding
      (Tape.Snapshot.ofList ((word a).map some))) := by
  have hlist := hw.encode_list_bool.list_map
    (isPolyTime_input boolEncoding).option_some
  have hhead := hlist.list_headD none
  exact (isPolyTime_const input []).snapshot hhead hlist.list_tail

/-- Installing a reply copies it into one selected channel and retains the other machine data. -/
theorem IsPolyTime.machineSnapshot_receive
    {snapshot : α → Snapshot k Bool State (Fin ports)} {port : α → Fin ports}
    {next : α → State} {answer : α → Word}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hp : IsPolyTime input (fun a => finiteEncoding (Fin ports) (port a)))
    (hn : IsPolyTime input (fun a => control (next a)))
    (ha : IsPolyTime input answer) :
    IsPolyTime input (fun a => machineSnapshotEncoding k ports control
      ((snapshot a).receive (port a) (next a) (answer a))) :=
  hn.option_some.machineSnapshot hs.machineSnapshot_position hs.machineSnapshot_work
    hs.machineSnapshot_output (hs.machineSnapshot_channels.tuple_update hp
      ((isPolyTime_const input []).channel ha.answerSnapshot))

/-- Read the input cell, including the clamped machine's two blank boundary positions. -/
theorem IsPolyTime.machineSnapshot_inputSymbol
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word : α → Word}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) :
    IsPolyTime input (fun a => cellEncoding ((snapshot a).inputSymbol (word a))) := by
  have hp := hs.machineSnapshot_position
  simpa only [Snapshot.inputSymbol, apply_ite, cellEncoding, optionEncoding_none] using
    (hp.unary_eq (g := fun _ => 0) (isPolyTime_const input [])).ite
      (isPolyTime_const input [])
      (hw.get? (hp.unary_sub (g := fun _ => 1) (isPolyTime_const input [true])))

/-- Collect the finitely many work-head symbols. -/
theorem IsPolyTime.machineSnapshot_workSymbols
    {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => tupleEncoding k cellEncoding (snapshot a).workSymbols) :=
  IsPolyTime.tuple (fun i => (hs.machineSnapshot_work.tuple_apply i).snapshot_head)

/-- Collect the finitely many answer-head symbols. -/
theorem IsPolyTime.machineSnapshot_answerSymbols
    {snapshot : α → Snapshot k Bool State (Fin ports)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a))) :
    IsPolyTime input (fun a => tupleEncoding ports cellEncoding (snapshot a).answerSymbols) :=
  IsPolyTime.tuple (fun port =>
    (hs.machineSnapshot_channels.tuple_apply port).channel_answer.snapshot_head)

private theorem IsPolyTime.moveInput {position length : α → ℕ}
    (hp : IsPolyTime input (fun a => unaryEncoding (position a)))
    (hl : IsPolyTime input (fun a => unaryEncoding (length a))) (direction : SignType) :
    IsPolyTime input (fun a =>
      unaryEncoding (Snapshot.moveInput (position a) (length a) direction)) :=
  match direction with
  | .neg => hp.unary_sub (g := fun _ => 1) (isPolyTime_const input [true])
  | .zero => hp
  | .pos =>
    (hp.unary_add (g := fun _ => 1) (isPolyTime_const input [true])).unary_min
      (hl.unary_add (g := fun _ => 1) (isPolyTime_const input [true]))

/-- Apply a fixed ordinary transition to encoded data. Every retained tape is copied explicitly. -/
theorem IsPolyTime.machineSnapshot_step
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word : α → Word}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (action : Turing.Action k Bool State)
    (symbol : Fin ports → Option Bool) (move : Fin ports → SignType) :
    IsPolyTime input (fun a => machineSnapshotEncoding k ports control
      ((snapshot a).step (word a) action symbol move)) := by
  apply IsPolyTime.machineSnapshot
  · exact isPolyTime_const input (optionEncoding control action.state)
  · exact hs.machineSnapshot_position.moveInput hw.unaryLength action.inputTape
  · apply IsPolyTime.tuple
    intro i
    have ht := hs.machineSnapshot_work.tuple_apply i
    have hd := isPolyTime_const input (finiteEncoding SignType (action.workTapes i).2)
    cases hwrite : (action.workTapes i).1 with
    | none => exact ht.snapshot_move hd
    | some value =>
      exact (ht.snapshot_write (isPolyTime_const input (cellEncoding value))).snapshot_move hd
  · exact hs.machineSnapshot_output.append (isPolyTime_const input action.output.toList)
  · apply IsPolyTime.tuple
    intro port
    have hc := hs.machineSnapshot_channels.tuple_apply port
    exact (hc.channel_query.append (isPolyTime_const input (symbol port).toList)).channel
      (hc.channel_answer.snapshot_move
        (isPolyTime_const input (finiteEncoding SignType (move port))))

end Turing.MultiTapeTM
