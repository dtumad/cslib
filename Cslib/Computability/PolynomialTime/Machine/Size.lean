/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine

/-!
# Size bounds for encoded machine snapshots

An ordinary transition increases the representation by a fixed constant. Receiving an answer
additionally charges for the entire reply. In particular, small transition tables alone do not
hide the cost of large oracle answers.
-/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine

variable {State : Type} {k ports : ℕ} {control : State ↪ Word}

@[simp] theorem length_cellEncoding_le (cell : Option Bool) :
    (cellEncoding cell).length ≤ 2 := by
  cases cell <;> simp [cellEncoding, boolEncoding]

@[simp] theorem length_channelEncoding (channel : ChannelSnapshot Bool) :
    (channelEncoding channel).length = 2 * channel.queryBuffer.length +
      (snapshotEncoding cellEncoding channel.answer).length + 1 := by
  change (pairEncoding wordEncoding (snapshotEncoding cellEncoding)
    (channel.queryBuffer, channel.answer)).length = _
  simp [wordEncoding]

@[simp] theorem length_machineSnapshotEncoding (snapshot : Snapshot k Bool State (Fin ports)) :
    (machineSnapshotEncoding k ports control snapshot).length =
      2 * (optionEncoding control snapshot.state).length + 2 * snapshot.inputPos +
        2 * (tupleEncoding k (snapshotEncoding cellEncoding) snapshot.workTapes).length +
        2 * snapshot.output.length +
        (tupleEncoding ports channelEncoding snapshot.channels).length + 4 := by
  change (pairEncoding (optionEncoding control) (pairEncoding unaryEncoding
    (pairEncoding (tupleEncoding k (snapshotEncoding cellEncoding))
      (pairEncoding wordEncoding (tupleEncoding ports channelEncoding))))
    (snapshot.state, snapshot.inputPos, snapshot.workTapes, snapshot.output,
      snapshot.channels)).length = _
  simp only [length_pairEncoding, unaryEncoding_apply, List.length_replicate,
    wordEncoding, Function.Embedding.refl_apply]
  omega

/-- A pending request fits within its complete snapshot's representation. -/
theorem length_query_le_machineSnapshotEncoding
    (snapshot : Snapshot k Bool State (Fin ports)) (port : Fin ports) :
    (snapshot.channels port).queryBuffer.length ≤
      (machineSnapshotEncoding k ports control snapshot).length := by
  have hchannel := length_element_le_length_listEncoding channelEncoding
    (List.mem_ofFn.mpr ⟨port, rfl⟩ : snapshot.channels port ∈ List.ofFn snapshot.channels)
  change (channelEncoding (snapshot.channels port)).length ≤
    (tupleEncoding ports channelEncoding snapshot.channels).length at hchannel
  simp only [length_channelEncoding] at hchannel
  simp only [length_machineSnapshotEncoding]
  omega

private theorem length_option_control_le {bound : ℕ}
    (hcontrol : ∀ state, (control state).length ≤ bound) (state : Option State) :
    (optionEncoding control state).length ≤ bound + 1 := by
  cases state with
  | none => simp
  | some state => simpa using Nat.add_le_add_right (hcontrol state) 1

/-- Initializing an answer tape has linear size in the full received word. -/
theorem length_answerSnapshot_le (answer : Word) :
    (snapshotEncoding cellEncoding (Tape.Snapshot.ofList (answer.map some))).length ≤
      10 * (answer.length + 1) := by
  have htail := length_listEncoding_le cellEncoding
    (values := (answer.map some).tail) (bound := 2)
    (fun cell _ => length_cellEncoding_le cell)
  have hhead := length_cellEncoding_le ((answer.map some).headD default)
  simp only [length_snapshotEncoding, Tape.Snapshot.ofList, listEncoding_nil,
    List.length_nil, Nat.mul_zero, Nat.zero_add]
  simp only [List.length_tail, List.length_map] at htail
  omega

/-- One ordinary transition has a constant increase depending only on the fixed machine. -/
theorem length_machineSnapshotEncoding_step_le (snapshot : Snapshot k Bool State (Fin ports))
    (input : Word) (action : Turing.Action k Bool State)
    (symbol : Fin ports → Option Bool) (move : Fin ports → SignType)
    {bound : ℕ} (hcontrol : ∀ state, (control state).length ≤ bound) :
    (machineSnapshotEncoding k ports control (snapshot.step input action symbol move)).length ≤
      (machineSnapshotEncoding k ports control snapshot).length +
        (2 * bound + 56 * k + 24 * ports + 6) := by
  have hstate := length_option_control_le hcontrol action.state
  have hposition : Snapshot.moveInput snapshot.inputPos input.length action.inputTape ≤
      snapshot.inputPos + 1 := by
    cases action.inputTape <;> simp [Snapshot.moveInput]
    omega
  have hwork : ∀ i, (snapshotEncoding cellEncoding
      ((snapshot.step input action symbol move).workTapes i)).length ≤
        (snapshotEncoding cellEncoding (snapshot.workTapes i)).length + 14 := by
    intro i
    have hmove := length_snapshotEncoding_move_le
      ((action.workTapes i).1.elim (snapshot.workTapes i)
        (fun cell => (snapshot.workTapes i).write cell)) (action.workTapes i).2
          length_cellEncoding_le
    cases hw : (action.workTapes i).1 with
    | none =>
      simp only [hw, Option.elim_none] at hmove
      simpa only [Snapshot.step, hw, Option.elim_none] using hmove.trans (by omega)
    | some cell =>
      have hwrite := length_snapshotEncoding_write_le (snapshot.workTapes i) cell
        (length_cellEncoding_le cell)
      simp only [hw, Option.elim_some] at hmove
      change (snapshotEncoding cellEncoding
        (((action.workTapes i).1.elim (snapshot.workTapes i)
          (fun cell => (snapshot.workTapes i).write cell)).move _)).length ≤ _
      simp only [hw, Option.elim_some]
      omega
  have hwork := length_tupleEncoding_le hwork
  have hchannels : ∀ port, (channelEncoding
      ((snapshot.step input action symbol move).channels port)).length ≤
        (channelEncoding (snapshot.channels port)).length + 12 := by
    intro port
    have hmove := length_snapshotEncoding_move_le (snapshot.channels port).answer (move port)
      length_cellEncoding_le
    simp only [length_channelEncoding, Snapshot.step, List.length_append]
    have : (symbol port).toList.length ≤ 1 := by cases symbol port <;> simp
    omega
  have hchannels := length_tupleEncoding_le hchannels
  have houtput : action.output.toList.length ≤ 1 := by cases action.output <;> simp
  simp only [length_machineSnapshotEncoding, Snapshot.step, List.length_append]
  dsimp only [Snapshot.step] at hwork hchannels
  omega

/-- Receiving a reply retains all other data and charges linearly for the reply's size. -/
theorem length_machineSnapshotEncoding_receive_le
    (snapshot : Snapshot k Bool State (Fin ports)) (port : Fin ports) (next : State) (answer : Word)
    {bound : ℕ} (hcontrol : ∀ state, (control state).length ≤ bound) :
    (machineSnapshotEncoding k ports control (snapshot.receive port next answer)).length ≤
      (machineSnapshotEncoding k ports control snapshot).length +
        (2 * bound + 2 + 20 * ports * (answer.length + 1)) := by
  have hstate := length_option_control_le hcontrol (some next)
  have hchannels : ∀ other, (channelEncoding
      ((snapshot.receive port next answer).channels other)).length ≤
        (channelEncoding (snapshot.channels other)).length + 10 * (answer.length + 1) := by
    intro other
    by_cases he : other = port
    · subst other
      have hanswer := length_answerSnapshot_le answer
      simp only [Snapshot.receive, Function.update_self, length_channelEncoding, List.length_nil]
      omega
    · simp [Snapshot.receive, Function.update_of_ne he]
  have hchannels := length_tupleEncoding_le hchannels
  simp only [length_machineSnapshotEncoding, Snapshot.receive]
  dsimp only [Snapshot.receive] at hchannels
  simp only [← Nat.mul_assoc] at hchannels
  rw [Nat.mul_right_comm 2 ports 10] at hchannels
  change _ ≤ _ + 20 * ports * (answer.length + 1) at hchannels
  omega

end Turing.MultiTapeTM
