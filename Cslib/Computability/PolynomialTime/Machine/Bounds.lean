/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Size
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot

/-!
# Space accounting for stateful replay

Request lengths are bounded by the initial buffers plus the number of transitions. Bounds on
reply lengths and per-call handler-state growth then give a linear bound on the stored execution.
The handler invariant may retain a security parameter, cache validity, or a fixed seed budget.
-/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {State S : Type} {k ports : ℕ} {control : State ↪ Word} {stateEncoding : S ↪ Word}

/-- Replay preserves the handler invariant and charges for all snapshots, replies, and state
growth. The request bound depends on the transition budget, not on the size of earlier replies. -/
theorem runSnapshotFromCoins_bound
    (machine : MultiTapePTM k Bool State (Fin ports)) (input coins : Word)
    (handler : Fin ports → Word → S → Word × S)
    (snapshot : Snapshot k Bool State (Fin ports)) (state : S)
    {bound queryBound replyBound growth : ℕ}
    (hcontrol : ∀ state, (control state).length ≤ bound)
    (hqueries : ∀ port, (snapshot.channels port).queryBuffer.length ≤ queryBound)
    (invariant : S → Prop) (hinit : invariant state)
    (hhandler : ∀ port request state, request.length ≤ queryBound + coins.length →
      invariant state →
      invariant (handler port request state).2 ∧
        (handler port request state).1.length ≤ replyBound ∧
        (stateEncoding (handler port request state).2).length ≤
          (stateEncoding state).length + growth) :
    let final := Id.run ((machine.runSnapshotFromCoins (m := StateT S Id) input
      (fun port request st => pure (handler port request st)) coins snapshot).run state)
    invariant final.2 ∧
      (∀ port, (final.1.channels port).queryBuffer.length ≤ queryBound + coins.length) ∧
      (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding final).length ≤
        (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
          (snapshot, state)).length + coins.length *
          (2 * (2 * bound + 56 * k + 24 * ports + 6 +
            20 * ports * (replyBound + 1)) + growth) := by
  let encoding := pairEncoding (machineSnapshotEncoding k ports control) stateEncoding
  let delta := 2 * (2 * bound + 56 * k + 24 * ports + 6 +
    20 * ports * (replyBound + 1)) + growth
  apply runSnapshotFromCoins_stateT_spec machine _ coins snapshot state
    (fun index pair => invariant pair.2 ∧
      (∀ port, (pair.1.channels port).queryBuffer.length ≤ queryBound + index) ∧
      (encoding pair).length ≤ (encoding (snapshot, state)).length + index * delta)
  · exact ⟨hinit, by simpa using hqueries, by simp⟩
  · rintro index ⟨current, st⟩ bit hi ⟨hinvariant, hq, hsize⟩
    dsimp only at hinvariant hq hsize
    cases hs : current.state with
    | none =>
      simp only [stepSnapshot, hs]
      refine ⟨hinvariant, fun port => (hq port).trans (by omega), ?_⟩
      change (encoding (current, st)).length ≤ _
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    | some q =>
      simp only [stepSnapshot, hs]
      cases ha : machine.tr q (current.inputSymbol input) current.workSymbols
          current.answerSymbols bit with
      | step action symbol move =>
        change invariant st ∧ _ ∧ _
        refine ⟨hinvariant, ?_, ?_⟩
        · intro port
          exact (current.length_query_step_le input action symbol move port).trans (by
            have := hq port
            omega)
        · have hnext := length_machineSnapshotEncoding_step_le current input action symbol move
            hcontrol
          change (encoding (current.step input action symbol move, st)).length ≤ _
          simp only [encoding, length_pairEncoding] at hsize ⊢
          dsimp only [delta] at hsize ⊢
          rw [Nat.add_mul, Nat.one_mul]
          omega
      | query port next =>
        let answer := handler port (current.channels port).queryBuffer st
        have hr := hhandler port (current.channels port).queryBuffer st
          (by have := hq port; omega) hinvariant
        change invariant answer.2 ∧ _ ∧ _
        refine ⟨hr.1, ?_, ?_⟩
        · intro other
          exact (current.length_query_receive_le port other next answer.1).trans (by
            have := hq other
            omega)
        · have hnext := length_machineSnapshotEncoding_receive_le current port next answer.1
            hcontrol
          have hreply := Nat.mul_le_mul_left (20 * ports) (Nat.add_le_add_right hr.2.1 1)
          change (encoding (current.receive port next answer.1, answer.2)).length ≤ _
          simp only [encoding, length_pairEncoding] at hsize ⊢
          dsimp only [delta] at hsize ⊢
          rw [Nat.add_mul, Nat.one_mul]
          have hstate := hr.2.2
          change (stateEncoding answer.2).length ≤ (stateEncoding st).length + growth at hstate
          change 20 * ports * (answer.1.length + 1) ≤ _ at hreply
          omega

end Turing.MultiTapeTM
