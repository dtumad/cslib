/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Replay
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot.Option

/-! # Uniform execution with aborting deterministic handlers -/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {Oracle S : Type} {stateEncoding : S ↪ Word}

/-- A certified partial handler can retain a failure flag while the machine finishes its
clock. The handler's certificate covers rejection, and no default state is needed. -/
theorem isPolyTime_totalizeHandler
    (handler : Oracle → Word → S → Option (Word × S))
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => optionEncoding (pairEncoding wordEncoding stateEncoding)
        (handler port pair.1 pair.2))) (port : Oracle) :
    IsPolyTime (pairEncoding wordEncoding (pairEncoding stateEncoding boolEncoding))
      (fun pair => pairEncoding wordEncoding (pairEncoding stateEncoding boolEncoding)
        (Id.run ((totalizeHandler (m := Id)
          (fun port request state => OptionT.mk (pure (handler port request state)))
            port pair.1).run pair.2))) := by
  let input := pairEncoding wordEncoding (pairEncoding stateEncoding boolEncoding)
  have hw := isPolyTime_fst wordEncoding (pairEncoding stateEncoding boolEncoding)
  have hs := (isPolyTime_snd wordEncoding (pairEncoding stateEncoding boolEncoding)).fst
  have ha := (isPolyTime_snd wordEncoding (pairEncoding stateEncoding boolEncoding)).snd
  have hcall := (hhandler port).comp_encoded
    (f := fun pair : Word × S × Bool => (pair.1, pair.2.1)) (hw.pair hs)
  have hresult := hcall.option_getD
    (fallback := fun pair => ([], pair.2.1))
    ((isPolyTime_const input []).pair (right := stateEncoding)
      (g := fun pair : Word × S × Bool => pair.2.1) hs)
  have h := (ha.cond hresult.fst (isPolyTime_const input [])).pair
    (left := wordEncoding) (right := wordEncoding)
    ((ha.cond hresult.snd hs).pair (left := wordEncoding) (right := boolEncoding)
      (ha.bool₂ hcall.option_isSome (· && ·)))
  convert h using 1
  funext ⟨word, state, active⟩
  cases active <;> cases h : handler port word state <;>
    simp [totalizeHandler, StateT.run, h] <;> rfl

variable {α State : Type} {k ports : ℕ} [Finite State]
  {input : α → Word} {control : State ↪ Word}

/-- The snapshot interpreter implements partial handlers with one uniform polynomial machine.
Successful replies preserve the representation invariant and have polynomial size and state
growth; rejection itself introduces no further requests or successful output. -/
theorem isPolyTime_runSnapshotFromCoins_optionT_of_growth
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : Fin ports → Word → S → Option (Word × S))
    (hhandler : ∀ port, IsPolyTime (pairEncoding wordEncoding stateEncoding)
      (fun pair => optionEncoding (pairEncoding wordEncoding stateEncoding)
        (handler port pair.1 pair.2)))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word} {state : α → S}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => stateEncoding (state a)))
    (invariant : α → S → Prop) (hinit : ∀ a, invariant a (state a))
    {reply growth : ℕ → ℕ} (hreply : PolynomiallyBounded reply)
    (hgrowth : PolynomiallyBounded growth)
    (hcall : ∀ a port request st,
      request.length ≤ (machineSnapshotEncoding k ports control (snapshot a)).length +
        (coins a).length → invariant a st → ∀ out, handler port request st = some out →
      invariant a out.2 ∧ out.1.length ≤ reply (input a).length ∧
        (stateEncoding out.2).length ≤ (stateEncoding st).length + growth (input a).length) :
    IsPolyTime input (fun a =>
      optionEncoding (pairEncoding (machineSnapshotEncoding k ports control) stateEncoding)
        (Id.run (((machine.runSnapshotFromCoins (m := StateT S (OptionT Id)) (word a)
          (fun port request state => OptionT.mk (pure (handler port request state)))
          (coins a) (snapshot a)).run (state a)).run))) := by
  let aborting : Fin ports → Word → StateT S (OptionT Id) Word :=
    fun port request state => OptionT.mk (pure (handler port request state))
  let total : Fin ports → Word → S × Bool → Word × S × Bool :=
    fun port request st => Id.run ((totalizeHandler aborting port request).run st)
  have htotal := isPolyTime_totalizeHandler handler hhandler
  have hrun := isPolyTime_runSnapshotFromCoins_of_growth machine total htotal hs hw hc
    (hst.pair (isPolyTime_const input [true]))
    (fun a st => invariant a st.1) hinit hreply
    (growth := fun n => 2 * growth n) (by fun_prop) (by
      rintro a port request ⟨st, active⟩ hrequest hinv
      cases active with
      | false =>
        simpa [total, aborting, totalizeHandler, StateT.run] using
          (show invariant a st ∧ 0 ≤ reply (input a).length ∧
            (pairEncoding stateEncoding boolEncoding (st, false)).length ≤
              (pairEncoding stateEncoding boolEncoding (st, false)).length +
                2 * growth (input a).length from ⟨hinv, Nat.zero_le _, Nat.le_add_right _ _⟩)
      | true =>
        cases hresult : handler port request st with
        | none =>
          simpa [total, aborting, totalizeHandler, StateT.run, hresult, length_pairEncoding,
            boolEncoding] using
            (show invariant a st ∧ 0 ≤ reply (input a).length ∧
              2 * (stateEncoding st).length + 2 ≤
                2 * (stateEncoding st).length + 2 + 2 * growth (input a).length from
                  ⟨hinv, Nat.zero_le _, Nat.le_add_right _ _⟩)
        | some out =>
          obtain ⟨hinv', hreply', hgrowth'⟩ := hcall a port request st hrequest hinv out hresult
          refine ⟨by simpa [total, aborting, totalizeHandler, StateT.run, hresult] using hinv',
            by simpa [total, aborting, totalizeHandler, StateT.run, hresult] using hreply', ?_⟩
          simp only [total, aborting, totalizeHandler, StateT.run, hresult, ↓reduceIte,
            OptionT.run_mk, pure_bind, Id.run_pure, Option.elim_some,
            length_pairEncoding, boolEncoding, Function.Embedding.coeFn_mk, List.length_singleton]
          omega)
  have hfinish := hrun.snd.snd.cond (hrun.fst.pair hrun.snd.fst).option_some
    (isPolyTime_const input [])
  convert hfinish using 1
  funext a
  have h := runSnapshotFromCoins_totalizeHandler (m := Id) machine (word a) aborting
    (coins a) (snapshot a) (state a) true
  simp only [↓reduceIte] at h
  have hvalue := congrArg Id.run h.symm
  simp only [Id.run_map] at hvalue
  have heq : (fun port request st => (pure (total port request st) : Id _)) =
      totalizeHandler aborting := by
    funext port request st
    exact Id.pure_run _
  rw [heq, hvalue]
  split <;> simp_all

end Turing.MultiTapeTM
