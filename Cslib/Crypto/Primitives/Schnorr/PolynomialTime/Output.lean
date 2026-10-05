/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Execution
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Forgery
import Cslib.Tactic.PolyTime

/-! # Complete saved-tape adversary execution and forgery checking -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool)
  (scalar : ∀ n, Computability.Encoding (F n) Bool)
  {State : Type} {k ports : ℕ}

/-- Check the completed machine's canonical output and final forgery. Successful results keep
the generator, public key, final cache, signing log, and unconsumed private and hash tapes. -/
def checkSeededSignatureMachine (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) :
    Option (Word × Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) := do
  let (candidate, state') ← checkSeededForgeryOutput (element state.1) (scalar state.1)
    state.2.1 state.2.2.1 (if snapshot.state.isNone then some snapshot.output else none)
      state.2.2.2
  pure (pairEncoding wordEncoding
    (pairEncoding (element state.1).toEmbedding (scalar state.1).toEmbedding) candidate,
      ⟨state.1, state.2.1, state.2.2.1, state'⟩)

/-- Execute the actual word adversary, rejecting handler failures, timeout, malformed output,
and invalid or nonfresh forgeries. Final verification uses the same saved hash tape and cache. -/
def runCheckedSeededSignatureMachine (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) :
    Option (Word × Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) := do
  let (final, state') ← machine.runSnapshotFromCoins (m := StateT _ Option) word
    (fun _ => seededSignatureMachineHandler element (fun n => (scalar n).toEmbedding))
      coins snapshot state
  checkSeededSignatureMachine element scalar final state'

variable
  (hz : IsPolyTime unaryEncoding (fun n => (scalar n).encode 0))
  (hgroupDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
    (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
  (hscalarDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
    (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
  (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (scalar n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
  (hadd : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 + arg.2.2)))

include hz hgroupDecode hscalarDecode hsmul hadd

/-- Completion, parsing, final hashing, and verification all have one uniform machine. -/
theorem isPolyTime_checkSeededSignatureMachine (control : State ↪ Word) :
    IsPolyTime (pairEncoding (machineSnapshotEncoding k ports control)
      (seededSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding)))
      (fun pair => optionEncoding (pairEncoding wordEncoding
        (seededSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding)))
        (checkSeededSignatureMachine element scalar pair.1 pair.2)) := by
  let input := pairEncoding (machineSnapshotEncoding k ports control)
    (seededSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding))
  have hi := isPolyTime_input input
  have hp := hi.snd.sigma_fst
  have hg : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1) := by
    dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
    polytime
  have hpk : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.2.1) := by
    dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
    polytime
  have hcheck := isPolyTime_checkSeededForgeryOutput element scalar
    (messages := fun pair => pair.2.2.2.2.1.1) (cache := fun pair => pair.2.2.2.2.1.2)
    (privateScalars := fun pair => pair.2.2.2.2.2.1)
    (hashScalars := fun pair => pair.2.2.2.2.2.2) hp hg hpk
    hi.fst.machineSnapshot_output? (by
      dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
      polytime) (by
      dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
      polytime) (by
      dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
      polytime) (by
      dsimp only [input, seededSignatureMachineStateEncoding, seededSignatureStateEncoding]
      polytime) (hz.comp_encoded hp) hgroupDecode hscalarDecode hsmul hadd
  have hstate := hp.pair (right := wordEncoding)
    (hg.pair (left := wordEncoding) (right := wordEncoding)
      (hpk.pair (left := wordEncoding) (right := wordEncoding) hcheck.tail.bitPair_snd))
  have hsuccess := (hcheck.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert hcheck.option_isSome.cond hsuccess (isPolyTime_const input []) using 1
  funext pair
  dsimp +instances only [checkSeededSignatureMachine]
  cases hrun : checkSeededForgeryOutput (element pair.2.1) (scalar pair.2.1)
    pair.2.2.1 pair.2.2.2.1 (if pair.1.state.isNone then some pair.1.output else none)
      pair.2.2.2.2 <;>
    simp [seededSignatureMachineStateEncoding, sigmaEncoding, pairEncoding_apply,
      wordEncoding]
  rfl

/-- The entire clocked adversary execution and its final verifier are uniformly polynomial.
Only the actual algebra, parsers, and input data need certificates; no whole-run cost is assumed. -/
theorem isPolyTime_runCheckedSeededSignatureMachine [Finite State]
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))
    {α : Type} {input : α → Word} {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word}
    {state : α → Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a =>
      seededSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding) (state a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, ((scalar n).encode value).length ≤ scalarSize n) :
    IsPolyTime input (fun a => optionEncoding (pairEncoding wordEncoding
      (seededSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding)))
      (runCheckedSeededSignatureMachine element scalar machine
        (word a) (coins a) (snapshot a) (state a))) := by
  have hrun := isPolyTime_runSeededSignatureMachine element (fun n => (scalar n).toEmbedding)
    hz hgroupDecode hsmul hsub machine hs hw hc hst hgroup hscalar hgsize hfsize
  simp only [runSnapshotFromCoins_optionT_id] at hrun
  have hfinal := (isPolyTime_checkSeededSignatureMachine element scalar hz hgroupDecode
    hscalarDecode hsmul hadd control).comp_encoded (hrun.option_getD (hs.pair hst))
  exact hrun.option_bind_getD (fallback := fun a => (snapshot a, state a)) hfinal

end Cslib.Crypto.Schnorr
