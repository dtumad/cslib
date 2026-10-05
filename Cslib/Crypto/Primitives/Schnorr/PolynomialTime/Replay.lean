/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Source
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Fork
public import Cslib.Computability.PolynomialTime.Fork.Partial
import Cslib.Tactic.PolyTime

/-! # Uniform replay of the checked Schnorr machine -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool)
  (scalar : ∀ n, Computability.Encoding (F n) Bool)
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
  (hsub : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))

include hz hgroupDecode hscalarDecode hsmul hadd hsub

/-- The hash-only source's successful trace is produced by one uniform machine. Its certificate
comes from the actual checked interpreter and charges for both tapes and the growing cache. -/
theorem isPolyTime_runSignatureFromAnswers
    {α : Type} {input : α → Word} {parameter : α → ℕ}
    {generator publicKey : ∀ a, G (parameter a)}
    {privateScalars hashScalars : ∀ a, List (F (parameter a))}
    {k ports : ℕ} {State : Type} [Finite State] {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word}
    (hp : IsPolyTime input (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime input (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime input (fun a => (element (parameter a)).encode (publicKey a)))
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hprivate : IsPolyTime input (fun a =>
      listEncoding (scalar (parameter a)).toEmbedding (privateScalars a)))
    (hhash : IsPolyTime input (fun a =>
      listEncoding (scalar (parameter a)).toEmbedding (hashScalars a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, ((scalar n).encode value).length ≤ scalarSize n) :
    IsPolyTime input (fun a => optionEncoding
      (pairEncoding (pairEncoding wordEncoding
        (pairEncoding (element (parameter a)).toEmbedding (scalar (parameter a)).toEmbedding))
        (listEncoding (sigmaEncoding
          (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
          (fun _ => (scalar (parameter a)).toEmbedding))))
      (runSignatureFromAnswers (element (parameter a)) (scalar (parameter a)) machine
        (word a) (coins a) (snapshot a) (generator a) (publicKey a)
        (privateScalars a) (hashScalars a))) := by
  let state (a : α) := (⟨parameter a, (generator a, publicKey a, ([], []),
    privateScalars a, hashScalars a), []⟩ : Σ n, (G n × G n ×
      ((List Word × List ((Word × G n) × F n)) × (List (F n) × List (F n)))) ×
        List ((Word × G n) × F n))
  have hst : IsPolyTime input (fun a =>
      tracedSignatureMachineStateEncoding element (fun n => (scalar n).toEmbedding) (state a)) := by
    dsimp only [state, tracedSignatureMachineStateEncoding, seededSignatureStateEncoding]
    polytime
  have hrun := isPolyTime_runCheckedTracedSignatureMachine element scalar hz hgroupDecode
    hscalarDecode hsmul hadd hsub machine hs hw hc hst hgroup hscalar hgsize hfsize
  have hresult := (hrun.tail.bitPair_fst.pair (left := wordEncoding) (right := wordEncoding)
    hrun.tail.bitPair_snd.bitPair_snd.bitPair_snd).option_some
  convert hrun.option_isSome.cond hresult (isPolyTime_const input []) using 1
  funext a
  have heq := congrArg (optionEncoding wordEncoding)
    (runSignatureFromAnswers_encode element scalar machine (word a) (coins a) (snapshot a)
      (parameter a) (generator a) (publicKey a) (privateScalars a) (hashScalars a))
  let output := pairEncoding (pairEncoding wordEncoding
    (pairEncoding (element (parameter a)).toEmbedding (scalar (parameter a)).toEmbedding))
    (listEncoding (sigmaEncoding
      (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
      (fun _ => (scalar (parameter a)).toEmbedding)))
  rw [optionEncoding_map output wordEncoding output (fun _ => rfl)] at heq
  rw [heq]
  cases runCheckedTracedSignatureMachine element scalar machine
    (word a) (coins a) (snapshot a) (state a) <;>
    simp [tracedSignatureMachineStateEncoding, sigmaEncoding, pairEncoding_apply, wordEncoding]

omit hgroupDecode hsub in
/-- A successful recorded run selects its first accepting hash; a rejected run selects none.
The ordinary optional projections avoid arbitrary default candidates. -/
theorem isPolyTime_findForkPoint_traced
    {α : Type} {input : α → Word} {parameter : α → ℕ}
    {generator publicKey : ∀ a, G (parameter a)}
    {result : ∀ a, Option ((Word × G (parameter a) × F (parameter a)) ×
      List (Sigma (PFunctor.mk (Word × G (parameter a)) (fun _ => F (parameter a))).B))}
    (hp : IsPolyTime input (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime input (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime input (fun a => (element (parameter a)).encode (publicKey a)))
    (hr : IsPolyTime input (fun a => optionEncoding
      (pairEncoding (pairEncoding wordEncoding
        (pairEncoding (element (parameter a)).toEmbedding (scalar (parameter a)).toEmbedding))
        (listEncoding (sigmaEncoding
          (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
          (fun _ => (scalar (parameter a)).toEmbedding)))) (result a))) :
    IsPolyTime input (fun a => optionEncoding unaryEncoding ((result a).bind fun out =>
      findForkPoint (generator a) (publicKey a) (some out.1)
        (out.2.map (fun event => (event.1, event.2))))) := by
  have hevents := hr.option_snd.option_getD (fallback := fun _ => [])
    (isPolyTime_const input [])
  have hhashes : IsPolyTime input (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
        (scalar (parameter a)).toEmbedding)
      ((((result a).map Prod.snd).getD []).map (fun event => (event.1, event.2)))) := by
    convert hevents using 1
    funext a
    apply listEncoding_map
    intro event
    rfl
  have hfind := isPolyTime_findForkPoint (fun n => (element n).toEmbedding) scalar
    hp hg hpk hr.option_fst hhashes hz hscalarDecode hsmul hadd
  convert hfind using 1
  funext a
  cases result a <;> rfl

/-- Both checked executions, their common private seed, and the copied answer prefix have one
uniform polynomial-time implementation. Only field/group primitives, parsing, input preparation,
and representation-size bounds are supplied; execution and selection are derived. -/
theorem isPolyTime_forkSignatureFromAnswers
    {Input : Type} (input : Input ↪ Word) {parameter : Input → ℕ}
    {generator publicKey : ∀ a, G (parameter a)}
    {privateScalars : ∀ a, List (F (parameter a))}
    {k ports : ℕ} {State : Type} [Finite State] {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : Input → Snapshot k Bool State (Fin ports)} {word coins : Input → Word}
    (hp : IsPolyTime input (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime input (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime input (fun a => (element (parameter a)).encode (publicKey a)))
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hprivate : IsPolyTime input (fun a =>
      listEncoding (scalar (parameter a)).toEmbedding (privateScalars a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, ((scalar n).encode value).length ≤ scalarSize n) :
    let output i := pairEncoding wordEncoding
      (pairEncoding (element (parameter i)).toEmbedding (scalar (parameter i)).toEmbedding)
    let operation i := pairEncoding wordEncoding (element (parameter i)).toEmbedding
    let answer i := (scalar (parameter i)).toEmbedding
    let events i := listEncoding (sigmaEncoding (operation i) (fun _ => answer i))
    let run i := runSignatureFromAnswers (element (parameter i)) (scalar (parameter i))
      machine (word i) (coins i) (snapshot i) (generator i) (publicKey i) (privateScalars i)
    let choose i (out : (Word × G (parameter i) × F (parameter i)) ×
        List (Sigma (PFunctor.mk (Word × G (parameter i)) (fun _ => F (parameter i))).B)) :=
      findForkPoint (generator i) (publicKey i) (some out.1)
        (out.2.map (fun event => (event.1, event.2)))
    IsPolyTime (sigmaEncoding input (fun i => pairEncoding
      (listEncoding (answer i)) (listEncoding (answer i))))
      (fun pair => optionEncoding (pairEncoding (pairEncoding (output pair.1) (events pair.1))
        (sigmaEncoding (operation pair.1) (fun _ => pairEncoding (answer pair.1)
          (pairEncoding (answer pair.1) (pairEncoding (output pair.1) (events pair.1))))))
        (FreeM.forkFromTracedAnswers (run pair.1) (choose pair.1) pair.2.1 pair.2.2)) := by
  intro output operation answer events run choose
  apply isPolyTime_forkFromTracedAnswers input output operation answer run choose
  · have hi := isPolyTime_input (sigmaEncoding input (fun i => listEncoding (answer i)))
    exact isPolyTime_runSignatureFromAnswers element scalar hz hgroupDecode hscalarDecode hsmul
      hadd hsub machine (hp.comp_encoded hi.sigma_fst) (hg.comp_encoded hi.sigma_fst)
      (hpk.comp_encoded hi.sigma_fst) (hs.comp_encoded hi.sigma_fst)
      (hw.comp_encoded hi.sigma_fst) (hc.comp_encoded hi.sigma_fst)
      (hprivate.comp_encoded hi.sigma_fst) hi.sigma_snd hgroup hscalar hgsize hfsize
  · have hi := isPolyTime_input (sigmaEncoding input (fun i => optionEncoding
      (pairEncoding (output i) (events i))))
    exact isPolyTime_findForkPoint_traced element scalar hz hscalarDecode hsmul hadd
      (hp.comp_encoded hi.sigma_fst) (hg.comp_encoded hi.sigma_fst)
      (hpk.comp_encoded hi.sigma_fst) hi.sigma_snd

end Cslib.Crypto.Schnorr
