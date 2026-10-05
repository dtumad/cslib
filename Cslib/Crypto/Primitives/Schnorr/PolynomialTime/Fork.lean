/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Fork
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
public import Cslib.Computability.PolynomialTime.Encoding.Decoding
import Cslib.Tactic.PolyTime
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Source
public import Cslib.Computability.PolynomialTime.Fork

/-!
# Uniform Schnorr fork selection and replay

The selector searches the recorded fresh hashes. The complete two-run certificate composes
checked machine execution, selection, and prefix copying with one shared private seed.
-/

public section

namespace Cslib.Crypto.Schnorr

section Selection

open Turing.MultiTapeTM

variable {α : Type} {F G : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, DecidableEq (G n)]
  {encode : α → Word} {parameter : α → ℕ}
  (element : ∀ n, G n ↪ Word) (scalar : ∀ n, Computability.Encoding (F n) Bool)
  {generator publicKey : ∀ a, G (parameter a)}
  {candidate : ∀ a, Word × G (parameter a) × F (parameter a)}
  {hashes : ∀ a, List ((Word × G (parameter a)) × F (parameter a))}

/-- Searching the fresh-hash transcript has one uniform machine, including the acceptance
test. The parameter, public key, generator, and candidate are captured by the ordinary list
search API. Its index counts fresh hashes, independently of the adversary's transitions. -/
theorem isPolyTime_findForkPoint_some
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hcandidate : IsPolyTime encode (fun a => pairEncoding wordEncoding
      (pairEncoding (element (parameter a)) (scalar (parameter a)).toEmbedding) (candidate a)))
    (hhashes : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)))
        (scalar (parameter a)).toEmbedding) (hashes a)))
    (hz : IsPolyTime unaryEncoding (fun n => (scalar n).encode 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n).toEmbedding (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding unaryEncoding
      (findForkPoint (generator a) (publicKey a) (some (candidate a)) (hashes a))) := by
  let environment := sigmaEncoding unaryEncoding (fun n => pairEncoding (element n)
    (pairEncoding (element n) (pairEncoding wordEncoding
      (pairEncoding (element n) (scalar n).toEmbedding))))
  let event n := pairEncoding (pairEncoding wordEncoding (element n)) (scalar n).toEmbedding
  let env (a : α) : Σ n, G n × G n × Word × G n × F n :=
    ⟨parameter a, generator a, publicKey a, candidate a⟩
  let predicate (ctx : Σ n, G n × G n × Word × G n × F n) (word : Word) :=
    (List.BitPair.fst word == pairEncoding wordEncoding (element ctx.1)
      (ctx.2.2.2.1, ctx.2.2.2.2.1)) &&
      decide (Accepts ctx.2.1 ctx.2.2.1 ctx.2.2.2.2.1
        (((scalar ctx.1).decode (List.BitPair.snd word)).getD 0) ctx.2.2.2.2.2)
  have henv : IsPolyTime encode (fun a => environment (env a)) :=
    hp.sigma (hg.pair (left := wordEncoding) (right := wordEncoding)
      (hpk.pair (left := wordEncoding) (right := wordEncoding) hcandidate))
  have hwords : IsPolyTime encode (fun a =>
      listEncoding wordEncoding ((hashes a).map (event (parameter a)))) := by
    simpa only [listEncoding_map (event _) wordEncoding (event _) (fun _ => rfl)] using hhashes
  have hi := isPolyTime_input (pairEncoding environment wordEncoding)
  have hn := hi.fst.sigma_fst
  have hzero := hz.comp_encoded hn
  have hchallenge := (hdecode.comp_encoded
    (f := fun pair : (Σ n, G n × G n × Word × G n × F n) × Word =>
      ⟨pair.1.1, List.BitPair.snd pair.2⟩)
    (hn.sigma hi.snd.bitPair_snd)).option_getD hzero
  have haccepts := isPolyTime_accepts (fun n => (scalar n).toEmbedding) element hsmul hadd
  have hcheck := haccepts.comp_encoded
    (encode := pairEncoding environment wordEncoding)
    (f := fun pair : (Σ n, G n × G n × Word × G n × F n) × Word =>
      ⟨pair.1.1, pair.1.2.1, pair.1.2.2.1,
      pair.1.2.2.2.2.1, ((scalar pair.1.1).decode (List.BitPair.snd pair.2)).getD 0,
      pair.1.2.2.2.2.2⟩) (by
      dsimp only [environment]
      polytime)
  have hkey : IsPolyTime (pairEncoding environment wordEncoding) (fun pair =>
      pairEncoding wordEncoding (element pair.1.1) (pair.1.2.2.2.1, pair.1.2.2.2.2.1)) := by
    dsimp only [environment]
    polytime
  have hpredicate : IsPolyTime (pairEncoding environment wordEncoding)
      (fun pair => [predicate pair.1 pair.2]) :=
    (hi.snd.bitPair_fst.beq hkey).bool₂ hcheck Bool.and
  have hfind := hwords.list_findIdx?_with henv hpredicate
  convert hfind using 1
  funext a
  congr 1
  simp only [findForkPoint, List.findIdx?_map, Function.comp_def]
  congr 1
  funext value
  rcases value with ⟨⟨message, commitment⟩, challenge⟩
  simp only [predicate, env, event, pairEncoding_apply, List.BitPair.fst_encode,
    List.BitPair.snd_encode, Computability.Encoding.toEmbedding_apply,
    Computability.Encoding.decode_encode, Option.getD_some, Bool.beq_eq_decide_eq,
    Bool.decide_and, List.BitPair.encode_inj, (element (parameter a)).injective.eq_iff,
    wordEncoding, Function.Embedding.refl_apply, Prod.mk.injEq]

/-- Optional checked output selects no fork when the first run failed. The fallback candidate
is used only inside the machine certificate; it cannot turn failure into a selected query. -/
theorem isPolyTime_findForkPoint
    {candidate : ∀ a, Option (Word × G (parameter a) × F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hcandidate : IsPolyTime encode (fun a => optionEncoding (pairEncoding wordEncoding
      (pairEncoding (element (parameter a)) (scalar (parameter a)).toEmbedding)) (candidate a)))
    (hhashes : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)))
        (scalar (parameter a)).toEmbedding) (hashes a)))
    (hz : IsPolyTime unaryEncoding (fun n => (scalar n).encode 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n).toEmbedding (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding unaryEncoding
      (findForkPoint (generator a) (publicKey a) (candidate a) (hashes a))) := by
  have hread := hcandidate.option_getD (fallback := fun a => ([], generator a, 0))
    ((isPolyTime_const encode []).pair (left := wordEncoding) (right := wordEncoding)
      (hg.pair (left := wordEncoding) (right := wordEncoding) (hz.comp_encoded hp)))
  have hfind := isPolyTime_findForkPoint_some element scalar hp hg hpk hread hhashes
    hz hdecode hsmul hadd
  convert hcandidate.option_isSome.cond hfind (isPolyTime_const encode []) using 1
  funext a
  cases candidate a <;> rfl

end Selection

section Replay

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

end Replay

end Cslib.Crypto.Schnorr
