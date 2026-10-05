/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Output
public import Cslib.Crypto.Primitives.Schnorr.Simulation.Trace

/-! # Uniform execution retaining Schnorr's fresh-hash transcript -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

section Call

variable {α : Type} {F G M Result : α → Type} {encode : α → Word}
  (element : ∀ a, G a ↪ Word) (scalar : ∀ a, F a ↪ Word)
  (messageCode : ∀ a, M a ↪ Word) (output : ∀ a, Result a ↪ Word)
  {state : ∀ a, (List (M a) × List ((M a × G a) × F a)) × (List (F a) × List (F a))}
  {events : ∀ a, List ((M a × G a) × F a)} {fallback : ∀ a, Result a}

/-- Recording a simulator call costs polynomial time in its existing certificate and state.
The default is used inside the certificate only; a failed call still rejects. -/
theorem isPolyTime_traceSeededCall
    (call : ∀ a, StateT ((List (M a) × List ((M a × G a) × F a)) ×
      (List (F a) × List (F a))) Option (Result a))
    (hcall : IsPolyTime encode (fun a => optionEncoding (pairEncoding (output a)
      (seededSignatureStateEncoding (element a) (scalar a) (messageCode a))) (call a (state a))))
    (hstate : IsPolyTime encode (fun a =>
      seededSignatureStateEncoding (element a) (scalar a) (messageCode a) (state a)))
    (hevents : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode a) (element a)) (scalar a)) (events a)))
    (hfallback : IsPolyTime encode (fun a => output a (fallback a))) :
    IsPolyTime encode (fun a => optionEncoding (pairEncoding (output a)
      (pairEncoding (seededSignatureStateEncoding (element a) (scalar a) (messageCode a))
        (listEncoding (pairEncoding (pairEncoding (messageCode a) (element a)) (scalar a)))))
      (traceSeededCall (call a) (state a, events a))) := by
  let result a := (call a (state a)).getD (fallback a, state a)
  have hresult := hcall.option_getD (fallback := fun a => (fallback a, state a))
    (hfallback.pair (left := wordEncoding) (right := wordEncoding) hstate)
  have hbefore : IsPolyTime encode (fun a => listEncoding (scalar a) (state a).2.2) := by
    simpa only [seededSignatureStateEncoding, pairEncoding_apply, List.BitPair.snd_encode] using
      hstate.bitPair_snd.bitPair_snd
  have hafter : IsPolyTime encode (fun a => listEncoding (scalar a) (result a).2.2.2) := by
    simpa only [result, seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.snd_encode] using hresult.bitPair_snd.bitPair_snd.bitPair_snd
  have hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode a) (element a)) (scalar a))
        (result a).2.1.2) := by
    simpa only [result, seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.snd_encode, List.BitPair.fst_encode] using
        hresult.bitPair_snd.bitPair_fst.bitPair_snd
  have hnew := hcache.list_take_indexed (count := fun _ => 1)
    (isPolyTime_const encode [true])
  have hlog : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode a) (element a)) (scalar a))
        (if (state a).2.2.length = (result a).2.2.2.length then events a
          else events a ++ (result a).2.1.2.take 1)) := by
    simpa only [apply_ite, listEncoding_append] using
      (hbefore.list_unaryLength_indexed.unary_eq
        hafter.list_unaryLength_indexed).ite hevents (hevents.append hnew)
  have hsuccess : IsPolyTime encode (fun a => optionEncoding (pairEncoding (output a)
      (pairEncoding (seededSignatureStateEncoding (element a) (scalar a) (messageCode a))
        (listEncoding (pairEncoding (pairEncoding (messageCode a) (element a)) (scalar a)))))
      (some ((result a).1, (result a).2,
        if (state a).2.2.length = (result a).2.2.2.length then events a
          else events a ++ (result a).2.1.2.take 1))) := by
    convert (hresult.bitPair_fst.pair (left := wordEncoding) (right := wordEncoding)
      (hresult.bitPair_snd.pair (left := wordEncoding) (right := wordEncoding) hlog)).option_some
        using 1
    funext a
    simp only [optionEncoding_some, pairEncoding_apply, List.BitPair.fst_encode,
      List.BitPair.snd_encode, wordEncoding, Function.Embedding.refl_apply]
    rfl
  convert hcall.option_isSome.cond hsuccess (isPolyTime_const encode []) using 1
  funext a
  dsimp only [traceSeededCall]
  cases h : call a (state a) with
  | none => rfl
  | some out =>
    by_cases hlen : (state a).2.2.length = out.2.2.2.length <;>
      simp [result, h, hlen]

end Call

section Recorded

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Canonical word requests preserve attribution of cache entries to signatures or fresh hashes. -/
theorem traceSeededSignatureWordHandler_recorded
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    (events : List ((Word × G) × F))
    (hstate : ∀ input challenge, state.1.2.lookup input = some challenge →
      input.1 ∈ state.1.1 ∨ (input, challenge) ∈ events)
    {out : Word × (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F))}
    (h : traceSeededCall (seededSignatureWordHandler element scalar g pk word)
      (state, events) = some out) :
    ∀ input challenge, out.2.1.1.2.lookup input = some challenge →
      input.1 ∈ out.2.1.1.1 ∨ (input, challenge) ∈ out.2.2 := by
  have htyped (op : (Word × G) ⊕ Word)
      (result : ((PFunctor.mk (Word × G) (fun _ => F) +
        PFunctor.mk Word (fun _ => G × F)).B op) ×
          ((List Word × List ((Word × G) × F)) × (List F × List F)))
      (hr : seededSignatureHandler g pk op state = some result) :=
    traceSeededSignatureHandler_recorded g pk op state events
      (fun input challenge hc => hstate input challenge (by
        simpa only [List.lookup_eq_some_iff, bne_iff_ne] using hc))
      (out := (result.1, result.2,
        if state.2.2.length = result.2.2.2.length then events else events ++ result.2.1.2.take 1))
      (by simp only [traceSeededCall, hr]; rfl)
  obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hout
  cases word with
  | nil => cases hresult
  | cons bit payload =>
    cases bit with
    | false =>
      obtain ⟨input, _, hresult⟩ := Option.bind_eq_some_iff.mp hresult
      obtain ⟨answer, hanswer, hresult⟩ := Option.bind_eq_some_iff.mp hresult
      cases Option.some.inj hresult
      intro key value hlookup
      exact htyped (.inl input) answer hanswer key value (by
        simpa only [List.lookup_eq_some_iff, bne_iff_ne] using hlookup)
    | true =>
      obtain ⟨answer, hanswer, hresult⟩ := Option.bind_eq_some_iff.mp hresult
      cases Option.some.inj hresult
      intro key value hlookup
      exact htyped (.inr payload) answer hanswer key value (by
        simpa only [List.lookup_eq_some_iff, bne_iff_ne] using hlookup)

end Recorded

variable {F G : ℕ → Type}

/-- The interpreter retains the ordinary simulator state and a chronological fresh-hash log. -/
def tracedSignatureMachineStateEncoding
    (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word) :
    (Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) ↪ Word :=
  sigmaEncoding unaryEncoding (fun n => pairEncoding
    (pairEncoding (element n).toEmbedding (pairEncoding (element n).toEmbedding
      (seededSignatureStateEncoding (element n).toEmbedding (scalar n) wordEncoding)))
    (listEncoding (pairEncoding (pairEncoding wordEncoding (element n).toEmbedding) (scalar n))))

variable [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word)

/-- The canonical word handler records fresh hashes using the very same cache and tape cursors. -/
def tracedSignatureMachineHandler (word : Word)
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    Option (Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) := do
  let (answer, state', events') ← traceSeededCall
    (seededSignatureWordHandler (element state.1) (scalar state.1)
      state.2.1.1 state.2.1.2.1 word) (state.2.1.2.2, state.2.2)
  pure (answer, ⟨state.1, (state.2.1.1, state.2.1.2.1, state'), events'⟩)

/-- Forgetting the fresh-hash log recovers the original canonical word handler exactly. -/
theorem tracedSignatureMachineHandler_forget (word : Word)
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    (tracedSignatureMachineHandler element scalar word state).map
      (fun out => (out.1, ⟨out.2.1, out.2.2.1⟩)) =
        seededSignatureMachineHandler element scalar word ⟨state.1, state.2.1⟩ := by
  dsimp +instances only [tracedSignatureMachineHandler, traceSeededCall,
    seededSignatureMachineHandler]
  cases seededSignatureWordHandler (element state.1) (scalar state.1)
    state.2.1.1 state.2.1.2.1 word state.2.1.2.2 <;> rfl

/-- The traced handler has one uniform certificate for every security parameter. -/
theorem isPolyTime_tracedSignatureMachineHandler
    (hz : IsPolyTime unaryEncoding (fun n => scalar n 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2))) :
    IsPolyTime (pairEncoding wordEncoding (tracedSignatureMachineStateEncoding element scalar))
      (fun pair => optionEncoding
        (pairEncoding wordEncoding (tracedSignatureMachineStateEncoding element scalar))
        (tracedSignatureMachineHandler element scalar pair.1 pair.2)) := by
  let input := pairEncoding wordEncoding (tracedSignatureMachineStateEncoding element scalar)
  have hi := isPolyTime_input input
  have hp := hi.snd.sigma_fst
  have hdata := hi.snd.sigma_snd.bitPair_fst
  have hg : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode,
      Computability.Encoding.toEmbedding_apply] using hdata.bitPair_fst
  have hpk : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode, List.BitPair.snd_encode,
      Computability.Encoding.toEmbedding_apply] using hdata.bitPair_snd.bitPair_fst
  have hst : IsPolyTime input (fun pair => seededSignatureStateEncoding
      (element pair.2.1).toEmbedding (scalar pair.2.1) wordEncoding pair.2.2.1.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      hdata.bitPair_snd.bitPair_snd
  have hcall := isPolyTime_seededSignatureWordHandler element scalar
    (messages := fun pair => pair.2.2.1.2.2.1.1)
    (cache := fun pair => pair.2.2.1.2.2.1.2)
    (privateScalars := fun pair => pair.2.2.1.2.2.2.1)
    (hashScalars := fun pair => pair.2.2.1.2.2.2.2) hp hg hpk hi.fst
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode] using hst.bitPair_fst.bitPair_fst)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode, List.BitPair.snd_encode] using hst.bitPair_fst.bitPair_snd)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode, List.BitPair.snd_encode] using hst.bitPair_snd.bitPair_fst)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.snd_encode] using hst.bitPair_snd.bitPair_snd)
    (hz.comp_encoded hp) hdecode hsmul hsub
  have hevents : IsPolyTime input (fun pair => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element pair.2.1).toEmbedding) (scalar pair.2.1))
        pair.2.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hi.snd.sigma_snd.bitPair_snd
  have htrace := isPolyTime_traceSeededCall (encode := input)
    (state := fun pair => pair.2.2.1.2.2) (events := fun pair => pair.2.2.2)
    (fun pair => (element pair.2.1).toEmbedding) (fun pair => scalar pair.2.1)
    (fun _ => wordEncoding) (fun _ => wordEncoding)
    (fun pair => seededSignatureWordHandler (element pair.2.1) (scalar pair.2.1)
      pair.2.2.1.1 pair.2.2.1.2.1 pair.1) hcall hst hevents
    (fallback := fun _ => []) (isPolyTime_const input [])
  have hkeys := hg.pair (left := wordEncoding) (right := wordEncoding)
    (hpk.pair (left := wordEncoding) (right := wordEncoding) htrace.tail.bitPair_snd.bitPair_fst)
  have hstate := hp.pair (right := wordEncoding)
    (hkeys.pair (left := wordEncoding) (right := wordEncoding) htrace.tail.bitPair_snd.bitPair_snd)
  have hsuccess := (htrace.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert htrace.option_isSome.cond hsuccess (isPolyTime_const input []) using 1
  funext pair
  dsimp +instances only [tracedSignatureMachineHandler]
  cases traceSeededCall (seededSignatureWordHandler (element pair.2.1) (scalar pair.2.1)
    pair.2.2.1.1 pair.2.2.1.2.1 pair.1) (pair.2.2.1.2.2, pair.2.2.2) <;>
      simp [tracedSignatureMachineStateEncoding, sigmaEncoding, pairEncoding_apply, wordEncoding]
  rfl

end Cslib.Crypto.Schnorr
