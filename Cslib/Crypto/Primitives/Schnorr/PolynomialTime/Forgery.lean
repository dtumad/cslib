/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Handler
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime

/-! # Checking the output of a saved-tape Schnorr execution -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM

/-- Decode the output of an adversary compiled through the typed word interface, then verify
its candidate. Machine timeout, interface failure, and malformed output all reject. -/
def checkSeededForgeryOutput {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (element : Computability.Encoding G Bool)
    (scalar : Computability.Encoding F Bool) (g pk : G) (output : Option Word) :
    StateT ((List Word × List ((Word × G) × F)) × (List F × List F)) Option (Word × G × F) :=
  fun state => do
    let word ← output
    let candidate ← ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.decodeChecked word
    let candidate ← candidate
    checkSeededForgery g pk candidate state

/-- Canonically encoded successful output is checked by the original saved-tape verifier. -/
@[simp] theorem checkSeededForgeryOutput_encode {F G : Type} [Field F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (element : Computability.Encoding G Bool)
    (scalar : Computability.Encoding F Bool) (g pk : G) (candidate : Word × G × F) :
    checkSeededForgeryOutput element scalar g pk
      (some (((Computability.encodingList Bool).bitPair (element.bitPair scalar)).bitOption.encode
        (some candidate))) = checkSeededForgery g pk candidate := by
  funext state
  simp [checkSeededForgeryOutput]

/-- Successful decoding identifies the exact canonical machine output and the checked candidate.
Neither a malformed word nor a valid encoded interface failure can produce a forgery. -/
theorem checkSeededForgeryOutput_eq_some_iff {F G : Type} [Field F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (element : Computability.Encoding G Bool)
    (scalar : Computability.Encoding F Bool) (g pk : G) (output : Option Word)
    (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    (result : (Word × G × F) × ((List Word × List ((Word × G) × F)) × (List F × List F))) :
    checkSeededForgeryOutput element scalar g pk output state = some result ↔
      ∃ candidate, output = some (((Computability.encodingList Bool).bitPair
        (element.bitPair scalar)).bitOption.encode (some candidate)) ∧
          checkSeededForgery g pk candidate state = some result := by
  constructor
  · intro h
    dsimp +instances only [checkSeededForgeryOutput] at h
    obtain ⟨word, hword, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨candidate, hdecode, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨value, rfl, hcheck⟩ := Option.bind_eq_some_iff.mp h
    rw [Computability.Encoding.decodeChecked_eq_some] at hdecode
    exact ⟨value, hdecode ▸ hword, hcheck⟩
  · rintro ⟨candidate, rfl, h⟩
    simpa using h

variable {α : Type} {F G M : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  {encode : α → Word} {parameter : α → ℕ}

/-- Final verification has a uniform certificate, including the last hash query, freshness,
and both tape cursors. An exhausted fresh query rejects; an exhausted cache hit still verifies. -/
theorem isPolyTime_checkSeededForgery
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    {generator publicKey : ∀ a, G (parameter a)}
    {candidate : ∀ a, M (parameter a) × G (parameter a) × F (parameter a)}
    {messages : ∀ a, List (M (parameter a))}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    {privateScalars hashScalars : ∀ a, List (F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hcandidate : IsPolyTime encode (fun a => pairEncoding (messageCode (parameter a))
      (pairEncoding (element (parameter a)) (scalar (parameter a))) (candidate a)))
    (hmessages : IsPolyTime encode (fun a => listEncoding (messageCode (parameter a)) (messages a)))
    (hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (hprivate : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (privateScalars a)))
    (hhash : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (hashScalars a)))
    (hz : IsPolyTime encode (fun a => scalar (parameter a) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a))
        (pairEncoding (element (parameter a)) (scalar (parameter a))))
        (seededSignatureStateEncoding (element (parameter a)) (scalar (parameter a))
          (messageCode (parameter a))))
      (checkSeededForgery (generator a) (publicKey a) (candidate a)
        ((messages a, cache a), privateScalars a, hashScalars a))) := by
  have hm : IsPolyTime encode (fun a => messageCode (parameter a) (candidate a).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hcandidate.bitPair_fst
  have hcommit : IsPolyTime encode (fun a => element (parameter a) (candidate a).2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode, List.BitPair.snd_encode] using
      hcandidate.bitPair_snd.bitPair_fst
  have hresponse : IsPolyTime encode (fun a => scalar (parameter a) (candidate a).2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using
      hcandidate.bitPair_snd.bitPair_snd
  have hquery := isPolyTime_seededSignatureHandler_hash element scalar messageCode
    (generator := generator) (publicKey := publicKey)
    (hm.pair (left := wordEncoding) (right := wordEncoding) hcommit)
    hmessages hcache hprivate hhash
  let result a := seededSignatureHandler (generator a) (publicKey a)
    (.inl ((candidate a).1, (candidate a).2.1))
      ((messages a, cache a), privateScalars a, hashScalars a)
  let fallback a : F (parameter a) ×
      ((List (M (parameter a)) × List ((M (parameter a) × G (parameter a)) × F (parameter a))) ×
        (List (F (parameter a)) × List (F (parameter a)))) :=
    (0, (messages a, cache a), privateScalars a, hashScalars a)
  have hstate := (hmessages.pair (left := wordEncoding) (right := wordEncoding) hcache).pair
    (left := wordEncoding) (right := wordEncoding)
    (hprivate.pair (left := wordEncoding) (right := wordEncoding) hhash)
  have hread := hquery.option_getD (fallback := fallback)
    (hz.pair (left := wordEncoding) (right := wordEncoding) hstate)
  have hc : IsPolyTime encode
      (fun a => scalar (parameter a) ((result a).getD (fallback a)).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hread.bitPair_fst
  have hvalid := (isPolyTime_accepts scalar element hsmul hadd).comp_encoded
    (f := fun a => ⟨parameter a, generator a, publicKey a, (candidate a).2.1,
      ((result a).getD (fallback a)).1, (candidate a).2.2⟩)
    (hp.sigma (hg.pair (left := wordEncoding) (right := wordEncoding)
      (hpk.pair (left := wordEncoding) (right := wordEncoding)
        (hcommit.pair (left := wordEncoding) (right := wordEncoding)
          (hc.pair (left := wordEncoding) (right := wordEncoding) hresponse)))))
  have hfresh := (hm.list_mem_indexed hmessages).map Bool.not
  have hsuccess := (hcandidate.pair (left := wordEncoding) (right := wordEncoding)
    hread.bitPair_snd).option_some
  apply hquery.option_bind_getD (fallback := fallback)
  convert (hvalid.bool₂ hfresh Bool.and).cond hsuccess (isPolyTime_const encode []) using 1
  funext a
  dsimp +instances only [result]
  simp only [decide_not, pairEncoding_apply, List.BitPair.snd_encode]
  split <;> rfl

/-- Checked output decoding and final verification are polynomial uniformly in the parameter.
The two algebra decoders are certified independently; messages use the ordinary word encoding. -/
theorem isPolyTime_checkSeededForgeryOutput
    (element : ∀ n, Computability.Encoding (G n) Bool)
    (scalar : ∀ n, Computability.Encoding (F n) Bool)
    {generator publicKey : ∀ a, G (parameter a)} {output : α → Option Word}
    {messages : α → List Word}
    {cache : ∀ a, List ((Word × G (parameter a)) × F (parameter a))}
    {privateScalars hashScalars : ∀ a, List (F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime encode (fun a => (element (parameter a)).encode (publicKey a)))
    (hout : IsPolyTime encode (fun a => optionEncoding wordEncoding (output a)))
    (hmessages : IsPolyTime encode (fun a => listEncoding wordEncoding (messages a)))
    (hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
        (scalar (parameter a)).toEmbedding) (cache a)))
    (hprivate : IsPolyTime encode
      (fun a => listEncoding (scalar (parameter a)).toEmbedding (privateScalars a)))
    (hhash : IsPolyTime encode
      (fun a => listEncoding (scalar (parameter a)).toEmbedding (hashScalars a)))
    (hz : IsPolyTime encode (fun a => (scalar (parameter a)).encode 0))
    (hgroupDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    (hscalarDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding
      (pairEncoding (pairEncoding wordEncoding
        (pairEncoding (element (parameter a)).toEmbedding (scalar (parameter a)).toEmbedding))
        (seededSignatureStateEncoding (element (parameter a)).toEmbedding
          (scalar (parameter a)).toEmbedding wordEncoding))
      (checkSeededForgeryOutput (element (parameter a)) (scalar (parameter a))
        (generator a) (publicKey a) (output a)
        ((messages a, cache a), privateScalars a, hashScalars a))) := by
  let code n := (Computability.encodingList Bool).bitPair ((element n).bitPair (scalar n))
  let word a := (output a).getD []
  have hw : IsPolyTime encode word := hout.option_getD (isPolyTime_const encode [])
  have hgd := hgroupDecode.comp_encoded (f := fun a =>
    ⟨parameter a, List.BitPair.fst (List.BitPair.snd (word a).tail)⟩)
    (hp.sigma hw.tail.bitPair_snd.bitPair_fst)
  have hsd := hscalarDecode.comp_encoded (f := fun a =>
    ⟨parameter a, List.BitPair.snd (List.BitPair.snd (word a).tail)⟩)
    (hp.sigma hw.tail.bitPair_snd.bitPair_snd)
  have hm : IsPolyTime encode (fun a => optionEncoding wordEncoding
      (some (List.BitPair.fst (word a).tail))) := hw.tail.bitPair_fst.option_some
  have hdecode : IsPolyTime encode (fun a => optionEncoding (code (parameter a)).toEmbedding
      ((code (parameter a)).decode (word a).tail)) :=
    hm.option_pair (hgd.option_pair hsd)
  have hchecked := IsPolyTime.decodeChecked_indexed code hw.tail hdecode
  let candidate a := ((code (parameter a)).decodeChecked (word a).tail).getD
    ([], generator a, 0)
  have hc : IsPolyTime encode (fun a => (code (parameter a)).encode (candidate a)) :=
    hchecked.option_getD ((isPolyTime_const encode []).pair
      (left := wordEncoding) (right := wordEncoding)
      (hg.pair (left := wordEncoding) (right := wordEncoding) hz))
  have hcheck := isPolyTime_checkSeededForgery
    (fun n => (element n).toEmbedding) (fun n => (scalar n).toEmbedding) (fun _ => wordEncoding)
    (candidate := candidate) hp hg hpk hc hmessages hcache hprivate hhash hz hsmul hadd
  have hfinish := hchecked.option_bind_getD (fallback := fun a => ([], generator a, 0))
    (cont := fun a candidate => checkSeededForgery (generator a) (publicKey a) candidate
      ((messages a, cache a), privateScalars a, hashScalars a)) hcheck
  convert (hw.headD false).cond hfinish (isPolyTime_const encode []) using 1
  funext a
  dsimp +instances only [checkSeededForgeryOutput, word]
  cases output a with
  | none => rfl
  | some word =>
    cases word with
    | nil => rfl
    | cons bit word =>
      cases bit with
      | false => rfl
      | true =>
        simp only [Bind.bind, Option.bind, Computability.Encoding.decodeChecked_bitOption_true,
          Option.getD_some, List.headD_cons, ↓reduceIte, List.tail_cons]
        cases (code (parameter a)).decodeChecked word <;> rfl

end Cslib.Crypto.Schnorr
