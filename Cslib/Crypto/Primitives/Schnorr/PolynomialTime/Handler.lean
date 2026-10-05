/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Simulation
public import Cslib.Crypto.Primitives.Schnorr.Simulation.Seeded
public import Cslib.Crypto.Primitives.Schnorr.Encoding
public import Cslib.Computability.PolynomialTime.Encoding.Decoding

/-! # Uniform certificates for Schnorr's saved-tape handler -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM

/-- Encode the signing log, shared cache, private scalars, and fresh hash answers together. -/
def seededSignatureStateEncoding {F G M : Type}
    (element : G ↪ Word) (scalar : F ↪ Word) (messageCode : M ↪ Word) :
    ((List M × List ((M × G) × F)) × (List F × List F)) ↪ Word :=
  pairEncoding
    (pairEncoding (listEncoding messageCode)
      (listEncoding (pairEncoding (pairEncoding messageCode element) scalar)))
    (pairEncoding (listEncoding scalar) (listEncoding scalar))

section Typed

variable {α : Type} {F G M : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  {encode : α → Word} {parameter : α → ℕ}
  (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
  {generator publicKey : ∀ a, G (parameter a)} {message : ∀ a, M (parameter a)}
  {messages : ∀ a, List (M (parameter a))}
  {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
  {privateScalars hashScalars : ∀ a, List (F (parameter a))}

/-- Cached hashes advance only the fresh-answer tape, and the certificate charges for the
complete returned state. Cache hits remain successful with an exhausted hash tape. -/
theorem isPolyTime_seededSignatureHandler_hash {commitment : ∀ a, G (parameter a)}
    (hinput : IsPolyTime encode (fun a => pairEncoding
      (messageCode (parameter a)) (element (parameter a)) (message a, commitment a)))
    (hmessages : IsPolyTime encode (fun a => listEncoding (messageCode (parameter a)) (messages a)))
    (hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (hprivate : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (privateScalars a)))
    (hhash : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (hashScalars a))) :
    IsPolyTime encode (fun a => optionEncoding (pairEncoding (scalar (parameter a))
      (seededSignatureStateEncoding (element (parameter a)) (scalar (parameter a))
        (messageCode (parameter a))))
      (seededSignatureHandler (generator a) (publicKey a) (.inl (message a, commitment a))
        ((messages a, cache a), privateScalars a, hashScalars a))) := by
  have hlookup := hinput.list_lookup_indexed (parameter := parameter)
    (key := fun n => pairEncoding (messageCode n) (element n)) (value := scalar) hcache
  have hquery := RandomOracle.isPolyTime_query_option (parameter := parameter)
    (key := fun n => pairEncoding (messageCode n) (element n)) (value := scalar)
    hinput hcache hhash.list_head?_indexed
  have htapes := hprivate.pair (left := wordEncoding) (right := wordEncoding)
    (hlookup.option_isSome.cond hhash hhash.list_tail_indexed)
  have hstate := (hmessages.pair (left := wordEncoding) (right := wordEncoding)
    hquery.tail.bitPair_snd).pair (left := wordEncoding) (right := wordEncoding) htapes
  have hsuccess := (hquery.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert hquery.option_isSome.cond hsuccess (isPolyTime_const encode []) using 1
  funext a
  cases hfind : (cache a).lookup (message a, commitment a) with
  | some answer =>
    rw [seededSignatureHandler_hash_hit _ _ _ _ _ _ _ answer hfind]
    simp [RandomOracle.query, hfind, seededSignatureStateEncoding, pairEncoding_apply,
      wordEncoding]
    rfl
  | none =>
    cases hh : hashScalars a with
    | nil =>
      rw [seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hfind]
      simp only [RandomOracle.query, hfind, List.head?_nil]
      rfl
    | cons answer rest =>
      rw [seededSignatureHandler_hash_miss _ _ _ _ _ _ _ answer hfind]
      simp [RandomOracle.query, hfind, seededSignatureStateEncoding, pairEncoding_apply,
        wordEncoding]
      rfl

/-- Signing uses the original simulator, advances its private tape by two scalars, and retains
the hash tape. Exhaustion and a programming collision both reject before returning any state. -/
theorem isPolyTime_seededSignatureHandler_sign
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hm : IsPolyTime encode (fun a => messageCode (parameter a) (message a)))
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
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 - arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding
      (pairEncoding (pairEncoding (element (parameter a)) (scalar (parameter a)))
        (seededSignatureStateEncoding (element (parameter a)) (scalar (parameter a))
          (messageCode (parameter a))))
      (seededSignatureHandler (generator a) (publicKey a) (.inr (message a))
        ((messages a, cache a), privateScalars a, hashScalars a))) := by
  have hsign := isPolyTime_simulateSign_option element scalar messageCode hp hg hpk hm hcache
    hprivate.list_head?_indexed hprivate.list_tail_indexed.list_head?_indexed hz hsmul hsub
  have hlog := hm.pair (left := wordEncoding) (right := wordEncoding) hmessages
  have htapes := hprivate.list_tail_indexed.list_tail_indexed.pair
    (left := wordEncoding) (right := wordEncoding) hhash
  have hstate := (hlog.pair (left := wordEncoding) (right := wordEncoding)
    hsign.tail.tail.bitPair_snd).pair (left := wordEncoding) (right := wordEncoding) htapes
  have hsuccess := (hsign.tail.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  have hpresent := hsign.option_isSome.bool₂ (hsign.tail.headD false) Bool.and
  convert hpresent.cond hsuccess (isPolyTime_const encode []) using 1
  funext a
  cases hh : privateScalars a with
  | nil =>
    rw [seededSignatureHandler_sign_exhausted _ _ _ _ _ _ _ (by simp)]
    rfl
  | cons challenge rest =>
    cases rest with
    | nil =>
      rw [seededSignatureHandler_sign_exhausted _ _ _ _ _ _ _ (by simp)]
      rfl
    | cons response rest =>
      rw [seededSignatureHandler_sign]
      simp only [List.head?_cons, List.tail_cons, Option.map₂_some_some]
      unfold simulateSign.finish
      split <;> simp [seededSignatureStateEncoding, pairEncoding_apply, wordEncoding]
      rfl

end Typed

/-- A word interface to the saved-tape simulator. Zero tags a canonically encoded hash input;
one tags a signing message. Malformed requests and simulator failures both reject the call. -/
def seededSignatureWordHandler {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G) :
    Word → StateT ((List Word × List ((Word × G) × F)) × (List F × List F)) Option Word
  | [], _ => none
  | false :: payload, state => do
      let input ← ((Computability.encodingList Bool).bitPair element).decodeChecked payload
      let (answer, state') ← seededSignatureHandler g pk (.inl input) state
      pure (scalar answer, state')
  | true :: message, state => do
      let (signature, state') ← seededSignatureHandler g pk (.inr message) state
      pure (pairEncoding element.toEmbedding scalar signature, state')

/-- The efficient word handler is exactly the canonical typed adapter, collapsing only failures.
The equality includes malformed requests, cache contents, and both saved tape cursors. -/
theorem seededSignatureWordHandler_eq_decodeQuery {F G : Type}
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (element : Computability.Encoding G Bool) (scalar : Computability.Encoding F Bool)
    (g pk : G) (word : Word)
    (state : (List Word × List ((Word × G) × F)) × (List F × List F)) :
    seededSignatureWordHandler element scalar.toEmbedding g pk word state = (do
      let (out, state') ← (decodeQuery
        (P := PFunctor.mk (Word × G) (fun _ => F) + PFunctor.mk Word (fun _ => G × F))
        (signatureRequestEncoding (Computability.encodingList Bool) element)
        (signatureResponseEncoding element scalar) (seededSignatureHandler g pk) word).run state
      let answer ← out
      pure (answer, state')) := by
  cases word with
  | nil => rfl
  | cons bit payload =>
    cases bit with
    | false =>
      simp only [seededSignatureWordHandler, decodeQuery, signatureRequestEncoding,
        OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, OptionT.run_pure]
      rw [Computability.Encoding.decodeChecked_bitSum_false]
      cases h : ((Computability.encodingList Bool).bitPair element).decodeChecked payload with
      | none => rfl
      | some input =>
        dsimp only [Option.map, Option.elimM, Option.elim, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Option.bind, monadLift_self, Functor.map, StateT.map]
        cases seededSignatureHandler g pk (.inl input) state <;> rfl
    | true =>
      simp only [seededSignatureWordHandler, decodeQuery, signatureRequestEncoding]
      rw [Computability.Encoding.decodeChecked_bitSum_true]
      have h : (Computability.encodingList Bool).decodeChecked payload = some payload :=
        Computability.Encoding.decodeChecked_encode (Computability.encodingList Bool) payload
      rw [h]
      dsimp only [Option.map, OptionT.run, OptionT.mk, Bind.bind, StateT.bind, OptionT.bind,
        Pure.pure, StateT.pure, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift,
        Option.bind]
      cases seededSignatureHandler g pk (.inr payload) state <;> rfl

section Word

variable {α : Type} {F G : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, DecidableEq (G n)]
  {encode : α → Word} {parameter : α → ℕ}
  (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word)
  {generator publicKey : ∀ a, G (parameter a)} {request : α → Word}
  {messages : α → List Word}
  {cache : ∀ a, List ((Word × G (parameter a)) × F (parameter a))}
  {privateScalars hashScalars : ∀ a, List (F (parameter a))}

/-- The complete word handler has a single uniform certificate, including request validation,
both adaptive oracle branches, response encoding, the signed-message log, and both tape cursors. -/
theorem isPolyTime_seededSignatureWordHandler
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => (element (parameter a)).encode (generator a)))
    (hpk : IsPolyTime encode (fun a => (element (parameter a)).encode (publicKey a)))
    (hrequest : IsPolyTime encode request)
    (hmessages : IsPolyTime encode (fun a => listEncoding wordEncoding (messages a)))
    (hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)).toEmbedding)
        (scalar (parameter a))) (cache a)))
    (hprivate : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (privateScalars a)))
    (hhash : IsPolyTime encode (fun a => listEncoding (scalar (parameter a)) (hashScalars a)))
    (hz : IsPolyTime encode (fun a => scalar (parameter a) 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding (pairEncoding wordEncoding
      (seededSignatureStateEncoding (element (parameter a)).toEmbedding (scalar (parameter a))
        wordEncoding))
      (seededSignatureWordHandler (element (parameter a)) (scalar (parameter a))
        (generator a) (publicKey a) (request a)
          ((messages a, cache a), privateScalars a, hashScalars a))) := by
  let hashCode (n : ℕ) := (Computability.encodingList Bool).bitPair (element n)
  let parsed (a : α) := (hashCode (parameter a)).decodeChecked (request a).tail
  have hgroup := hdecode.comp_encoded
    (f := fun a => ⟨parameter a, List.BitPair.snd (request a).tail⟩)
    (hp.sigma hrequest.tail.bitPair_snd)
  have hparser : IsPolyTime encode (fun a => optionEncoding
      (hashCode (parameter a)).toEmbedding ((hashCode (parameter a)).decode (request a).tail)) :=
    (hrequest.tail.bitPair_fst.option_some
      (element := fun _ => wordEncoding)).option_pair hgroup
  have hparsed := IsPolyTime.decodeChecked_indexed hashCode hrequest.tail hparser
  have harg := hparsed.option_getD (fallback := fun a => ([], generator a))
    ((isPolyTime_const encode []).pair (left := wordEncoding) (right := wordEncoding) hg)
  have hmessage : IsPolyTime encode (fun a => (parsed a).getD ([], generator a) |>.1) := by
    simpa only [parsed, hashCode, Computability.Encoding.bitPair_toEmbedding, pairEncoding_apply,
      List.BitPair.fst_encode, Computability.Encoding.toEmbedding_apply,
      Computability.encodingList, id_eq] using harg.bitPair_fst
  have hcommitment : IsPolyTime encode (fun a => (element (parameter a)).encode
      ((parsed a).getD ([], generator a)).2) := by
    simpa only [parsed, hashCode, Computability.Encoding.bitPair_toEmbedding, pairEncoding_apply,
      List.BitPair.snd_encode, Computability.Encoding.toEmbedding_apply] using harg.bitPair_snd
  have hhashCall := isPolyTime_seededSignatureHandler_hash
    (generator := generator) (publicKey := publicKey)
    (fun n => (element n).toEmbedding) scalar (fun _ => wordEncoding)
    (hmessage.pair (left := wordEncoding) (right := wordEncoding) hcommitment)
    hmessages hcache hprivate hhash
  have hhashResult := hparsed.option_isSome.cond hhashCall (isPolyTime_const encode [])
  have hsignCall := isPolyTime_seededSignatureHandler_sign
    (fun n => (element n).toEmbedding) scalar (fun _ => wordEncoding)
    hp hg hpk hrequest.tail hmessages hcache hprivate hhash hz hsmul hsub
  have hbranch := (hrequest.headD false).cond hsignCall hhashResult
  have hempty := hrequest.unaryLength.unary_eq (g := fun _ => 0) (isPolyTime_const encode [])
  convert hempty.cond (isPolyTime_const encode []) hbranch using 1
  funext a
  dsimp +instances only [parsed, hashCode]
  cases hw : request a with
  | nil => rfl
  | cons bit payload =>
    cases bit with
    | false =>
      dsimp +instances only [seededSignatureWordHandler, List.tail_cons, List.headD_cons,
        List.length_cons, Option.getD]
      cases hparse : ((Computability.encodingList Bool).bitPair
        (element (parameter a))).decodeChecked payload with
      | none => rfl
      | some input =>
        dsimp only [Bind.bind, Option.bind]
        cases seededSignatureHandler (generator a) (publicKey a) (.inl input)
          ((messages a, cache a), privateScalars a, hashScalars a) <;> rfl
    | true =>
      dsimp +instances only [seededSignatureWordHandler, List.tail_cons, List.headD_cons,
        List.length_cons]
      cases seededSignatureHandler (generator a) (publicKey a) (.inr payload)
        ((messages a, cache a), privateScalars a, hashScalars a) <;> rfl

end Word

end Cslib.Crypto.Schnorr
