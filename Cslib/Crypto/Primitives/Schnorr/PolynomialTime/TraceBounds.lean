/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Trace

/-! # Size of the fresh-hash transcript -/

public section

namespace Cslib.Crypto.Schnorr

open Turing.MultiTapeTM

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A successful call either preserves the hash tape or consumes exactly its head and inserts
the corresponding fresh hash. The new message fits in the canonical request buffer. -/
theorem seededSignatureWordHandler_hashTape
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    {out : Word × (List Word × List ((Word × G) × F)) × (List F × List F)}
    (h : seededSignatureWordHandler element scalar g pk word state = some out) :
    out.2.2.2 = state.2.2 ∨ ∃ input answer, input.1.length ≤ word.length ∧
      out.2.1.2 = (input, answer) :: state.1.2 ∧
        state.2.2 = answer :: out.2.2.2 := by
  let : BEq Word := instBEqOfDecidableEq
  rcases state with ⟨⟨messages, cache⟩, privateScalars, hashScalars⟩
  cases word with
  | nil => cases h
  | cons bit payload =>
    cases bit with
    | false =>
      change ((do
        let input ← ((Computability.encodingList Bool).bitPair element).decodeChecked payload
        let result ← seededSignatureHandler g pk (.inl input)
          ((messages, cache), privateScalars, hashScalars)
        pure (scalar result.1, result.2)) : Option _) = some out at h
      obtain ⟨input, hinput, h⟩ := Option.bind_eq_some_iff.mp h
      have hcode := (Computability.Encoding.decodeChecked_eq_some _ _ _).mp hinput
      have hmessage : input.1.length ≤ (false :: payload).length := by
        have hlength := congrArg List.length hcode
        change (pairEncoding wordEncoding element.toEmbedding input).length = payload.length
          at hlength
        simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply] at hlength
        simp only [List.length_cons]
        omega
      obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
      have hout' : (scalar result.1, result.2) = out := Option.some.inj hout
      subst out
      cases hlookup : cache.lookup input with
      | some answer =>
        rw [seededSignatureHandler_hash_hit _ _ _ _ _ _ _ answer hlookup] at hresult
        cases hresult
        exact Or.inl rfl
      | none =>
        cases hashScalars with
        | nil =>
          rw [seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup] at hresult
          cases hresult
        | cons answer rest =>
          rw [seededSignatureHandler_hash_miss _ _ _ _ _ _ _ answer hlookup] at hresult
          cases hresult
          exact Or.inr ⟨input, answer, hmessage, rfl, rfl⟩
    | true =>
      obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
      have hout' : (pairEncoding element.toEmbedding scalar result.1, result.2) = out :=
        Option.some.inj hout
      subst out
      cases privateScalars with
      | nil =>
        rw [seededSignatureHandler_sign_exhausted _ _ _ _ _ _ _ (by simp)] at hresult
        cases hresult
      | cons challenge rest =>
        cases rest with
        | nil =>
          rw [seededSignatureHandler_sign_exhausted _ _ _ _ _ _ _ (by simp)] at hresult
          cases hresult
        | cons response rest =>
          rw [seededSignatureHandler_sign] at hresult
          simp only [simulateSign.finish] at hresult
          split at hresult
          · cases Option.some.inj hresult
            exact Or.inl rfl
          · cases hresult

/-- Advancing the hash cursor identifies the newly inserted cache entry and consumed answer. -/
theorem seededSignatureWordHandler_fresh
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    {out : Word × (List Word × List ((Word × G) × F)) × (List F × List F)}
    (h : seededSignatureWordHandler element scalar g pk word state = some out)
    (hchanged : state.2.2.length ≠ out.2.2.2.length) :
    ∃ input answer, input.1.length ≤ word.length ∧
      out.2.1.2 = (input, answer) :: state.1.2 ∧ state.2.2 = answer :: out.2.2.2 :=
  (seededSignatureWordHandler_hashTape element scalar g pk word state h).resolve_left
    (fun heq => hchanged (congrArg List.length heq.symm))

/-- Recorded answers are exactly the consumed hash-tape prefix, in order. -/
theorem traceSeededSignatureWordHandler_answers
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    (events : List ((Word × G) × F))
    {out : Word × ((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)}
    (h : traceSeededCall (seededSignatureWordHandler element scalar g pk word)
      (state, events) = some out) :
    out.2.2.map Prod.snd ++ out.2.1.2.2 = events.map Prod.snd ++ state.2.2 := by
  obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hout
  rcases seededSignatureWordHandler_hashTape element scalar g pk word state hresult with
    heq | ⟨input, answer, _, hcache, htape⟩
  · simp [heq]
  · simp [htape, hcache, List.append_assoc]

/-- A successful call appends at most one bounded event. Existing transcript length does not
enter the per-call growth bound; copying the retained log is charged by the interpreter. -/
theorem traceSeededSignatureWordHandler_size
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    (events : List ((Word × G) × F))
    {out : Word × ((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)}
    (h : traceSeededCall (seededSignatureWordHandler element scalar g pk word)
      (state, events) = some out)
    (groupBound scalarBound : ℕ)
    (hg : ∀ value, (element.encode value).length ≤ groupBound)
    (hf : ∀ value, (scalar value).length ≤ scalarBound) :
    out.1.length ≤ 2 * groupBound + scalarBound + 1 ∧
      (seededSignatureStateEncoding element.toEmbedding scalar wordEncoding out.2.1).length ≤
        (seededSignatureStateEncoding element.toEmbedding scalar wordEncoding state).length +
          (24 * word.length + 8 * groupBound + 4 * scalarBound + 18) ∧
      (listEncoding (pairEncoding (pairEncoding wordEncoding element.toEmbedding) scalar)
        out.2.2).length ≤
      (listEncoding (pairEncoding (pairEncoding wordEncoding element.toEmbedding) scalar)
        events).length + 8 * word.length + 4 * groupBound + 2 * scalarBound + 7 := by
  obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hout
  obtain ⟨hreply, hstate⟩ :=
    seededSignatureWordHandler_size element scalar g pk word state hresult
      groupBound scalarBound hg hf
  refine ⟨hreply, hstate, ?_⟩
  dsimp only
  split
  · omega
  next hchanged =>
    obtain ⟨input, answer, hmessage, hcache, _⟩ :=
      seededSignatureWordHandler_fresh element scalar g pk word state hresult hchanged
    rw [hcache]
    have := hg input.2
    have := hf answer
    simp only [List.take_succ_cons, List.take_zero, listEncoding_append, List.length_append,
      listEncoding_cons, listEncoding_nil, length_pairEncoding, List.length_nil,
      wordEncoding, Function.Embedding.refl_apply, Computability.Encoding.toEmbedding_apply]
    omega

end Cslib.Crypto.Schnorr
