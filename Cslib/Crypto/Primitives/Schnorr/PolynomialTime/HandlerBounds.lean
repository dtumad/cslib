/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Handler

/-! # Size bounds for adaptive Schnorr simulation -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM

variable {F G M : Type}

@[simp] theorem length_seededSignatureStateEncoding
    (element : G ↪ Word) (scalar : F ↪ Word) (messageCode : M ↪ Word)
    (state : (List M × List ((M × G) × F)) × (List F × List F)) :
    (seededSignatureStateEncoding element scalar messageCode state).length =
      4 * (listEncoding messageCode state.1.1).length +
        2 * (listEncoding (pairEncoding (pairEncoding messageCode element) scalar)
          state.1.2).length +
        2 * (listEncoding scalar state.2.1).length +
          (listEncoding scalar state.2.2).length + 4 := by
  simp only [seededSignatureStateEncoding, length_pairEncoding]
  omega

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Each successful word call has a bounded reply and adds only one log entry and one cache
entry. Consumed tape entries cannot increase the retained state. The bound applies to arbitrary
prior caches, so adaptive execution needs no separate bound on the number of cached entries. -/
theorem seededSignatureWordHandler_size
    (element : Computability.Encoding G Bool) (scalar : F ↪ Word) (g pk : G)
    (word : Word) (state : (List Word × List ((Word × G) × F)) × (List F × List F))
    {out : Word × (List Word × List ((Word × G) × F)) × (List F × List F)}
    (h : seededSignatureWordHandler element scalar g pk word state = some out)
    (groupBound scalarBound : ℕ)
    (hg : ∀ value, (element.encode value).length ≤ groupBound)
    (hf : ∀ value, (scalar value).length ≤ scalarBound) :
    out.1.length ≤ 2 * groupBound + scalarBound + 1 ∧
      (seededSignatureStateEncoding element.toEmbedding scalar wordEncoding out.2).length ≤
        (seededSignatureStateEncoding element.toEmbedding scalar wordEncoding state).length +
          (24 * word.length + 8 * groupBound + 4 * scalarBound + 18) := by
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
      have hmessage : input.1.length ≤ payload.length := by
        have hlength := congrArg List.length hcode
        change (pairEncoding wordEncoding element.toEmbedding input).length = payload.length
          at hlength
        simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply] at hlength
        omega
      obtain ⟨result, hresult, hout⟩ := Option.bind_eq_some_iff.mp h
      have hout' : (scalar result.1, result.2) = out := Option.some.inj hout
      subst out
      cases hlookup : cache.lookup input with
      | some answer =>
        rw [seededSignatureHandler_hash_hit _ _ _ _ _ _ _ answer hlookup] at hresult
        cases hresult
        exact ⟨(hf answer).trans (by omega), Nat.le_add_right _ _⟩
      | none =>
        cases hashScalars with
        | nil =>
          rw [seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup] at hresult
          cases hresult
        | cons answer rest =>
          rw [seededSignatureHandler_hash_miss _ _ _ _ _ _ _ answer hlookup] at hresult
          cases hresult
          refine ⟨(hf answer).trans (by omega), ?_⟩
          have := hg input.2
          have := hf answer
          simp only [length_seededSignatureStateEncoding, listEncoding_cons, length_pairEncoding,
            wordEncoding, Function.Embedding.refl_apply, Computability.Encoding.toEmbedding_apply,
            List.length_cons]
          omega
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
          next =>
            have hout := Option.some.inj hresult
            cases hout
            have := hg (response • g - challenge • pk)
            have := hf challenge
            have := hf response
            simp only [length_pairEncoding, length_seededSignatureStateEncoding, listEncoding_cons,
              wordEncoding, Function.Embedding.refl_apply,
              Computability.Encoding.toEmbedding_apply, List.length_cons]
            constructor <;> omega
          next => cases hresult

end Cslib.Crypto.Schnorr
