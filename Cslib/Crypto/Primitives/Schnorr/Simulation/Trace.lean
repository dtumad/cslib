/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation.Seeded

/-! # Recording fresh hashes in the saved-tape simulator -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

variable {F G M α : Type}

/-- Record the fresh hash of a successful simulator call. Each signature-handler call and the
final verifier consume at most one hash answer, inserting it at the head of the shared cache.
Cache hits and signing calls leave the hash tape unchanged and add no event. -/
def traceSeededCall
    (call : StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option α) :
    StateT (((List M × List ((M × G) × F)) × (List F × List F)) ×
      List ((M × G) × F)) Option α := fun (state, events) => do
  let (answer, state') ← call state
  let events' := if state.2.2.length = state'.2.2.length then events
    else events ++ state'.1.2.take 1
  pure (answer, state', events')

/-- Recording does not change the answer, state, or rejection behavior. -/
theorem traceSeededCall_forget
    (call : StateT ((List M × List ((M × G) × F)) × (List F × List F)) Option α)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F)) :
    (traceSeededCall call (state, events)).map (fun out => (out.1, out.2.1)) = call state := by
  dsimp +instances only [traceSeededCall]
  cases call state <;> rfl

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]

/-- A cached hash is absent from the fresh-hash transcript, even with exhausted tapes. -/
theorem traceSeededCall_hash_hit (g pk : G) (input : M × G)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) (answer : F) (h : cache.lookup input = some answer) :
    traceSeededCall (seededSignatureHandler g pk (.inl input))
      (((messages, cache), privateScalars, hashScalars), events) =
        some (answer, ((messages, cache), privateScalars, hashScalars), events) := by
  simp [traceSeededCall, seededSignatureHandler_hash_hit _ _ _ _ _ _ _ _ h]

/-- A cache miss records exactly its input and consumed answer in chronological order. -/
theorem traceSeededCall_hash_miss (g pk : G) (input : M × G)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) (answer : F) (h : cache.lookup input = none) :
    traceSeededCall (seededSignatureHandler g pk (.inl input))
      (((messages, cache), privateScalars, answer :: hashScalars), events) =
        some (answer, ((messages, (input, answer) :: cache), privateScalars, hashScalars),
          events ++ [(input, answer)]) := by
  simp [traceSeededCall, seededSignatureHandler_hash_miss _ _ _ _ _ _ _ _ h]

/-- Programming a signature consumes private scalars and adds no fresh hash draw. -/
theorem traceSeededCall_sign (g pk : G) (message : M)
    (messages : List M) (cache : List ((M × G) × F)) (privateScalars hashScalars : List F)
    (events : List ((M × G) × F)) (challenge response : F) :
    traceSeededCall (seededSignatureHandler g pk (.inr message))
      (((messages, cache), challenge :: response :: privateScalars, hashScalars), events) =
        (simulateSign.finish message cache
          (response • g - challenge • pk, challenge, response)).map
            (fun out => (out.1, ((message :: messages, out.2), privateScalars, hashScalars),
              events)) := by
  simp only [traceSeededCall, seededSignatureHandler_sign]
  cases simulateSign.finish message cache
    (response • g - challenge • pk, challenge, response) <;> simp

/-- Recording the final checker is the same as recording its hash query and then checking the
candidate. A rejected forgery never supplies a successful transcript to the fork selector. -/
theorem traceSeededCall_check (g pk : G) (candidate : M × G × F)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F)) :
    traceSeededCall (checkSeededForgery g pk candidate) (state, events) = (do
      let (challenge, state') ← traceSeededCall
        (seededSignatureHandler g pk (.inl (candidate.1, candidate.2.1))) (state, events)
      if decide (Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2) &&
          decide (candidate.1 ∉ state.1.1) then
        some (candidate, state')
      else none) := by
  dsimp +instances only [traceSeededCall, checkSeededForgery]
  cases seededSignatureHandler g pk (.inl (candidate.1, candidate.2.1)) state with
  | none => rfl
  | some out =>
    rcases out with ⟨challenge, state'⟩
    dsimp +instances only [Bind.bind, Option.bind, Pure.pure]
    by_cases h : (decide (Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2) &&
      decide (candidate.1 ∉ state.1.1)) = true <;>
        simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- Every cache answer remains attributable to a signed message or a recorded fresh draw. -/
theorem traceSeededSignatureHandler_recorded (g pk : G) (op : (M × G) ⊕ M)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F))
    (hstate : ∀ input challenge, state.1.2.lookup input = some challenge →
      input.1 ∈ state.1.1 ∨ (input, challenge) ∈ events)
    {out : ((signatureEffects 0 M G F).B (.inr op)) ×
      (((List M × List ((M × G) × F)) × (List F × List F)) × List ((M × G) × F))}
    (h : traceSeededCall (seededSignatureHandler g pk op) (state, events) = some out) :
    ∀ input challenge, out.2.1.1.2.lookup input = some challenge →
      input.1 ∈ out.2.1.1.1 ∨ (input, challenge) ∈ out.2.2 := by
  rcases state with ⟨⟨messages, cache⟩, privateScalars, hashScalars⟩
  cases op with
  | inl key =>
    cases hlookup : cache.lookup key with
    | some answer =>
      rw [traceSeededCall_hash_hit _ _ _ _ _ _ _ _ _ hlookup] at h
      cases h
      exact hstate
    | none =>
      cases hashScalars with
      | nil =>
        simp [traceSeededCall, seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup] at h
      | cons answer rest =>
        rw [traceSeededCall_hash_miss _ _ _ _ _ _ _ _ _ hlookup] at h
        cases h
        intro input challenge hc
        by_cases heq : input = key
        · subst input
          have heq : challenge = answer := by simpa using hc.symm
          subst challenge
          exact Or.inr (by simp)
        · have hold : cache.lookup input = some challenge := by
            simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr heq] using hc
          exact (hstate input challenge hold).imp_right (List.mem_append_left _)
  | inr message =>
    cases privateScalars with
    | nil => cases h
    | cons challenge rest =>
      cases rest with
      | nil => cases h
      | cons response rest =>
        rw [traceSeededCall_sign] at h
        unfold simulateSign.finish at h
        split at h
        · cases h
          intro input value hc
          by_cases heq : input = (message, response • g - challenge • pk)
          · subst input
            exact Or.inl (by simp)
          · have hold : cache.lookup input = some value := by
              simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr heq] using hc
            exact (hstate input value hold).imp_left (List.mem_cons_of_mem _)
        · cases h

/-- Every accepted fresh forgery has an accepting answer in the recorded transcript. This
includes a hash first requested by the final verifier. -/
theorem traceSeededCall_check_recorded (g pk : G) (candidate : M × G × F)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F))
    (hstate : ∀ input challenge, state.1.2.lookup input = some challenge →
      input.1 ∈ state.1.1 ∨ (input, challenge) ∈ events)
    {out : (M × G × F) × (((List M × List ((M × G) × F)) ×
      (List F × List F)) × List ((M × G) × F))}
    (h : traceSeededCall (checkSeededForgery g pk candidate) (state, events) = some out) :
    out.1 = candidate ∧ ∃ challenge, Accepts g pk candidate.2.1 challenge candidate.2.2 ∧
      ((candidate.1, candidate.2.1), challenge) ∈ out.2.2 := by
  rw [traceSeededCall_check] at h
  obtain ⟨⟨challenge, state', events'⟩, hquery, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  next hvalid =>
    cases h
    have hvalid : Accepts (F := F) g pk candidate.2.1 challenge candidate.2.2 ∧
        candidate.1 ∉ state.1.1 := by simpa using hvalid
    have hrecord := traceSeededSignatureHandler_recorded g pk _ state events hstate hquery
    have hplain : seededSignatureHandler g pk (.inl (candidate.1, candidate.2.1)) state =
        some (challenge, state') := by
      rw [← traceSeededCall_forget
        (seededSignatureHandler g pk (.inl (candidate.1, candidate.2.1))) state events, hquery]
      rfl
    obtain ⟨hlog, _, hlookup⟩ := seededSignatureHandler_hash_spec g pk _ state hplain
    exact ⟨rfl, challenge, hvalid.1, (hrecord _ _ hlookup).resolve_left (hlog ▸ hvalid.2)⟩
  next => cases h

/-- Recorded hash answers followed by the remaining tape equal the original answer sequence. -/
theorem traceSeededCall_hash_answers (g pk : G) (input : M × G)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F))
    {out : F × (((List M × List ((M × G) × F)) × (List F × List F)) × List ((M × G) × F))}
    (h : traceSeededCall (seededSignatureHandler g pk (.inl input)) (state, events) = some out) :
    out.2.2.map Prod.snd ++ out.2.1.2.2 = events.map Prod.snd ++ state.2.2 := by
  rcases state with ⟨⟨messages, cache⟩, privateScalars, hashScalars⟩
  cases hlookup : cache.lookup input with
  | some answer =>
    rw [traceSeededCall_hash_hit _ _ _ _ _ _ _ _ _ hlookup] at h
    cases h
    rfl
  | none =>
    cases hashScalars with
    | nil =>
      simp [traceSeededCall, seededSignatureHandler_hash_exhausted _ _ _ _ _ _ hlookup] at h
    | cons answer rest =>
      rw [traceSeededCall_hash_miss _ _ _ _ _ _ _ _ _ hlookup] at h
      cases h
      simp [List.append_assoc]

/-- Successful final checking also preserves the exact consumed-prefix decomposition. -/
theorem traceSeededCall_check_answers (g pk : G) (candidate : M × G × F)
    (state : (List M × List ((M × G) × F)) × (List F × List F))
    (events : List ((M × G) × F))
    {out : (M × G × F) × (((List M × List ((M × G) × F)) ×
      (List F × List F)) × List ((M × G) × F))}
    (h : traceSeededCall (checkSeededForgery g pk candidate) (state, events) = some out) :
    out.2.2.map Prod.snd ++ out.2.1.2.2 = events.map Prod.snd ++ state.2.2 := by
  rw [traceSeededCall_check] at h
  obtain ⟨⟨challenge, state', events'⟩, hquery, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · cases h
    exact traceSeededCall_hash_answers g pk _ state events hquery
  · cases h

end Cslib.Crypto.Schnorr
