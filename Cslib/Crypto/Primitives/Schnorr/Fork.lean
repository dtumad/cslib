/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Extraction
public import Cslib.Crypto.Primitives.Schnorr.Simulation
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Replay

/-!
# Forking a Schnorr signature adversary

Fresh hash queries are separate polynomial operations carrying their input. The first forgery
selects its accepting hash occurrence from the recorded execution. Forking at that occurrence
retains the inlined cache and adversary state and supplies a fresh hash answer.

`signatureExtractor` composes the signing simulator, final verification, adaptive forking,
and checked special-soundness extraction. Soundness is structural. `Schnorr.Fork.Measure`
proves its adaptive probability bound, and `Schnorr.Security` connects the closed reduction to
the honest EUF-CMA experiment, including the accumulated signing-simulation error.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M]

/-- Select the first accepting occurrence of the forgery's hash input, counting hash operations
only. Including the final verifier query makes a previously unqueried forgery eligible too. -/
def forkPoint (g pk : G) (candidate : Option (M × G × F))
    (events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)) : Option ℕ :=
  match candidate with
  | none => none
  | some (message, commitment, response) =>
    let hashes := events.filterMap fun
      | ⟨.inl _, _⟩ => none
      | ⟨.inr input, challenge⟩ => some (input, challenge)
    hashes.findIdx? fun event => decide (event.1 = (message, commitment) ∧
      Accepts g pk commitment event.2 response)

/-- Fork a candidate-producing program and extract only from two checked transcripts at
the same hash input. The program must inline its mutable state before calling this function. -/
def forkExtractor (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F))) :
    (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option F) :=
  finish <$> FreeM.fork (fun op => op.isRight)
    (fun out => forkPoint g pk out.1 out.2) (FreeM.trace program)
where
  /-- Check the two returned transcripts before special-soundness extraction. -/
  finish out :=
    match out.1.1, out.2 with
    | some (message, commitment, response),
        some ⟨.inr input, challenge, challenge', some (message', commitment', response'), _⟩ =>
      if (message, commitment) = input ∧ (message', commitment') = input then
        extract? g pk input.2 (challenge, response) (challenge', response')
      else none
    | _, _ => none

/-- The extractor can retain a transcript and restart the original program through a replay
handler. This identifies the full two-run computation, before taking any marginal measure. -/
theorem forkExtractor_eq_replay [DecidableEq (P + PFunctor.mk (M × G) (fun _ => F)).A]
    (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F))) :
    forkExtractor g pk program = forkExtractor.finish g pk <$>
      FreeM.forkWithReplay (fun op => op.isRight)
        (fun out => forkPoint g pk out.1 out.2) (FreeM.trace program) := by
  rw [forkExtractor, FreeM.fork_eq_forkWithReplay]

/-- Every successful adaptive extraction is a discrete logarithm of the supplied public key. -/
theorem forkExtractor_sound (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)))
    {secret : F} (h : MonadAttach.CanReturn (forkExtractor g pk program) (some secret)) :
    secret • g = pk := by
  unfold forkExtractor at h
  obtain ⟨⟨⟨candidate, events⟩, fork⟩, _, h⟩ := (FreeM.canReturn_map _ _ _).mp h
  unfold forkExtractor.finish at h
  dsimp only at h
  cases candidate with
  | none => cases h
  | some candidate =>
    rcases candidate with ⟨message, commitment, response⟩
    cases fork with
    | none => cases h
    | some event =>
      rcases event with ⟨op, challenge, challenge', second, events'⟩
      cases op with
      | inl op => cases h
      | inr input =>
        cases second with
        | none => cases h
        | some second =>
          rcases second with ⟨message', commitment', response'⟩
          dsimp only at h
          split at h
          · exact extract?_sound g pk input.2 _ _ h
          · cases h

/-- Simulate signing, retain each fresh hash input as a visible operation, and fork the
resulting adversary. All cache and signing-log state is inlined before the fork. -/
def signatureExtractor (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option F) :=
  let ambient := fun op : P.A =>
    FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
  forkExtractor g pk (simulatedForgery ambient (sample.liftM ambient)
    (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
    g pk adversary).run

theorem signatureExtractor_sound (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) {secret : F}
    (h : MonadAttach.CanReturn (signatureExtractor sample g pk adversary) (some secret)) :
    secret • g = pk :=
  forkExtractor_sound g pk _ h

end Cslib.Crypto.Schnorr
