/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Fork
public import Cslib.Foundations.Data.PFunctor.Free.Trace.Handler

/-! # Every successful simulated forgery has a fork point -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MonadAttach

variable {P : PFunctor.{0, 0}} {F G M : Type} [DecidableEq G] [DecidableEq M]

private abbrev HashEffects (P : PFunctor.{0, 0}) (M G F : Type) :=
  P + PFunctor.mk (M × G) (fun _ => F)

/-- Every cache entry comes from a signed message or a recorded fresh hash query. -/
private def cacheRecorded (events : List (Sigma (HashEffects P M G F).B))
    (state : List M × List ((M × G) × F)) : Prop :=
  ∀ input challenge, state.2.lookup input = some challenge →
    input.1 ∈ state.1 ∨ ⟨Sum.inr input, challenge⟩ ∈ events

private theorem cacheRecorded_append (before after : List (Sigma (HashEffects P M G F).B))
    (state : List M × List ((M × G) × F)) (h : cacheRecorded before state) :
    cacheRecorded (before ++ after) state := by
  intro input challenge hlookup
  exact (h input challenge hlookup).imp_right (List.mem_append_left _)

variable [Field F] [AddCommGroup G] [Module F G]

private theorem cacheRecorded_handler
    (ambient : (op : P.A) → (HashEffects P M G F).FreeM (P.B op))
    (sample : (HashEffects P M G F).FreeM F) (g pk : G)
    (op : (signatureEffects P M G F).A) (before : List (Sigma (HashEffects P M G F).B))
    (state : List M × List ((M × G) × F))
    (answer : (signatureEffects P M G F).B op)
    (state' : List M × List ((M × G) × F)) (events : List (Sigma (HashEffects P M G F).B))
    (hstate : cacheRecorded before state)
    (h : CanReturn (FreeM.trace ((simulatedSignatureHandler ambient sample
      (fun input => FreeM.lift (P := HashEffects P M G F) (.inr input)) g pk op).run state).run)
        (some (answer, state'), events)) : cacheRecorded (before ++ events) state' := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl op =>
    have hreturn := FreeM.canReturn_of_trace _ h
    obtain ⟨_, _, hreturn⟩ := (FreeM.canReturn_bind _ _ _).mp hreturn
    have heq : some (answer, state') = some (_, messages, cache) := hreturn
    cases heq
    exact cacheRecorded_append _ _ _ hstate
  | inr op =>
    cases op with
    | inl input =>
      cases hx : cache.lookup input with
      | some challenge =>
        simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
          RandomOracle.query, hx, pure_bind, FreeM.trace_pure, FreeM.canReturn_pure] at h
        cases h
        simpa using hstate
      | none =>
        simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
          RandomOracle.query, hx, bind_assoc, pure_bind] at h
        obtain ⟨challenge, first, rest, hfirst, hrest, hevents⟩ :=
          (FreeM.canReturn_trace_bind _ _ _).mp h
        have hfirst : first = [⟨Sum.inr input, challenge⟩] := by
          rw [FreeM.trace_lift] at hfirst
          symm
          simpa only [← FreeM.map_eq_map, FreeM.canReturn_map, FreeM.canReturn_lift,
            true_and, Prod.mk.injEq, exists_eq_left] using hfirst
        simp only [FreeM.trace_pure, FreeM.canReturn_pure, Prod.mk.injEq,
          Option.some.injEq] at hrest
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrest
        subst first
        simp only [List.append_nil] at hevents
        subst events
        intro key value hlookup
        by_cases heq : key = input
        · subst key
          have hv : value = answer := by simpa using hlookup.symm
          subst value
          exact Or.inr (by simp)
        · have hold : cache.lookup key = some value := by
            simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr heq] using hlookup
          exact (hstate key value hold).imp_right (List.mem_append_left _)
    | inr message =>
      have hreturn := FreeM.canReturn_of_trace _ h
      dsimp only [simulatedSignatureHandler, StateT.run, OptionT.run, Bind.bind,
        OptionT.instMonad, OptionT.bind, OptionT.mk] at hreturn
      obtain ⟨out, hout, hreturn⟩ := (FreeM.canReturn_bind _ _ _).mp hreturn
      cases out with
      | none => cases hreturn
      | some out =>
        rcases out with ⟨signature, cache'⟩
        have heq : some (answer, state') = some (signature, message :: messages, cache') := hreturn
        cases heq
        obtain ⟨challenge, _, rfl, _⟩ := simulateSign_sound sample g pk message cache hout
        intro input value hlookup
        by_cases heq : input = (message, answer.1)
        · subst input
          exact Or.inl (by simp)
        · have hold : cache.lookup input = some value := by
            simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr heq] using hlookup
          exact (hstate input value hold).imp (List.mem_cons_of_mem _)
            (List.mem_append_left _)

/-- Every accepted fresh forgery uses an answer from a recorded hash operation. The final
verifier query is included, so the adversary need not have queried this input itself. -/
theorem exists_hash_of_simulatedForgery
    (ambient : (op : P.A) → (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (P.B op))
    (sample : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    {message : M} {commitment : G} {response : F}
    {events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)}
    (h : CanReturn (FreeM.trace (simulatedForgery ambient sample
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run) (some (message, commitment, response), events)) :
    ∃ challenge, Accepts g pk commitment challenge response ∧
      ⟨Sum.inr (message, commitment), challenge⟩ ∈ events := by
  let hashSample := fun input => FreeM.lift (P := HashEffects P M G F) (.inr input)
  let handler := simulatedSignatureHandler ambient sample hashSample g pk
  dsimp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.instMonad,
    OptionT.bind, OptionT.mk] at h
  obtain ⟨out, before, after, hbefore, hafter, hevents⟩ :=
    (FreeM.canReturn_trace_bind _ _ _).mp h
  cases out with
  | none => cases hafter
  | some out =>
    rcases out with ⟨⟨m, R, z⟩, messages, cache⟩
    have hstate : cacheRecorded before (messages, cache) := by
      simpa using FreeM.trace_liftM_stateT_invariant handler cacheRecorded
        (cacheRecorded_handler ambient sample g pk) (adversary pk) [] ([], [])
        (by simp [cacheRecorded]) hbefore
    dsimp only at hafter
    simp only [verify, StateT.run_bind, StateT.run_pure, monadLift,
      MonadLift.monadLift, OptionT.lift, OptionT.mk,
      FreeM.bind_eq_bind, bind_assoc, pure_bind] at hafter
    obtain ⟨⟨challenge, cache'⟩, queried, last, hquery, hlast, hafter⟩ :=
      (FreeM.canReturn_trace_bind _ _ _).mp hafter
    dsimp only at hlast
    split at hlast
    next hvalid =>
      have hlast : (some (message, commitment, response), last) = (some (m, R, z), []) := hlast
      cases hlast
      have hvalid : Accepts g pk commitment challenge response ∧ message ∉ messages := by
        simpa using hvalid
      have hquery' : CanReturn (FreeM.trace ((handler (.inr (.inl
          (message, commitment)))).run (messages, cache)).run)
          (some (challenge, messages, cache'), queried) := by
        change CanReturn (FreeM.trace ((RandomOracle.query (hashSample (message, commitment))
          (message, commitment) cache) >>= fun out => pure (some (out.1, messages, out.2)))) _
        exact (FreeM.canReturn_trace_bind _ _ _).mpr
          ⟨(challenge, cache'), queried, [], hquery, rfl, (List.append_nil _).symm⟩
      have hrecord := cacheRecorded_handler ambient sample g pk _ _ _ _ _ _ hstate hquery'
      have hlookup := RandomOracle.lookup_of_canReturn _ _ _ (FreeM.canReturn_of_trace _ hquery)
      refine ⟨challenge, hvalid.1, ?_⟩
      have hmem := (hrecord (message, commitment) challenge hlookup).resolve_left hvalid.2
      dsimp only at hevents hafter
      simpa only [hevents, hafter, List.append_nil] using hmem
    next => cases hlast

/-- The selector succeeds exactly when the trace contains an accepting hash answer. -/
theorem forkPoint_isSome_iff (g pk : G) (message : M) (commitment : G) (response : F)
    (events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)) :
    (forkPoint g pk (some (message, commitment, response)) events).isSome ↔
      ∃ challenge, Accepts g pk commitment challenge response ∧
        ⟨Sum.inr (message, commitment), challenge⟩ ∈ events := by
  simp only [forkPoint, findForkPoint, List.findIdx?_isSome, List.any_eq_true, decide_eq_true_eq,
    List.mem_filterMap]
  constructor
  · rintro ⟨⟨input, challenge⟩, ⟨⟨op, answer⟩, hmem, heq⟩, hinput, haccepts⟩
    cases op with
    | inl op => cases heq
    | inr input' =>
      cases heq
      dsimp only at hinput
      subst input
      exact ⟨challenge, haccepts, hmem⟩
  · rintro ⟨challenge, haccepts, hmem⟩
    exact ⟨((message, commitment), challenge),
      ⟨⟨Sum.inr (message, commitment), challenge⟩, hmem, rfl⟩, rfl, haccepts⟩

/-- The selector counts only hash operations, rather than ambient randomness or signing. -/
theorem forkPoint_lt (g pk : G) (candidate : Option (M × G × F))
    (events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)) {n : ℕ}
    (h : forkPoint g pk candidate events = some n) :
    n < events.countP (fun event => event.1.isRight) := by
  cases candidate with
  | none => cases h
  | some candidate =>
    obtain ⟨message, commitment, response⟩ := candidate
    have hn := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
    rw [List.length_filterMap_eq_countP] at hn
    convert hn using 2
    funext ⟨op, answer⟩
    cases op <;> rfl

/-- Selecting the operation after a known prefix identifies the forgery's input and its
accepting challenge. This applies to each of the two traces returned by a fork. -/
theorem findForkPoint_spec_of_prefix (g pk : G) (candidate : Option (M × G × F))
    (before events : List ((M × G) × F)) (input : M × G) (challenge : F)
    (hprefix : before ++ [(input, challenge)] <+: events)
    (hpoint : findForkPoint g pk candidate events = some before.length) :
    ∃ response, candidate = some (input.1, input.2, response) ∧
      Accepts g pk input.2 challenge response := by
  cases candidate with
  | none => cases hpoint
  | some candidate =>
    rcases candidate with ⟨message, commitment, response⟩
    obtain ⟨after, rfl⟩ := hprefix
    simp only [findForkPoint, List.append_assoc, List.singleton_append] at hpoint
    obtain ⟨_, hgood, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hpoint
    simp only [List.getElem_append_right (by rfl), Nat.sub_self, List.getElem_cons_zero,
      decide_eq_true_eq] at hgood
    obtain ⟨hinput, haccepts⟩ := hgood
    cases hinput
    exact ⟨response, rfl, haccepts⟩

/-- The selector counts only hashes in an interleaved transcript; its selected occurrence
identifies the candidate and accepting challenge. -/
theorem forkPoint_spec_of_prefix (g pk : G) (candidate : Option (M × G × F))
    (before events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B))
    (input : M × G) (challenge : F)
    (hprefix : before ++ [⟨Sum.inr input, challenge⟩] <+: events)
    (hpoint : forkPoint g pk candidate events =
      some (before.countP (fun event => event.1.isRight))) :
    ∃ response, candidate = some (input.1, input.2, response) ∧
      Accepts g pk input.2 challenge response := by
  let hash : Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B → Option ((M × G) × F)
    | ⟨.inl _, _⟩ => none
    | ⟨.inr input, challenge⟩ => some (input, challenge)
  have hlength : (before.filterMap hash).length = before.countP (fun event => event.1.isRight) :=
    by
    rw [List.length_filterMap_eq_countP]
    congr 1
    funext ⟨op, answer⟩
    cases op <;> rfl
  apply findForkPoint_spec_of_prefix g pk candidate (before.filterMap hash)
    (events.filterMap hash) input challenge
  · simpa [hash] using hprefix.filterMap hash
  · rw [hlength]
    unfold forkPoint at hpoint
    convert hpoint using 2
    congr 1

/-- With only hash effects visible, a semantic fork whose two selectors agree yields two
accepting transcripts at the same input. Private randomness is already fixed in `program`. -/
theorem accepts_of_findForkPoint_eq (g pk : G)
    (program : (PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)))
    {first second : Option (M × G × F)}
    {events events' : List (Sigma (PFunctor.mk (M × G) (fun _ => F)).B)}
    {input : M × G} {challenge challenge' : F}
    (h : CanReturn (FreeM.fork (fun _ => true)
      (fun out => findForkPoint g pk out.1 (out.2.map (fun event => (event.1, event.2))))
      (FreeM.trace program))
      ((first, events), some ⟨input, challenge, challenge', second, events'⟩))
    (hpoint : findForkPoint g pk second (events'.map (fun event => (event.1, event.2))) =
      findForkPoint g pk first (events.map (fun event => (event.1, event.2)))) :
    ∃ response response', first = some (input.1, input.2, response) ∧
      second = some (input.1, input.2, response') ∧
      Accepts g pk input.2 challenge response ∧ Accepts g pk input.2 challenge' response' := by
  obtain ⟨before, n, hchoose, hcount, _, hfirst, hsecond⟩ :=
    FreeM.fork_trace_prefix _ _ program h
  have hchoose : findForkPoint g pk first (events.map (fun event => (event.1, event.2))) =
      some (before.map (fun event => (event.1, event.2))).length := by
    simpa only [← hcount, List.countP_true, List.length_map] using hchoose
  obtain ⟨response, rfl, haccepts⟩ := findForkPoint_spec_of_prefix g pk first
    (before.map (fun event => (event.1, event.2))) _ input challenge
    (by simpa using hfirst.map (fun event => (event.1, event.2))) hchoose
  obtain ⟨response', rfl, haccepts'⟩ := findForkPoint_spec_of_prefix g pk second
    (before.map (fun event => (event.1, event.2))) _ input challenge'
    (by simpa using hsecond.map (fun event => (event.1, event.2))) (hpoint.trans hchoose)
  exact ⟨response, response', rfl, rfl, haccepts, haccepts'⟩

/-- If both continuations select the forked occurrence, their forgeries use that same input
and are accepted by the two recorded challenges. -/
theorem accepts_of_forkPoint_eq (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)))
    {first second : Option (M × G × F)}
    {events events' : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)}
    {input : M × G} {challenge challenge' : F}
    (h : CanReturn (FreeM.fork
      (fun op : (P + PFunctor.mk (M × G) (fun _ => F)).A => op.isRight)
      (fun out => forkPoint g pk out.1 out.2) (FreeM.trace program))
      ((first, events), some ⟨Sum.inr input, challenge, challenge', second, events'⟩))
    (hpoint : forkPoint g pk second events' = forkPoint g pk first events) :
    ∃ response response', first = some (input.1, input.2, response) ∧
      second = some (input.1, input.2, response') ∧
      Accepts g pk input.2 challenge response ∧ Accepts g pk input.2 challenge' response' := by
  obtain ⟨before, n, hchoose, hcount, _, hfirst, hsecond⟩ :=
    FreeM.fork_trace_prefix _ _ program h
  have hchoose : forkPoint g pk first events =
      some (before.countP (fun event => event.1.isRight)) := by
    simpa only [hcount] using hchoose
  obtain ⟨response, rfl, haccepts⟩ :=
    forkPoint_spec_of_prefix g pk first before events input challenge hfirst hchoose
  obtain ⟨response', rfl, haccepts'⟩ :=
    forkPoint_spec_of_prefix g pk second before events' input challenge' hsecond
      (hpoint.trans hchoose)
  exact ⟨response, response', rfl, rfl, haccepts, haccepts'⟩

/-- A successful fork in the general forking lemma passes the executable extraction checks. -/
theorem forkExtractor_finish_isSome [DecidableEq F] (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)))
    {out} {n : ℕ}
    (h : CanReturn (FreeM.fork
      (fun op : (P + PFunctor.mk (M × G) (fun _ => F)).A => op.isRight)
      (fun out => forkPoint g pk out.1 out.2) (FreeM.trace program)) out)
    (hsuccess : out ∈ FreeM.forkSuccess (fun out => forkPoint g pk out.1 out.2) n) :
    (forkExtractor.finish g pk out).isSome := by
  rcases out with ⟨⟨first, events⟩, event⟩
  obtain ⟨⟨op, challenge, challenge', second, events'⟩, hevent, hfirst, hsecond, hne⟩ := hsuccess
  cases hevent
  obtain ⟨_, _, _, _, hselect, _⟩ := FreeM.fork_trace_prefix _ _ program h
  cases op with
  | inl op => cases hselect
  | inr input =>
    obtain ⟨response, response', rfl, rfl, haccepts, haccepts'⟩ :=
      accepts_of_forkPoint_eq g pk program h (hsecond.trans hfirst.symm)
    simp [forkExtractor.finish, extract?, hne, haccepts, haccepts']

/-- A successful simulated forgery always selects a hash operation from its own execution. -/
theorem exists_forkPoint_of_simulatedForgery
    (ambient : (op : P.A) → (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (P.B op))
    (sample : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    {message : M} {commitment : G} {response : F}
    {events : List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)}
    (h : CanReturn (FreeM.trace (simulatedForgery ambient sample
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run) (some (message, commitment, response), events)) :
    ∃ n, forkPoint g pk (some (message, commitment, response)) events = some n ∧
      n < events.countP (fun event => event.1.isRight) := by
  have hsome := (forkPoint_isSome_iff g pk message commitment response events).mpr
    (exists_hash_of_simulatedForgery ambient sample g pk adversary h)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨n, hn, forkPoint_lt g pk _ events hn⟩

end Cslib.Crypto.Schnorr
