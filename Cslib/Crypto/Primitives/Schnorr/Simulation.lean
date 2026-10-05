/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Oracle
public import Cslib.Crypto.RandomOracle.Measure
public import Cslib.Foundations.MeasureTheory.Option
public import Cslib.Foundations.Control.Monad.IsMonadHom.Transformers

/-!
# Simulating Schnorr signing queries

The simulator chooses a challenge and response, then programs their commitment into the
random oracle. It aborts on an existing cache entry. The successful signature and final cache
have exactly the honest signer's joint measure restricted to fresh commitments.

This is the signing step of VCVio's Fiat--Shamir reduction, expressed using `StateT` and
`OptionT` directly. It does not give the simulator the secret key.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

section Simulation

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq M] [DecidableEq G]

/-- Program the simulated transcript if its commitment is fresh. -/
def simulateSign.finish (message : M) (cache : List ((M × G) × F)) (transcript : G × F × F) :
    Option ((G × F) × List ((M × G) × F)) :=
  if cache.lookup (message, transcript.1) = none then
    some ((transcript.1, transcript.2.2), ((message, transcript.1), transcript.2.1) :: cache)
  else none

/-- Program a fresh hash input with a simulated transcript, aborting if it was already queried. -/
def simulateSign {m : Type → Type*} [Monad m] (sample : m F) (g pk : G) (message : M) :
    StateT (List ((M × G) × F)) (OptionT m) (G × F) := fun cache => OptionT.mk do
  let transcript ← simulateTranscript sample g pk
  pure (simulateSign.finish message cache transcript)

variable {P : PFunctor.{0, 0}}

/-- A successful simulated signature is accepted by the same cache, and adds exactly one entry. -/
theorem simulateSign_sound (sample : P.FreeM F) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) {signature : G × F} {cache' : List ((M × G) × F)}
    (h : MonadAttach.CanReturn ((simulateSign sample g pk message).run cache).run
      (some (signature, cache'))) :
    ∃ challenge, cache.lookup (message, signature.1) = none ∧
      cache' = ((message, signature.1), challenge) :: cache ∧
      Accepts g pk signature.1 challenge signature.2 := by
  simp only [simulateSign, simulateSign.finish, simulateTranscript, StateT.run, OptionT.run,
    OptionT.mk, bind_assoc, pure_bind] at h
  obtain ⟨challenge, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  obtain ⟨response, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  simp only [FreeM.canReturn_pure] at h
  split at h
  next hfresh =>
    cases h
    exact ⟨challenge, hfresh, rfl, accepts_simulate g pk challenge response⟩
  next => cases h

/-- Simulate adaptive signing requests using only the public key, with one shared cache and
the same signed-message log as the honest experiment. A programming collision aborts the run.
`hashSample` may use a separate effect so forking can select fresh hash queries specifically. -/
def simulatedSignatureHandler {m : Type → Type*} [Monad m]
    (ambient : (op : P.A) → m (P.B op)) (sample : m F)
    (hashSample : M × G → m F) (g pk : G) :
    (op : (signatureEffects P M G F).A) →
      StateT (List M × List ((M × G) × F)) (OptionT m)
        ((signatureEffects P M G F).B op)
  | .inl op => fun state => OptionT.mk do
      let answer ← ambient op
      pure (some (answer, state))
  | .inr (.inl input) => fun (messages, cache) => OptionT.mk do
      let (answer, cache') ← RandomOracle.query (hashSample input) input cache
      pure (some (answer, messages, cache'))
  | .inr (.inr message) => fun (messages, cache) => do
      let (signature, cache') ← (simulateSign sample g pk message).run cache
      pure (signature, message :: messages, cache')

/-- Return an accepted forgery on a fresh message, using a supplied public key. Verification
queries the same cache, including entries programmed by the signing simulator. -/
def simulatedForgery {m : Type → Type*} [Monad m] (ambient : (op : P.A) → m (P.B op))
    (sample : m F) (hashSample : M × G → m F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    OptionT m (M × G × F) := do
  let ((message, signature), messages, cache) ←
    ((adversary pk).liftM (simulatedSignatureHandler ambient sample hashSample g pk)).run ([], [])
  let (valid, _) ← monadLift
    ((verify (fun input => RandomOracle.query (hashSample input) input)
      g pk message signature).run cache)
  if valid && decide (message ∉ messages) then pure (message, signature) else failure

/-- The simulated EUF-CMA game treats programming collisions and rejected forgeries as losses. -/
def simulatedUnforgeabilityExperiment (sample : P.FreeM F) (hashSample : M × G → P.FreeM F)
    (g pk : G) (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) : P.FreeM Bool :=
  Option.isSome <$> (simulatedForgery FreeM.lift sample hashSample g pk adversary).run

section Measures

variable [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op))
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [Countable M]
  [MeasurableSpace (List ((M × G) × F))] [DiscreteMeasurableSpace (List ((M × G) × F))]

/-- The simulator and the honest signer agree on the whole signature/cache pair until a
commitment collides with an existing hash input. The failed branch is explicitly `none`. -/
theorem denote_simulateSign (sample : P.FreeM F) (g : G) (secret : F) (message : M)
    (cache : List ((M × G) × F)) (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ ((simulateSign sample g (secret • g) message).run cache).run =
      (FreeM.denote μ ((sign (monadLift sample) (RandomOracle.query sample)
        g secret message).run cache)).map (fun out =>
          if cache.lookup (message, out.1.1) = none then some out else none) := by
  let finish : G × F × F → Option ((G × F) × List ((M × G) × F)) := fun t =>
    if cache.lookup (message, t.1) = none then
      some ((t.1, t.2.2), ((message, t.1), t.2.1) :: cache) else none
  change FreeM.denote μ ((simulateTranscript sample g (secret • g)) >>= fun t =>
    pure (finish t)) = _
  change FreeM.denote μ ((simulateTranscript sample g (secret • g)).bind (pure ∘ finish)) = _
  rw [FreeM.bind_pure_comp, FreeM.denote_map _ _ _ Measurable.of_discrete,
    ← denote_realTranscript_eq_simulateTranscript μ sample g secret hsample]
  rw [← FreeM.denote_map _ _ _ Measurable.of_discrete,
    ← FreeM.denote_map _ _ _ Measurable.of_discrete]
  simp only [FreeM.map_eq_map, map_eq_pure_bind, realTranscript, sign,
    StateT.run_bind, StateT.run_pure,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    FreeM.denote_bind_of_discrete, FreeM.denote_pure]
  apply congrArg (Measure.bind (FreeM.denote μ sample))
  funext nonce
  by_cases hx : cache.lookup (message, nonce • g) = none
  · simp only [RandomOracle.query, StateT.run, hx, finish, ↓reduceIte,
      FreeM.denote_bind_of_discrete, FreeM.denote_pure,
      Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable,
      Measure.dirac_bind Measurable.of_discrete]
  · simp only [finish, hx, ↓reduceIte]
    rw [Measure.bind_const, Measure.bind_const]
    have hquery : FreeM.denote μ ((RandomOracle.query sample (message, nonce • g)).run cache)
        Set.univ = 1 := by
      obtain ⟨challenge, hchallenge⟩ := Option.ne_none_iff_exists'.mp hx
      simp [RandomOracle.query, StateT.run, hchallenge]
    rw [hquery, one_smul]
    rw [hsample, measure_univ, one_smul]

/-- The simulator aborts exactly when a uniform commitment hits this message's cache entries. -/
theorem denote_simulateSign_none (sample : P.FreeM F) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ ((simulateSign sample g pk message).run cache).run {none} =
      uniformOn Set.univ {commitment : G | (cache.lookup (message, commitment)).isSome} := by
  let : Finite G := Finite.of_surjective _ hg.surjective
  let finish : G × F × F → Option ((G × F) × List ((M × G) × F)) := fun t =>
    if cache.lookup (message, t.1) = none then
      some ((t.1, t.2.2), ((message, t.1), t.2.1) :: cache) else none
  change FreeM.denote μ ((simulateTranscript sample g pk).bind (pure ∘ finish)) {none} = _
  rw [FreeM.bind_pure_comp, FreeM.denote_map _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  rw [← denote_simulateTranscript_map_fst μ sample g hg pk hsample,
    Measure.map_apply measurable_fst MeasurableSet.of_discrete]
  congr 1
  ext t
  change finish t = none ↔ (cache.lookup (message, t.1)).isSome = true
  cases hx : cache.lookup (message, t.1) <;> simp [finish, hx]

/-- Each signing query loses at most one scalar-space fraction per existing cache entry. -/
theorem denote_simulateSign_none_le [MeasurableSpace M] [MeasurableSingletonClass M]
    (sample : P.FreeM F) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    FreeM.denote μ ((simulateSign sample g pk message).run cache).run {none} ≤
      cache.length / (Nat.card F : ℝ≥0∞) := by
  let : Finite G := Finite.of_surjective _ hg.surjective
  let := Fintype.ofFinite G
  have hcard : Nat.card G = Nat.card F := (Nat.card_congr (Equiv.ofBijective _ hg)).symm
  rw [denote_simulateSign_none μ sample g pk message cache hg hsample, div_eq_mul_inv]
  let ν := (uniformOn (Set.univ : Set G)).map (Prod.mk message)
  have hpoint (input : M × G) : ν {input} ≤ (Nat.card F : ℝ≥0∞)⁻¹ := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    calc
      _ ≤ uniformOn Set.univ {input.2} := by
        apply measure_mono
        intro commitment h
        exact congrArg Prod.snd h
      _ = _ := by simp [uniformOn_univ, ← Nat.card_eq_fintype_card, hcard]
  have h := RandomOracle.measure_lookup_isSome_le ν cache (Nat.card F : ℝ≥0∞)⁻¹ hpoint
  dsimp only [ν] at h
  rw [Measure.map_apply (show Measurable (Prod.mk message : G → M × G) by fun_prop)
    MeasurableSet.of_discrete] at h
  exact h

/-- Successful simulation gives exactly the honest joint measure restricted to fresh inputs. -/
theorem denote_simulateSign_some (sample : P.FreeM F) (g : G) (secret : F) (message : M)
    (cache : List ((M × G) × F)) (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (s : Set ((G × F) × List ((M × G) × F))) :
    FreeM.denote μ ((simulateSign sample g (secret • g) message).run cache).run (some '' s) =
      FreeM.denote μ ((sign (monadLift sample) (RandomOracle.query sample)
        g secret message).run cache) (s ∩ {out | cache.lookup (message, out.1.1) = none}) := by
  rw [denote_simulateSign μ sample g secret message cache hsample,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext out
  change (if cache.lookup (message, out.1.1) = none then some out else none) ∈ some '' s ↔
    out ∈ s ∧ cache.lookup (message, out.1.1) = none
  by_cases h : cache.lookup (message, out.1.1) = none <;> simp [h]

/-- Any event of honest signing is bounded by its simulated event plus the programming error.
Events may inspect both the signature and the resulting cache. -/
theorem denote_sign_le_simulateSign_add [MeasurableSpace M] [MeasurableSingletonClass M]
    (sample : P.FreeM F) (g : G) (secret : F) (message : M) (cache : List ((M × G) × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (s : Set ((G × F) × List ((M × G) × F))) :
    FreeM.denote μ ((sign (monadLift sample) (RandomOracle.query sample)
      g secret message).run cache) s ≤
    FreeM.denote μ ((simulateSign sample g (secret • g) message).run cache).run (some '' s) +
      cache.length / (Nat.card F : ℝ≥0∞) := by
  have hbad := denote_simulateSign_none_le μ sample g (secret • g) message cache hg hsample
  rw [denote_simulateSign μ sample g secret message cache hsample,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)] at hbad
  rw [denote_simulateSign_some μ sample g secret message cache hsample]
  calc
    _ ≤ FreeM.denote μ ((sign (monadLift sample) (RandomOracle.query sample)
        g secret message).run cache)
        ((s ∩ {out | cache.lookup (message, out.1.1) = none}) ∪
          {out | cache.lookup (message, out.1.1) ≠ none}) := by
      apply measure_mono
      intro out hout
      by_cases h : cache.lookup (message, out.1.1) = none
      · exact Or.inl ⟨hout, h⟩
      · exact Or.inr h
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (by
      convert hbad using 1
      congr 1
      ext out
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      split <;> simp_all [-List.lookup_eq_none_iff]))

end Measures

end Simulation

section Inlining

open PFunctor

variable {P : PFunctor.{0, 0}} {F G M : Type}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
  {m n : Type → Type*} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  {f : ∀ {α}, m α → n α} (hf : IsMonadHom m n f)

include hf

/-- Sampling implementations commute with simulated signing, including its abort. -/
theorem map_simulateSign (sample : m F) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) :
    f ((simulateSign sample g pk message).run cache).run =
      ((simulateSign (f sample) g pk message).run cache).run := by
  simp only [simulateSign, simulateTranscript, StateT.run, OptionT.run, OptionT.mk,
    bind_assoc, pure_bind, hf.map_bind, hf.map_pure]

/-- Inlining each underlying effect commutes with the combined signing and hash handler. -/
theorem map_simulatedSignatureHandler
    (ambient : (op : P.A) → m (P.B op)) (sample : m F)
    (hashSample : M × G → m F) (g pk : G)
    (op : (signatureEffects P M G F).A) (state : List M × List ((M × G) × F)) :
    f ((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run =
      ((simulatedSignatureHandler (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk op).run state).run := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl op =>
    simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
      hf.map_bind, hf.map_pure]
  | inr op =>
    cases op with
    | inl input =>
      simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        hf.map_bind, hf.map_pure]
      rw [RandomOracle.map_query hf]
    | inr message =>
      dsimp only [simulatedSignatureHandler, StateT.run, OptionT.run, Bind.bind,
        OptionT.instMonad, OptionT.bind, OptionT.mk]
      rw [hf.map_bind]
      have h := map_simulateSign hf sample g pk message cache
      dsimp only [StateT.run, OptionT.run] at h
      rw [h]
      congr 1
      funext out
      cases out <;> exact hf.map_pure _

/-- An implementation can replace fresh hash operations after the simulator has been inlined.
The equality includes the signing log, shared cache, aborts, and final verification. -/
theorem map_simulatedForgery
    (ambient : (op : P.A) → m (P.B op)) (sample : m F)
    (hashSample : M × G → m F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    f (simulatedForgery ambient sample hashSample g pk adversary).run =
      (simulatedForgery (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk adversary).run := by
  have hhandler : (fun op state => OptionT.mk
      (f ((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run)) =
      simulatedSignatureHandler (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk := by
    funext op state
    exact map_simulatedSignatureHandler hf ambient sample hashSample g pk op state
  have hstate := congrFun ((hf.optionT.stateT
    (List M × List ((M × G) × F))).map_pfunctorFreeMLiftM
      (simulatedSignatureHandler ambient sample hashSample g pk) (adversary pk)) ([], [])
  rw [hhandler] at hstate
  dsimp only [OptionT.mk, OptionT.run, StateT.run] at hstate
  dsimp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk, StateT.run]
  rw [hf.map_bind, hstate]
  congr 1
  funext out
  cases out with
  | none => exact hf.map_pure _
  | some out =>
    rcases out with ⟨⟨message, signature⟩, messages, cache⟩
    simp only [verify, monadLift, MonadLift.monadLift,
      OptionT.lift, OptionT.mk, bind_assoc, pure_bind, hf.map_bind]
    dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
    simp only [hf.map_bind, hf.map_pure, bind_assoc, pure_bind]
    rw [RandomOracle.map_query hf]
    congr 1
    funext out
    split <;> exact hf.map_pure _

end Inlining

end Cslib.Crypto.Schnorr
