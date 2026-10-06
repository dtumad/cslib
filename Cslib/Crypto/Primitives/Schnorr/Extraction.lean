/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.HVZK
public import Cslib.Foundations.MeasureTheory.Collision
public import Cslib.Foundations.MeasureTheory.Option

/-!
# Extracting a witness from a Schnorr identification prover

The extractor runs the prover's commitment once, then two independent challenge/response
continuations from the same private state, and extracts a witness from two accepting transcripts
with distinct challenges. Every extracted value is a discrete logarithm of the public key
(`extractor_sound`), in every lawful monad with possible outputs. Under a measure semantics with a
uniform sampler of challenges, a prover accepted with probability `ε` yields extraction
probability at least `ε² - ε / |F|` (`le_sem_extractor`).
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {F G State : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

section Programs

variable {m : Type → Type*} [Monad m]

/-- Challenge a saved prover state and retain both the challenge and its response. -/
def interaction (sample : m F) (response : F → m F) : m (F × F) := do
  let challenge ← sample
  let answer ← response challenge
  pure (challenge, answer)

/-- The interactive verification experiment, before applying Fiat–Shamir. -/
def identificationExperiment (sample : m F) (g pk : G) (commit : m (G × State))
    (response : State → F → m F) : m Bool := do
  let (commitment, state) ← commit
  let (challenge, answer) ← interaction sample (response state)
  pure (decide (Accepts g pk commitment challenge answer))

/-- Check two transcripts before extracting a witness from them. -/
def extract? (g pk commitment : G) (first second : F × F) : Option F :=
  if first.1 ≠ second.1 ∧ Accepts g pk commitment first.1 first.2 ∧
      Accepts g pk commitment second.1 second.2 then
    some (extract first.1 first.2 second.1 second.2)
  else none

/-- Two continuations share the original commitment and private state; the commitment runs once. -/
def extractor (sample : m F) (g pk : G) (commit : m (G × State))
    (response : State → F → m F) : m (Option F) := do
  let (commitment, state) ← commit
  let first ← interaction sample (response state)
  let second ← interaction sample (response state)
  pure (extract? g pk commitment first second)

end Programs

/-- A successful extraction returns a discrete logarithm, rather than an unchecked candidate. -/
theorem extract?_sound (g pk commitment : G) (first second : F × F) {secret : F}
    (h : extract? g pk commitment first second = some secret) : secret • g = pk := by
  unfold extract? at h
  split at h
  next hgood =>
    cases h
    exact extract_smul g pk commitment hgood.1 hgood.2.1 hgood.2.2
  next => cases h

/-- Every value the extractor can return is a discrete logarithm of the public key. -/
theorem extractor_sound {m : Type → Type*} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] (sample : m F) (g pk : G) (commit : m (G × State))
    (response : State → F → m F) {secret : F}
    (h : MonadAttach.CanReturn (extractor sample g pk commit response) (some secret)) :
    secret • g = pk := by
  obtain ⟨⟨commitment, state⟩, -, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
  obtain ⟨first, -, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
  obtain ⟨second, -, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
  exact extract?_sound g pk commitment first second (LawfulMonadAttach.eq_of_canReturn_pure h)

section Measures

variable {m : Type → Type*} [Monad m] [LawfulMonad m]
  {sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α} (hsem : IsMeasureSemantics m sem)
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
include hsem

omit [Field F] [DecidableEq F] in
/-- Responding to a challenge does not change its distribution, when the response returns almost
surely. -/
theorem sem_interaction_map_fst (sample : m F) (response : F → m F)
    [∀ challenge, IsProbabilityMeasure (sem (response challenge))] :
    (sem (interaction sample response)).map Prod.fst = sem sample := by
  rw [← hsem.map_map _ measurable_fst]
  simp only [interaction, map_bind, map_pure, hsem.map_bind_of_discrete, hsem.map_pure]
  simp_rw [Measure.bind_const, measure_univ, one_smul]
  exact Measure.bind_dirac

/-- The extraction bound for a Schnorr identification prover whose commitment and responses
return almost surely: the commitment and private state are sampled once and shared by both
continuations. -/
theorem le_sem_extractor [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (sample : m F) (g pk : G) (commit : m (G × State)) (response : State → F → m F)
    [IsProbabilityMeasure (sem commit)]
    [∀ state challenge, IsProbabilityMeasure (sem (response state challenge))]
    (hsample : sem sample = uniformOn Set.univ) :
    let ε := sem (identificationExperiment sample g pk commit response) {true}
    ε ^ 2 - ε / Nat.card F ≤
      sem (extractor sample g pk commit response) {result | result.isSome} := by
  classical
  let := Fintype.ofFinite F
  let ν := fun state : G × State => sem (interaction sample (response state.2))
  let good := fun state : G × State => {t : F × F | Accepts g pk state.1 t.1 t.2}
  have hfiber (state : G × State) (c : F) :
      ν state {t | t.1 = c} ≤ (Nat.card F : ℝ≥0∞)⁻¹ := by
    change sem (interaction sample (response state.2)) (Prod.fst ⁻¹' {c}) ≤ _
    rw [← Measure.map_apply measurable_fst (measurableSet_singleton _),
      sem_interaction_map_fst hsem, hsample, uniformOn_univ]
    simp [Nat.card_eq_fintype_card]
  have hexperiment :
      sem (identificationExperiment sample g pk commit response) {true} =
        ∫⁻ state, ν state (good state) ∂sem commit := by
    simp only [identificationExperiment, hsem.map_bind_of_discrete, hsem.map_pure]
    rw [Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro state
    rw [Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable]
    calc
      _ = ∫⁻ t, (good state).indicator (fun _ => 1) t ∂ν state := by
        apply lintegral_congr
        intro t
        by_cases h : Accepts g pk state.1 t.1 t.2 <;>
          simp [good, h, Set.indicator, Measure.dirac_apply' _ (measurableSet_singleton _)]
      _ = _ := lintegral_indicator_one MeasurableSet.of_discrete
  have hlocal (state : G × State) :
      sem (do
        let first ← interaction sample (response state.2)
        let second ← interaction sample (response state.2)
        pure (extract? g pk state.1 first second)) {result | result.isSome} =
      ((ν state).prod (ν state))
        {p | p.1 ∈ good state ∧ p.2 ∈ good state ∧ p.1.1 ≠ p.2.1} := by
    let x := interaction sample (response state.2)
    have hprog : (do
        let first ← x
        let second ← x
        pure (extract? g pk state.1 first second)) =
        (fun p => extract? g pk state.1 p.1 p.2) <$>
          (x >>= fun first => x >>= fun second => pure (first, second)) := by
      simp only [map_bind, map_pure]
    change sem _ _ = _
    rw [hprog, hsem.map_map_of_discrete, hsem.map_bind_bind_prod,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    congr 1
    ext p
    simp [extract?, good, and_comm, and_left_comm]
  have hfork : sem (extractor sample g pk commit response) {result | result.isSome} =
      ∫⁻ state, ((ν state).prod (ν state))
        {p | p.1 ∈ good state ∧ p.2 ∈ good state ∧ p.1.1 ≠ p.2.1} ∂sem commit := by
    rw [extractor, hsem.map_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    exact lintegral_congr hlocal
  dsimp only
  rw [hexperiment, hfork, div_eq_mul_inv]
  exact Measure.sq_lintegral_sub_mul_le_prod (sem commit) ν Prod.fst good _ hfiber

end Measures

end Cslib.Crypto.Schnorr
