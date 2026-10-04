/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PFunctor
public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach
public import Cslib.Foundations.MeasureTheory.Collision
public import Cslib.Foundations.MeasureTheory.Option

/-!
# Forking a Schnorr identification prover

The extractor saves the prover's commitment and private state, then runs two independent
challenge/response continuations from that same state. Every extracted value is a discrete
logarithm of the public key. A prover accepted with probability `ε` yields extraction probability
at least `ε² - ε / |F|`.

This is the fixed-commitment forking step. Applying it to signatures additionally requires the
adaptive random-oracle occurrence selection and signing simulation; the EUF-CMA experiment in
`Schnorr.Oracle` is not itself a rewindable identification prover.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory
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

/-- The interactive verification experiment, before applying Fiat--Shamir. -/
def identificationExperiment (sample : m F) (g pk : G) (commit : m (G × State))
    (response : State → F → m F) : m Bool := do
  let (commitment, state) ← commit
  let (challenge, answer) ← interaction sample (response state)
  pure (decide (Accepts g pk commitment challenge answer))

/-- Check the two transcripts before extracting a witness. -/
def extract? (g pk commitment : G) (first second : F × F) : Option F :=
  if first.1 ≠ second.1 ∧ Accepts g pk commitment first.1 first.2 ∧
      Accepts g pk commitment second.1 second.2 then
    some (extract first.1 first.2 second.1 second.2)
  else none

/-- Two continuations share the original commitment and private state. The prefix runs once. -/
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

variable {P : PFunctor.{0, 0}}

theorem extractor_sound (sample : P.FreeM F) (g pk : G) (commit : P.FreeM (G × State))
    (response : State → F → P.FreeM F) {secret : F}
    (h : MonadAttach.CanReturn (extractor sample g pk commit response) (some secret)) :
    secret • g = pk := by
  obtain ⟨state, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  obtain ⟨first, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  obtain ⟨second, _, h⟩ := (FreeM.canReturn_bind _ _ _).mp h
  exact extract?_sound g pk state.1 first second h.symm

section Measures

variable [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]

omit [Field F] [DecidableEq F] in
/-- Responding to a challenge cannot change its marginal distribution. -/
theorem denote_interaction_map_fst (sample : P.FreeM F) (response : F → P.FreeM F) :
    (FreeM.denote μ (interaction sample response)).map Prod.fst = FreeM.denote μ sample := by
  rw [← FreeM.denote_map _ _ _ measurable_fst]
  simp only [interaction, FreeM.map_eq_map, map_bind, map_pure,
    FreeM.denote_bind_of_discrete, FreeM.denote_pure]
  simp_rw [Measure.bind_const, measure_univ, one_smul]
  exact Measure.bind_dirac

/-- Concrete extraction bound for a Schnorr identification prover. The commitment and the
prover's private state are sampled only once, then shared by both continuations. -/
theorem le_denote_extractor [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    (sample : P.FreeM F) (g pk : G) (commit : P.FreeM (G × State))
    (response : State → F → P.FreeM F)
    (hsample : FreeM.denote μ sample = uniformOn Set.univ) :
    let ε := FreeM.denote μ (identificationExperiment sample g pk commit response) {true}
    ε ^ 2 - ε / Nat.card F ≤ FreeM.denote μ (extractor sample g pk commit response)
      {result | result.isSome} := by
  classical
  let := Fintype.ofFinite F
  let ν := fun state : G × State => FreeM.denote μ (interaction sample (response state.2))
  let good := fun state : G × State => {t : F × F | Accepts g pk state.1 t.1 t.2}
  have hfiber (state : G × State) (c : F) :
      ν state {t | t.1 = c} ≤ (Nat.card F : ℝ≥0∞)⁻¹ := by
    change FreeM.denote μ (interaction sample (response state.2)) (Prod.fst ⁻¹' {c}) ≤ _
    rw [← Measure.map_apply measurable_fst (measurableSet_singleton _),
      denote_interaction_map_fst, hsample, uniformOn_univ]
    simp [Nat.card_eq_fintype_card]
  have hexperiment :
      FreeM.denote μ (identificationExperiment sample g pk commit response) {true} =
        ∫⁻ state, ν state (good state) ∂FreeM.denote μ commit := by
    simp only [identificationExperiment, FreeM.denote_bind_of_discrete, FreeM.denote_pure]
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
      FreeM.denote μ (do
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
          (do let first ← x; let second ← x; pure (first, second)) := by
      simp only [map_bind, map_pure]
    change FreeM.denote μ _ _ = _
    rw [hprog, ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete]
    have hpair := FreeM.denote_bind_bind_prod_mk μ x x
    simp only [FreeM.bind_eq_bind] at hpair
    rw [hpair, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    congr 1
    ext p
    simp [extract?, good, and_comm, and_left_comm]
  have hfork : FreeM.denote μ (extractor sample g pk commit response)
      {result | result.isSome} =
      ∫⁻ state, ((ν state).prod (ν state))
        {p | p.1 ∈ good state ∧ p.2 ∈ good state ∧ p.1.1 ≠ p.2.1} ∂FreeM.denote μ commit := by
    rw [extractor, FreeM.denote_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    exact lintegral_congr hlocal
  dsimp only
  rw [hexperiment, hfork, div_eq_mul_inv]
  exact Measure.sq_lintegral_sub_mul_le_prod (FreeM.denote μ commit) ν Prod.fst good _ hfiber

end Measures

end Cslib.Crypto.Schnorr
