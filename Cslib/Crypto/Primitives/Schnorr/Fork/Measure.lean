/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Fork.Trace
public import Cslib.Crypto.Primitives.Schnorr.Fork.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability

/-! # Concrete probability of extracting from a Schnorr forgery -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory MonadAttach
open scoped ENNReal

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Countable F]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] [Countable P.A]

variable [∀ op, MeasurableSpace ((P + PFunctor.mk (M × G) (fun _ => F)).B op)]
  [∀ op, MeasurableSingletonClass ((P + PFunctor.mk (M × G) (fun _ => F)).B op)]
  [∀ op, Countable ((P + PFunctor.mk (M × G) (fun _ => F)).B op)]
  (μ : (op : (P + PFunctor.mk (M × G) (fun _ => F)).A) →
    Measure ((P + PFunctor.mk (M × G) (fun _ => F)).B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- Every successful forgery with a covered hash position contributes to the concrete
extraction bound. This theorem permits adaptive programs and arbitrary ambient randomness;
only fresh hash answers need the point-mass bound `r`. -/
theorem le_denote_forkExtractor (g pk : G)
    (program : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F))) (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ input challenge, μ (.inr input) {challenge} ≤ r)
    (hcovered : ∀ out, CanReturn (FreeM.trace program) out → out.1.isSome →
      ∃ n < q, forkPoint g pk out.1 out.2 = some n) :
    let ε := FreeM.denote μ program {candidate : Option (M × G × F) | candidate.isSome}
    ε * (ε / q - r) ≤ FreeM.denote μ (forkExtractor g pk program)
      {result : Option F | result.isSome} := by
  classical
  let : Countable (P + PFunctor.mk (M × G) (fun _ => F)).A :=
    inferInstanceAs (Countable (P.A ⊕ (M × G)))
  let : MeasurableSpace (List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B)) := ⊤
  let choose := fun out :
      Option (M × G × F) × List (Sigma (P + PFunctor.mk (M × G) (fun _ => F)).B) =>
    forkPoint g pk out.1 out.2
  have hfork := FreeM.le_denote_fork_trace μ (fun op => op.isRight) choose program q r
    (fun op hselect => by
      cases op with
      | inl op => cases hselect
      | inr input => exact hanswer input)
    (fun out _ n hn => forkPoint_lt g pk out.1 out.2 hn)
  have hprob : FreeM.denote μ (FreeM.trace program) {out | ∃ n < q, choose out = some n} =
      FreeM.denote μ program {candidate | candidate.isSome} := by
    calc
      _ = FreeM.denote μ (FreeM.trace program) {out | out.1.isSome} := by
        apply measure_congr
        filter_upwards [FreeM.ae_canReturn μ (FreeM.trace program)] with out hout
        apply propext
        constructor
        · rintro ⟨n, _, hn⟩
          cases hc : out.1 with
          | none => simp [choose, forkPoint, findForkPoint, hc] at hn
          | some candidate => simp
        · exact hcovered out hout
      _ = _ := by
        have hmap : (FreeM.denote μ (FreeM.trace program)).map Prod.fst =
            FreeM.denote μ program := by
          rw [← FreeM.denote_map _ _ _ measurable_fst]
          congr 1
          exact FreeM.map_fst_trace program
        rw [← hmap, Measure.map_apply measurable_fst MeasurableSet.of_discrete]
        rfl
  dsimp only at hfork ⊢
  rw [hprob] at hfork
  apply hfork.trans
  rw [forkExtractor, ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  apply measure_mono_ae
  filter_upwards [FreeM.ae_canReturn μ (FreeM.fork (fun op => op.isRight) choose
    (FreeM.trace program))] with out hout
  intro hsuccess
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hsuccess
  exact forkExtractor_finish_isSome g pk program hout hn

/-- Private randomness is sampled once and reused by the complete extractor, including the
simulator. The success probability is that of its first execution averaged over the same seed. -/
theorem le_denote_forkExtractor_bind {Seed : Type} [MeasurableSpace Seed]
    [MeasurableSingletonClass Seed] [Countable Seed]
    (seed : (P + PFunctor.mk (M × G) (fun _ => F)).FreeM Seed) (g pk : G)
    (program : Seed → (P + PFunctor.mk (M × G) (fun _ => F)).FreeM (Option (M × G × F)))
    (q : ℕ) (r : ℝ≥0∞) (hanswer : ∀ input challenge, μ (.inr input) {challenge} ≤ r)
    (hcovered : ∀ saved, CanReturn seed saved →
      ∀ out, CanReturn (FreeM.trace (program saved)) out → out.1.isSome →
        ∃ n < q, forkPoint g pk out.1 out.2 = some n) :
    let ε := FreeM.denote μ (seed >>= program) {candidate : Option (M × G × F) | candidate.isSome}
    ε * (ε / q - r) ≤
      FreeM.denote μ (seed >>= fun saved => forkExtractor g pk (program saved))
        {result : Option F | result.isSome} := by
  dsimp only
  simp only [FreeM.denote_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  refine (ENNReal.mul_sub_lintegral_le Measurable.of_discrete.aemeasurable
    (fun _ => prob_le_one) q r).trans ?_
  apply lintegral_mono_ae
  filter_upwards [FreeM.ae_canReturn μ seed] with saved hsaved
  exact le_denote_forkExtractor μ g pk (program saved) q r hanswer (hcovered saved hsaved)

/-- Concrete extraction from the public-key signing simulator. The query bound counts fresh
hash operations in the simulated experiment, including final verification. -/
theorem le_denote_signatureExtractor (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (q : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ input challenge, μ (.inr input) {challenge} ≤ r) :
    let ambient := fun op : P.A =>
      FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
    let program := (simulatedForgery ambient (sample.liftM ambient)
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run
    (∀ out, CanReturn (FreeM.trace program) out →
      out.2.countP (fun event => event.1.isRight) ≤ q) →
    let ε := FreeM.denote μ program {candidate : Option (M × G × F) | candidate.isSome}
    ε * (ε / q - r) ≤ FreeM.denote μ (signatureExtractor sample g pk adversary)
      {result : Option F | result.isSome} := by
  dsimp only
  intro hqueries
  apply le_denote_forkExtractor μ g pk _ q r hanswer
  rintro ⟨candidate, events⟩ htrace hsome
  cases candidate with
  | none => cases hsome
  | some candidate =>
    rcases candidate with ⟨message, commitment, response⟩
    obtain ⟨n, hn, hlt⟩ := exists_forkPoint_of_simulatedForgery _ _ g pk adversary htrace
    exact ⟨n, hlt.trans_le (hqueries _ htrace), hn⟩

/-- The source adversary's hash-query bound suffices: the verifier contributes one additional
query, and the signing simulator draws its coins from the ambient effects. -/
theorem le_denote_signatureExtractor_of_queryBoundP (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (qH : ℕ) (r : ℝ≥0∞)
    (hanswer : ∀ input challenge, μ (.inr input) {challenge} ≤ r)
    (hqueries : FreeM.queryBoundP (fun op : (signatureEffects P M G F).A => match op with
      | .inr (.inl _) => true | _ => false) (adversary pk) ≤ qH) :
    let ambient := fun op : P.A =>
      FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
    let program := (simulatedForgery ambient (sample.liftM ambient)
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run
    let ε := FreeM.denote μ program {candidate : Option (M × G × F) | candidate.isSome}
    ε * (ε / (qH + 1) - r) ≤ FreeM.denote μ (signatureExtractor sample g pk adversary)
      {result : Option F | result.isSome} := by
  have hbound := le_denote_signatureExtractor μ sample g pk adversary (qH + 1) r hanswer
  dsimp only at hbound ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hbound
  apply hbound
  intro out hout
  have h := (FreeM.countP_trace_le_queryBoundP _ _ hout).trans
    ((queryBoundP_simulatedForgery sample g pk adversary).trans
      (add_le_add hqueries le_rfl))
  exact_mod_cast h

end Cslib.Crypto.Schnorr
