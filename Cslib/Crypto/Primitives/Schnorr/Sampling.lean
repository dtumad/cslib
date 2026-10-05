/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Security
public import Cslib.Crypto.Primitives.Schnorr.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Random.Approximation

/-!
# Schnorr security with bounded sampling

Local cutoff certificates compose through the complete games, including both fork executions.
Exhaustion is explicit. It can only remove successful forgeries, so the honest implemented game
needs no additional error on the left of the security inequality.
-/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {P Q : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [Countable P.A]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]
  (ν : (op : Q.A) → Measure (Q.B op)) [∀ op, IsProbabilityMeasure (ν op)]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Finite F]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]

/-- The implemented EUF-CMA game is bounded by the actual implemented discrete-logarithm
experiment. Only per-operation cutoff laws are assumed; the full-game error is derived. -/
theorem euf_cma_bound_sqrt_cutoff
    (handler : (op : P.A) → OptionT Q.FreeM (P.B op))
    (hstep : ∀ op, (FreeM.denote ν (handler op).run).comap some ≤ μ op)
    (risk : P.A → Bool) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (hfailure : ∀ op, FreeM.denote ν (handler op).run {none} ≤ if risk op then δ else 0)
    (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F))
    (hg : Function.Bijective (fun scalar : F => scalar • g))
    (hsample : FreeM.denote μ sample = uniformOn Set.univ)
    (hdraw : FreeM.queryBoundP risk sample ≤ 1) (q qS qH : ℕ)
    (hqueries : ∀ pk, FreeM.queryBoundP (fun op : (signatureEffects P M G F).A =>
      match op with | .inl op => risk op | .inr _ => true) (adversary pk) ≤ q)
    (hsign : ∀ pk, FreeM.queryBoundP (fun op : (signatureEffects P M G F).A => match op with
      | .inr (.inr _) => true | _ => false) (adversary pk) ≤ qS)
    (hhash : ∀ pk, FreeM.queryBoundP (fun op : (signatureEffects P M G F).A => match op with
      | .inr (.inl _) => true | _ => false) (adversary pk) ≤ qH) :
    (FreeM.denote ν ((unforgeabilityExperiment sample g adversary).liftM handler).run
      {some true}).toReal ≤
        (qS : ℝ) * (qH + qS) / Nat.card F + (qH + 1) / Nat.card F +
          Real.sqrt ((qH + 1) *
            ((FreeM.denote ν ((DiscreteLog.experiment sample g
              (dlogReduction sample g adversary)).liftM handler).run {some true}).toReal +
                (4 * q + 3) * δ.toReal)) := by
  have hgame := ENNReal.toReal_mono (measure_ne_top _ _)
    (FreeM.denote_liftM_option_le μ ν handler hstep
      (unforgeabilityExperiment sample g adversary) {true})
  have hcost : FreeM.queryBoundP risk
      (DiscreteLog.experiment sample g (dlogReduction sample g adversary)) ≤
        ((4 * q + 3 : ℕ) : ℕ∞) := by
    simpa using queryBoundP_dlogExperiment risk sample hdraw g adversary q hqueries
  have herror := ENNReal.toReal_mono (by finiteness)
    (FreeM.denote_le_liftM_option_add_of_le μ ν handler hstep risk δ hfailure
      (DiscreteLog.experiment sample g (dlogReduction sample g adversary))
        (4 * q + 3) hcost {true})
  simp only [Set.image_singleton] at hgame herror
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at herror
  push_cast at herror
  apply (hgame.trans (euf_cma_bound_sqrt μ sample g adversary hg hsample qS qH hsign hhash)).trans
  gcongr

end Cslib.Crypto.Schnorr
