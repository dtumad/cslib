/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.ElGamal
import Cslib.Crypto.Primitives.Schnorr.Oracle
import Cslib.Crypto.Primitives.Schnorr.Sampling
import Cslib.Foundations.Data.PFunctor.Free.Random
import Mathlib.Algebra.Field.ZMod

set_option linter.hashCommand false

/-! Run both honest schemes from individual bits through bounded rejection sampling.
`OptionT` retains sampling failure; `StateT` retains Schnorr's hash cache. -/

open PFunctor Cslib.Crypto

namespace CryptoSampling

abbrev bits : PFunctor := ⟨Unit, fun _ => Fin 2⟩
abbrev F := ZMod 101
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def sample (attempts : ℕ) : OptionT bits.FreeM (Fin 101) :=
  OptionT.mk (FreeM.sampleFin (FreeM.lift ()) 101 7 attempts)

def scalar (attempts : ℕ) : OptionT bits.FreeM F :=
  (fun x : Fin 101 => (x.val : F)) <$> sample attempts

def elgamal (attempts : ℕ) : OptionT bits.FreeM (Multiplicative F) := do
  let (pk, secret) ← ElGamal.keygen (sample attempts) (Multiplicative.ofAdd (1 : F))
  let ciphertext ← ElGamal.encrypt (sample attempts) (Multiplicative.ofAdd (1 : F)) pk
    (Multiplicative.ofAdd (42 : F))
  pure (ElGamal.decrypt secret ciphertext)

def schnorr (attempts : ℕ) : OptionT bits.FreeM Bool := do
  let (pk, secret) ← Schnorr.keygen (scalar attempts) (1 : F)
  let (valid, _) ← (do
    let signature ← Schnorr.sign (monadLift (scalar attempts))
      (RandomOracle.query (scalar attempts)) (1 : F) secret "message"
    Schnorr.verify (RandomOracle.query (scalar attempts)) (1 : F) pk "message" signature :
      StateT (List ((String × F) × F)) (OptionT bits.FreeM) Bool).run []
  pure valid

-- Repeated 7-bit blocks with a single set bit are nonzero accepted proposals.
def accepted (_ : bits.A) : StateM ℕ (Fin 2) := fun count =>
  (if count % 7 = 0 then 1 else 0, count + 1)

def rejected (_ : bits.A) : StateM ℕ (Fin 2) := fun count => (1, count + 1)

#guard ((((elgamal 2).run.liftM accepted).run 0).run ==
  (some (Multiplicative.ofAdd (42 : F)), 14))
#guard ((((schnorr 2).run.liftM accepted).run 0).run == (some true, 21))

-- Exhausting the sampler stops key generation in both schemes and keeps the failure visible.
#guard ((((elgamal 2).run.liftM rejected).run 0).run == (none, 14))
#guard ((((schnorr 2).run.liftM rejected).run 0).run == (none, 14))

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance : MeasurableSpace F := ⊤
local instance : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

abbrev scalars : PFunctor := ⟨Unit, fun _ => F⟩

noncomputable def scalarLaw (_ : scalars.A) : Measure F := uniformOn Set.univ
noncomputable def bitLaw (_ : bits.A) : Measure (Fin 2) := uniformOn Set.univ

local instance (op : scalars.A) : IsProbabilityMeasure (scalarLaw op) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set F)))
local instance (op : bits.A) : IsProbabilityMeasure (bitLaw op) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin 2))))

def scalarHandler (attempts : ℕ) (_ : scalars.A) : OptionT bits.FreeM F :=
  OptionT.mk (Option.map (ZMod.finEquiv 101).toEquiv <$>
    FreeM.sampleFin (FreeM.lift ()) 101 7 attempts)

def noQuery (_pk : F) : (Schnorr.signatureEffects scalars Unit F F).FreeM (Unit × F × F) :=
  pure ((), 1, 1)

-- This boundary case still needs key generation and two verifier draws. The cutoff law is
-- proved from the actual bit sampler and applied to the complete two-run reduction.
example (attempts : ℕ) :
    (FreeM.denote bitLaw ((Schnorr.unforgeabilityExperiment (FreeM.lift (P := scalars) ())
      (1 : F) noQuery).liftM (scalarHandler attempts)).run {some true}).toReal ≤
        1 / 101 + Real.sqrt
          ((FreeM.denote bitLaw ((DiscreteLog.experiment (FreeM.lift (P := scalars) ()) (1 : F)
            (Schnorr.dlogReduction (FreeM.lift (P := scalars) ()) (1 : F) noQuery)).liftM
              (scalarHandler attempts)).run {some true}).toReal +
                3 * (2⁻¹ : ℝ) ^ attempts) := by
  have hcoin : FreeM.denote bitLaw (FreeM.lift (P := bits) ()) = uniformOn Set.univ :=
    FreeM.denote_lift bitLaw ()
  have hstep (op : scalars.A) : (FreeM.denote bitLaw (scalarHandler attempts op).run).comap some ≤
      scalarLaw op :=
    FreeM.comap_denote_map_sampleFin_le (P := bits) (α := F)
      bitLaw (FreeM.lift (P := bits) ()) hcoin 101 7 attempts
      (ZMod.finEquiv 101).toEquiv (by decide)
  have hfailure (op : scalars.A) : FreeM.denote bitLaw (scalarHandler attempts op).run {none} ≤
      (2 : ℝ≥0∞)⁻¹ ^ attempts :=
    FreeM.denote_map_sampleFin_none_le_of_bounds (P := bits) (α := F)
      bitLaw (FreeM.lift (P := bits) ()) hcoin 101 7 attempts
      (ZMod.finEquiv 101).toEquiv (by decide) (by decide)
  have hg : Function.Bijective (fun scalar : F => scalar • (1 : F)) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro x
      exact ⟨x, by simp⟩
  have h := Schnorr.euf_cma_bound_sqrt_cutoff (P := scalars) (Q := bits)
    scalarLaw bitLaw (scalarHandler attempts) hstep
    (fun _ => true) ((2 : ℝ≥0∞)⁻¹ ^ attempts) (by finiteness) hfailure
    (FreeM.lift (P := scalars) ()) (1 : F) noQuery hg
    (FreeM.denote_lift (P := scalars) scalarLaw ())
    (by simp [FreeM.queryBoundP_lift (P := scalars)]) 0 0 0
    (by simp [noQuery]) (by simp [noQuery]) (by simp [noQuery])
  simpa [Nat.card_eq_fintype_card] using h

end CryptoSampling
