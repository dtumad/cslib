/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Crypto.Primitives.Schnorr.Security
import Cslib.Foundations.Data.PFunctor.Free.Trace
import Mathlib.Algebra.Field.ZMod

set_option linter.hashCommand false

/-! Integration checks for cached signing, message freshness, and replay. The small field is
only an executable regression instance; the library theorems quantify over arbitrary fields. -/

open Cslib.Crypto PFunctor

namespace SchnorrTests

abbrev F := ZMod 101
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev random : PFunctor := ⟨Unit, fun _ => F⟩

def sample : random.FreeM F := FreeM.lift ()

def counted (op : random.A) : StateM ℕ (random.B op) := fun count =>
  (count, count + 1)

def honest : random.FreeM (Bool × List ((String × F) × F)) :=
  (do
    let signature ← Schnorr.sign (monadLift sample) (RandomOracle.query sample)
      (1 : F) (7 : F) "message"
    Schnorr.verify (RandomOracle.query sample) (1 : F) (7 : F) "message" signature :
      StateT (List ((String × F) × F)) random.FreeM Bool).run []

-- The verifier reuses the signing challenge: just the nonce and first hash query draw randomness.
#guard ((honest.liftM counted).run 3).1.1 = true
#guard ((honest.liftM counted).run 3).1.2.length = 1
#guard ((honest.liftM counted).run 3).2 = 5

def replaySignature (_pk : F) :
    (Schnorr.signatureEffects random String F F).FreeM (String × F × F) := do
  let signature ← FreeM.lift (P := Schnorr.signatureEffects random String F F)
    (.inr (.inr "message"))
  pure ("message", signature)

-- A valid signature obtained from the signing oracle is not a forgery on a fresh message.
#guard (((Schnorr.unforgeabilityExperiment sample (1 : F) replaySignature).liftM counted).run
  3 |>.run) == (false, 6)

example : Schnorr.extract (3 : F) (Schnorr.respond (7 : F) (11 : F) (3 : F))
    (5 : F) (Schnorr.respond (7 : F) (11 : F) (5 : F)) = (7 : F) := by
  norm_num [Schnorr.extract, Schnorr.respond]
  rw [div_eq_iff (by decide : (2 : F) ≠ 0)]
  norm_num

def twoSamples : random.FreeM (F × F) := do
  let first ← sample
  let second ← sample
  pure (first, second)

-- Replaying a prefix leaves the saved first sample in the continuation; only the suffix changes.
example : FreeM.replay [⟨(), (17 : F)⟩] twoSamples =
    some (do let second ← sample; pure ((17 : F), second)) := rfl

example : FreeM.replay [⟨(), (17 : F)⟩, ⟨(), (23 : F)⟩] twoSamples =
    some (pure ((17 : F), (23 : F))) := rfl

-- The simulated commitment is 1 when the challenge is 0 and response is 1.
-- An existing entry at that input causes an explicit programming failure.
#guard ((((Schnorr.simulateSign sample (1 : F) (7 : F) "message").run
  [(("message", 1), 42)]).run.liftM counted).run 0).run == (none, 2)

abbrev forkEffects : PFunctor := random + PFunctor.mk (String × F) (fun _ => F)

def forkAnswers (op : forkEffects.A) : StateM ℕ (forkEffects.B op) := fun count =>
  match op with
  | .inl () => ((count : F), count + 1)
  | .inr _ => ((count : F), count + 1)

-- A regression adversary knows the test secret. It requests a signature on another message,
-- then creates its own forgery. This tests the entire extractor, not a security assumption.
def knowledgeable (_pk : F) :
    (Schnorr.signatureEffects random String F F).FreeM (String × F × F) := do
  let _ ← FreeM.lift (P := Schnorr.signatureEffects random String F F)
    (.inr (.inr "signed"))
  let challenge ← FreeM.lift (P := Schnorr.signatureEffects random String F F)
    (.inr (.inl ("fresh", 11)))
  pure ("fresh", 11, Schnorr.respond (7 : F) 11 challenge)

#guard ((((Schnorr.signatureExtractor sample (1 : F) (7 : F) knowledgeable).liftM
  forkAnswers).run 0).run == (some (7 : F), 4))

#guard ((((Schnorr.dlogReduction sample (1 : F) knowledgeable (7 : F)).liftM
  counted).run 0).run == (some (7 : F), 4))

-- A signing-oracle reply loses freshness and cannot become an extraction target.
#guard ((((Schnorr.signatureExtractor sample (1 : F) (7 : F) replaySignature).liftM
  forkAnswers).run 0).run == (none, 2))

-- With the identity public key this candidate accepts every challenge. The adversary makes
-- no hash query, so extraction must include the verifier's final query as a forkable occurrence.
def identityKey (_pk : F) :
    (Schnorr.signatureEffects random String F F).FreeM (String × F × F) :=
  pure ("fresh", 1, 1)

#guard ((((Schnorr.signatureExtractor sample (1 : F) (0 : F) identityKey).liftM
  forkAnswers).run 0).run == (some (0 : F), 2))

def equalChallenges (op : forkEffects.A) : Id (forkEffects.B op) :=
  match op with
  | .inl () => pure (0 : F)
  | .inr _ => pure (0 : F)

-- Equal challenges are rejected before dividing, even though both transcripts verify.
#guard (((Schnorr.signatureExtractor sample (1 : F) (0 : F) identityKey).liftM
  equalChallenges).run == none)

-- The selector skips unrelated inputs and nonaccepting challenges, and failed output selects none.
#guard Schnorr.findForkPoint (1 : F) (7 : F) (some ("fresh", 11, Schnorr.respond (7 : F) 11 3))
  [(("other", 11), 3), (("fresh", 11), 2), (("fresh", 11), 3)] == some 2
#guard Schnorr.findForkPoint (1 : F) (7 : F) (some ("fresh", 11, Schnorr.respond (7 : F) 11 3))
  [(("fresh", 11), 2)] == none
#guard Schnorr.findForkPoint (1 : F) (7 : F) (none : Option (String × F × F))
  [(("fresh", 11), 3)] == none

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance : MeasurableSpace F := ⊤
local instance : MeasurableSingletonClass F := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List ((Unit × F) × F)) := ⊤

noncomputable def answers (_ : random.A) : Measure F := uniformOn Set.univ

local instance (op : random.A) : IsProbabilityMeasure (answers op) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set F)))

-- Instantiate the joint-state collision theorem with the concrete scalar cardinality.
example (cache : List ((Unit × F) × F)) :
    FreeM.denote answers ((Schnorr.simulateSign sample (1 : F) (7 : F) ()).run cache).run
      {none} ≤ cache.length / (101 : ℝ≥0∞) := by
  have hg : Function.Bijective (fun scalar : F => scalar • (1 : F)) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro x
      exact ⟨x, by simp⟩
  simpa [Nat.card_eq_fintype_card] using Schnorr.denote_simulateSign_none_le
    answers sample (1 : F) (7 : F) () cache hg (FreeM.denote_lift (P := random) answers ())

-- The verifier-only fork has one query, and two uniform challenges differ with probability 100/101.
-- This pins the zero-adversary-query boundary of the quantitative theorem.
def noQuery (_pk : F) : (Schnorr.signatureEffects random Unit F F).FreeM (Unit × F × F) :=
  pure ((), 1, 1)

example : (100 / 101 : ℝ≥0∞) ≤
    FreeM.denote answers (Schnorr.dlogReduction sample (1 : F) noQuery 0)
      {result : Option F | result.isSome} := by
  have hbound := Schnorr.le_denote_dlogReduction answers sample (1 : F) 0 noQuery 0
    (FreeM.denote_lift (P := random) answers ()) (by simp [noQuery])
  have hprogram :
      (Schnorr.simulatedForgery FreeM.lift sample (fun _ => sample)
        (1 : F) 0 noQuery).run = (fun _ : F => some ((), (1 : F), (1 : F))) <$> sample := by
    simp only [Schnorr.simulatedForgery, noQuery, FreeM.liftM_pure, StateT.run_pure,
      pure_bind, OptionT.run, Schnorr.verify, StateT.run_bind, StateT.run_pure,
      monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, bind_assoc, pure_bind]
    simp only [StateT.run, RandomOracle.query, List.lookup_nil, bind_assoc, pure_bind]
    change (do let challenge ← sample; pure (some ((), (1 : F), (1 : F)))) = _
    simp only [map_eq_pure_bind]
  dsimp only at hbound
  rw [hprogram, ← FreeM.map_eq_map, FreeM.denote_map (P := random) _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at hbound
  simp only [Set.preimage, Set.mem_ofPred_eq, Option.isSome_some, Set.ofPred_true, measure_univ,
    Nat.cast_zero, zero_add, div_one, one_mul, Nat.card_eq_fintype_card, ZMod.card] at hbound
  have harith : (1 - 1 / 101 : ℝ≥0∞) = 100 / 101 := by
    have h := ENNReal.sub_div (a := 101) (b := 1) (c := 101) (by intros; norm_num)
    norm_num [ENNReal.div_self (by norm_num : (101 : ℝ≥0∞) ≠ 0) (by simp)] at h
    have hsub : (101 : ℝ≥0∞) - 1 = 100 := by
      simpa using (ENNReal.natCast_sub 101 1).symm
    rw [hsub] at h
    simpa only [one_div] using h.symm
  exact harith ▸ hbound

end SchnorrTests
