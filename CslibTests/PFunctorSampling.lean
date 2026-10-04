/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Random
import Cslib.Foundations.Data.PFunctor.Free.Random.Approximation
import Cslib.Foundations.Data.PFunctor.Free.Random.Tape
import Cslib.Foundations.Data.PFunctor.Free.Fork.Replay
import Cslib.Crypto.Negligible

/-! Sampling a range just above a power of two exercises the worst rejection rate. These
checks pin the connection between the actual binary program, its failure event, and its cost. -/

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctorSampling

set_option linter.hashCommand false

abbrev bits : PFunctor := ⟨Unit, fun _ => Fin 2⟩

def coin : bits.FreeM (Fin 2) := FreeM.lift ()

noncomputable def answers (_ : bits.A) : Measure (Fin 2) := uniformOn Set.univ

theorem denote_coin : FreeM.denote answers coin = uniformOn Set.univ :=
  FreeM.denote_lift (P := bits) answers ()

theorem cost_coin : FreeM.queryBound coin = 1 := FreeM.queryBound_lift (P := bits) ()

abbrev requests : PFunctor := ⟨Bool, fun _ => Fin 2⟩

def savedPrefix : requests.FreeM (Fin 2 × Fin 2) := do
  let saved ← FreeM.lift false
  let challenge ← FreeM.lift true
  pure (saved, challenge)

def replayed : requests.FreeM ((Fin 2 × Fin 2) ×
    Option ((op : requests.A) × requests.B op × requests.B op × (Fin 2 × Fin 2))) :=
  FreeM.forkWithReplay id (fun _ => some 0) savedPrefix

-- Replaying the prefix consumes no answer. Only the selected challenge is replaced.
#guard FreeM.runFromAnswers replayed [0, 1, 0] ==
  some ((0, 1), some ⟨true, 1, 0, (0, 0)⟩)
#guard FreeM.runFromAnswers replayed [0, 1] == none

-- Spare tape entries are irrelevant, including after an adaptive second run.
#guard FreeM.runFromAnswers replayed [0, 1, 0, 1] ==
  FreeM.runFromAnswers replayed [0, 1, 0]

local instance (op : bits.A) : IsProbabilityMeasure (answers op) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin 2))))

-- The whole two-run distribution is preserved, rather than just its first marginal.
example :
    let observe := fun out : (Fin 2 × Fin 2) ×
      Option ((op : requests.A) × requests.B op × requests.B op × (Fin 2 × Fin 2)) =>
        (out.1, out.2.map fun event => event.2.2.2)
    FreeM.denote answers (FreeM.runFromAnswers (observe <$> replayed) <$>
      (List.replicate 4 ()).mapM (fun _ => coin)) =
        (FreeM.denote (P := requests) (fun _ => FreeM.denote answers coin)
          (observe <$> replayed)).map some := by
  dsimp only
  apply FreeM.denote_runFromAnswers
  rw [FreeM.queryBound_map]
  apply (FreeM.queryBound_forkWithReplay_le id (fun _ => some 0) savedPrefix).trans
  norm_num [savedPrefix, FreeM.queryBound_lift_bind (P := requests)]

example (attempts : ℕ) :
    FreeM.denote answers (FreeM.sampleFin coin 257 9 attempts) {none} =
      (1 - (257 : ℝ≥0∞) / 512) ^ attempts := by
  convert FreeM.denote_sampleFin_none answers coin denote_coin
    257 9 attempts (by decide) using 1
  norm_num

example (attempts : ℕ) :
    FreeM.queryBound (FreeM.sampleFin coin 257 9 attempts) ≤ (attempts : ℕ∞) * 9 := by
  simpa using FreeM.queryBound_sampleFin_le coin 1 cost_coin.le 257 9 attempts

example (n attempts : ℕ) [NeZero n] :
    FreeM.denote answers (FreeM.sampleFin coin n (Nat.clog 2 n) attempts) {none} ≤
      (2 : ℝ≥0∞)⁻¹ ^ attempts :=
  FreeM.denote_sampleFin_none_le answers coin denote_coin n attempts

-- A security-parameter-sized attempt budget has negligible failure; each attempt uses clog₂ n bits.
example : Cslib.Crypto.Negligible (fun security => (1 / 2 : ℝ) ^ security) :=
  Cslib.Crypto.negligible_geometric (by norm_num)

abbrev adaptiveDraws : PFunctor := ⟨Bool, fun large => Fin (if large then 5 else 3)⟩

-- The first answer determines the second range. Neither range is a power of two.
def twoDraws : adaptiveDraws.FreeM Bool := do
  let first ← FreeM.lift false
  let second ← FreeM.lift (first.val == 0)
  pure (second.val == 0)

example (attempts : ℕ) :
    (∫⁻ value, if value then 1 else 0 ∂FreeM.denote (P := adaptiveDraws)
      (fun _ => uniformOn Set.univ) twoDraws) ≤
      (∫⁻ out, out.elim 0 (fun value => if value then 1 else 0) ∂FreeM.denote answers
        (twoDraws.liftM (fun large => OptionT.mk
          (FreeM.sampleFin coin (if large then 5 else 3) (if large then 3 else 2) attempts))).run) +
            2 * (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  let : ∀ large : Bool, NeZero (if large then 5 else 3 : ℕ) := by
    intro large
    cases large <;> infer_instance
  refine FreeM.lintegral_uniform_le_liftM_sampleFin_add
    (P := bits) (Operation := Bool) (α := Bool) answers coin denote_coin
    (fun large : Bool => if large then 5 else 3) (fun large : Bool => if large then 3 else 2)
    attempts 2
    ?_ ?_ twoDraws ?_ (fun value : Bool => if value then 1 else 0) ?_
  · intro large; cases large <;> decide
  · intro large; cases large <;> decide
  · norm_num [twoDraws, FreeM.queryBound_lift_bind (P := adaptiveDraws),
      FreeM.queryBound_lift (P := adaptiveDraws)]
  · intro value; cases value <;> simp

example : Cslib.Crypto.Negligible
    (fun n => ((7 * (n + 1) ^ 3 : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ (n + 1)) :=
  Cslib.Crypto.negligible_sampling_error (by fun_prop) (fun _ => by omega)

end PFunctorSampling
