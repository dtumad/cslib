/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free.Fork.Probability
import Cslib.Foundations.Data.PFunctor.Free.Fork.Replay
import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape
import Cslib.Foundations.MeasureTheory.Uniform
import Cslib.Crypto.RandomOracle

set_option linter.hashCommand false

/-! Adaptive selection uses the first run's final response. Replay retains the prefix,
including a cache inlined through `StateT`, and only reruns the selected suffix. -/

open PFunctor Cslib.Crypto

namespace PFunctorFork

abbrev effects : PFunctor := ⟨Bool, fun _ => ℕ⟩

def counted (_ : effects.A) : StateM ℕ ℕ := fun count => (count, count + 1)

def program : effects.FreeM (ℕ × ℕ × ℕ) := do
  let saved ← FreeM.lift false
  let first ← FreeM.lift true
  let last ← FreeM.lift true
  pure (saved, first, last)

def runFork (choose : (ℕ × ℕ × ℕ) → Option ℕ) : StateM ℕ
    ((ℕ × ℕ × ℕ) × Option (ℕ × ℕ × ℕ)) :=
  ((fun out => (out.1, out.2.map fun event => event.2.2.2)) <$>
    FreeM.forkWithReplay id choose program).liftM counted

def choose (out : ℕ × ℕ × ℕ) : Option ℕ := if out.2.2 % 2 = 0 then some 1 else some 0

-- The saved ambient response survives either fork. Only hash operations count toward the index.
#guard ((runFork choose).run 0).run == (((0, 1, 2), some (0, 1, 3)), 4)
#guard ((runFork choose).run 1).run == (((1, 2, 3), some (1, 4, 5)), 6)

-- Missing and out-of-range selections consume no additional randomness.
#guard ((runFork (fun _ => none)).run 0).run == (((0, 1, 2), none), 3)
#guard ((runFork (fun _ => some 2)).run 0).run == (((0, 1, 2), none), 3)

-- An incompatible prefix is rejected before making any fresh request.
#guard ((((FreeM.runWithReplay (P := effects) [⟨true, 99⟩] program).run).liftM
  counted).run 0).run == (none, 0)

-- A recorded suffix extending past return is rejected too.
#guard ((((FreeM.runWithReplay (P := effects) [⟨false, 9⟩, ⟨true, 8⟩, ⟨true, 7⟩, ⟨true, 6⟩]
    program).run).liftM counted).run 0).run == (none, 0)

def fixedTape (tape : List ℕ) : effects.FreeM (ℕ × ℕ) := do
  let challenge ← FreeM.lift true
  pure (challenge, tape.headD 0)

-- Private randomness is sampled once, although the program reads it after the fork point.
-- Both runs retain that sample while receiving different challenges.
example : FreeM.fork id (fun _ => some 0)
      ([()].mapM (fun _ => FreeM.lift false) >>= fixedTape) =
    ([()].mapM (fun _ => FreeM.lift false) >>= fun tape =>
      FreeM.fork id (fun _ => some 0) (fixedTape tape)) :=
  FreeM.fork_mapM_bind_of_not_select _ _ _ _ _ rfl

#guard (((FreeM.forkWithReplay id (fun _ => some 0)
    ([()].mapM (fun _ => FreeM.lift false) >>= fixedTape)).liftM counted).run 0).run ==
      (((1, 0), some ⟨true, 1, 2, (2, 0)⟩), 3)

def cached : effects.FreeM ((ℕ × ℕ × ℕ) × List (Bool × ℕ)) :=
  (do
    let saved ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) false
    let fresh ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) true
    let repeated ← RandomOracle.query (FreeM.lift true : effects.FreeM ℕ) false
    pure (saved, fresh, repeated) : StateT (List (Bool × ℕ)) effects.FreeM (ℕ × ℕ × ℕ)).run []

def forkedCache : StateM ℕ
    (((ℕ × ℕ × ℕ) × List (Bool × ℕ)) × Option ((ℕ × ℕ × ℕ) × List (Bool × ℕ))) :=
  ((fun out => (out.1, out.2.map fun event => event.2.2.2)) <$>
    FreeM.forkWithReplay id (fun _ => some 1) cached).liftM counted

-- Each branch has its own fresh entry; both retain and reuse the saved entry without a new draw.
#guard (forkedCache.run 0).run ==
  ((((0, 1, 0), [(true, 1), (false, 0)]), some ((0, 2, 0), [(true, 2), (false, 0)])), 3)

-- Tape replay counts selected queries, retaining the unselected response in either prefix.
#guard FreeM.forkFromAnswers id choose program [10, 11, 12] [30] ==
  some ((10, 11, 12), some ⟨true, 12, 30, (10, 11, 30)⟩)
#guard FreeM.forkFromAnswers id choose program [10, 11, 13] [30, 31] ==
  some ((10, 11, 13), some ⟨true, 11, 30, (10, 30, 31)⟩)

-- A missing fork needs no fresh tape. Actual exhaustion remains distinct from that case.
#guard FreeM.forkFromAnswers id (fun _ => none) program [10, 11, 12] [] ==
  some ((10, 11, 12), none)
#guard FreeM.forkFromAnswers id (fun _ => some 2) program [10, 11, 12] [] ==
  some ((10, 11, 12), none)
#guard FreeM.forkFromAnswers id choose program [10, 11] [30, 31] == none
#guard FreeM.forkFromAnswers id choose program [10, 11, 13] [30] == none

-- The private seed is still read after the fork, and both branches see the same seed.
#guard FreeM.forkFromAnswers id (fun _ => some 0) (fixedTape [99]) [1] [2] ==
  some ((1, 99), some ⟨true, 1, 2, (2, 99)⟩)

-- Reexecution reconstructs the prefix cache and excludes the first run's suffix entry.
#guard (FreeM.forkFromAnswers id (fun _ => some 1) cached [0, 1] [5]).map
    (fun out => (out.1, out.2.map fun event => event.2.2.2)) ==
  some ((((0, 1, 0), [(true, 1), (false, 0)]),
    some ((0, 5, 0), [(true, 5), (false, 0)])))

def changingPath : effects.FreeM (ℕ × ℕ) := do
  let first ← FreeM.lift true
  if first = 0 then pure (first, 0) else
    let second ← FreeM.lift true
    pure (first, second)

-- The first run leaves an answer unused; a longer second run uses only its fresh suffix.
#guard FreeM.forkFromAnswers id (fun _ => some 0) changingPath [0, 99] [1, 2] ==
  some ((0, 0), some ⟨true, 0, 1, (1, 2)⟩)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev four : PFunctor := ⟨Unit, fun _ => Fin 4⟩

local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => trivial⟩

noncomputable def uniformAnswers (_ : four.A) : Measure (Fin 4) := uniformOn Set.univ

local instance (op : four.A) : IsProbabilityMeasure (uniformAnswers op) := by
  unfold uniformAnswers
  infer_instance

def twoDraws : four.FreeM (Fin 4) := do
  let _ ← FreeM.lift ()
  FreeM.lift ()

def adaptive (last : Fin 4) : Option ℕ := if last.val < 2 then some 0 else some 1

-- The selector depends on the final draw, even when it chooses the earlier query.
-- This checks a positive numerical bound, including the challenge-collision subtraction.
example : (1 / 4 : ℝ≥0∞) ≤
    FreeM.denote uniformAnswers (FreeM.fork (fun _ => true) adaptive twoDraws)
      (⋃ n, FreeM.forkSuccess adaptive n) := by
  have hbound := FreeM.le_denote_fork uniformAnswers (fun _ => true) adaptive twoDraws 2
    (1 / 4) (fun _ _ _ => by simp [uniformAnswers, uniformOn_univ]) (by
      intro a events htrace n hn
      obtain ⟨first, rest, hrest, rfl⟩ :=
        (FreeM.canReturn_trace_lift_bind (P := four) () _ _ _).mp htrace
      obtain ⟨last, tail, htail, rfl⟩ :=
        (FreeM.canReturn_trace_lift_bind (P := four) () _ _ _).mp hrest
      have htail : (a, tail) = (last, []) := htail
      cases htail
      simp only [List.countP_cons, List.countP_nil, ↓reduceIte] at *
      unfold adaptive at hn
      split at hn <;> simp only [Option.some.injEq] at hn <;> omega)
  have hsuccess : {a : Fin 4 | ∃ n < 2, adaptive a = some n} = Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    unfold adaptive
    split <;> simp
  dsimp only at hbound
  rw [hsuccess, measure_univ] at hbound
  have harith : (1 : ℝ≥0∞) * (1 / 2 - 1 / 4) = 1 / 4 := by
    rw [one_mul]
    have hhalf : (1 / 2 : ℝ≥0∞) / 2 = 1 / 4 := by
      simp only [div_eq_mul_inv, one_mul]
      rw [← ENNReal.mul_inv (a := 2) (b := 2) (by simp) (by simp)]
      norm_num
    simpa only [hhalf] using ENNReal.sub_half (a := (1 / 2 : ℝ≥0∞)) (by norm_num)
  exact harith ▸ hbound

end PFunctorFork
