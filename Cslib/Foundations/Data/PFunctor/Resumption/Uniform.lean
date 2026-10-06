/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Coin
public import Cslib.Foundations.Data.PFunctor.Resumption.Iterate

/-!
# Uniform sampling from fair coins

Free programs of coin flips sample uniformly only below powers of two. Rejection sampling samples
uniformly from every `Fin k` (`PFunctor.Resumption.toMeasure_uniformFin`): it reads
`Nat.log 2 k + 1` flips as a number below `2 ^ (Nat.log 2 k + 1)`, and starts again until the
number is below `k`. It returns almost surely, but no number of flips suffices on every run.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.Resumption

/-- Sample uniformly from `Fin k` by rejection: read `Nat.log 2 k + 1` coin flips as a number below
`2 ^ (Nat.log 2 k + 1)`, and start again until the number is below `k`. -/
def uniformFin (k : ℕ+) : Resumption coinOracle (Fin k) :=
  (fun x => Fin.ofNat k x.val) <$>
    repeatUntil (.mk ⟨⟩ (FreeM.bitsAfter · (Nat.log 2 k))) {x | x.val < k}

/-- Rejection sampling from fair coins is uniform. -/
theorem toMeasure_uniformFin (k : ℕ+) :
    (uniformFin k).toMeasure fairCoins = uniformOn Set.univ := by
  have hk : (k : ℕ) < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hbits : (FreeM.coin.bind (FreeM.bitsAfter · (Nat.log 2 k))).toMeasure fairCoins =
      uniformOn Set.univ := by
    rw [← FreeM.bits_succ]
    exact FreeM.toMeasure_bits _
  have hs : (FreeM.coin.bind (FreeM.bitsAfter · (Nat.log 2 k))).toMeasure fairCoins
      {x | x.val < k} ≠ 0 := by
    rw [hbits]
    exact (uniformOn_eq_zero_iff Set.finite_univ).not.mpr
      (Set.nonempty_iff_ne_empty.mp ⟨⟨0, by omega⟩, trivial, k.pos⟩)
  rw [uniformFin, toMeasure_map_of_discrete' fairCoins,
    toMeasure_repeatUntil (Obj.mk (P := coinOracle) ⟨⟩ (FreeM.bitsAfter · (Nat.log 2 k))) _
      fairCoins hs, Obj.fst_mk,
    Obj.snd_mk, ← FreeM.coin, hbits, uniformOn_univ_cond, uniformOn_map_of_bijOn]
  refine ⟨fun _ _ => trivial, fun x hx y hy hxy => ?_, fun y _ => ⟨⟨y.val, by omega⟩, y.isLt, ?_⟩⟩
  · simpa [Fin.ext_iff, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hxy
  · simp

/-- Rejection sampling from fair coins returns almost surely. -/
instance (k : ℕ+) : IsProbabilityMeasure ((uniformFin k).toMeasure fairCoins) := by
  rw [toMeasure_uniformFin]
  exact isProbabilityMeasure_uniformOn Set.finite_univ ⟨0, trivial⟩

end PFunctor.Resumption
