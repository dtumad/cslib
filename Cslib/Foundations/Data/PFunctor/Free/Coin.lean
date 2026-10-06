/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Uniform

/-!
# Coin flips

`PFunctor.coinOracle` has a single operation, flipping a coin, answered by a bit, and
`PFunctor.FreeM.coin` flips it. When every flip is answered by a fair coin (`PFunctor.fairCoins`),
`j` flips read as a number are uniform below `2 ^ j` (`PFunctor.FreeM.toMeasure_bits`). Free
programs of flips reach only dyadic probabilities; sampling uniformly below other bounds needs
rejection sampling, as a resumption.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PFunctor

/-- Coin flips: a single operation, answered by a bit. -/
abbrev coinOracle : PFunctor.{0, 0} := purePower Bool

/-- Answer every coin flip with a fair coin. -/
noncomputable abbrev fairCoins (a : coinOracle.A) : Measure (coinOracle.B a) :=
  uniformOn Set.univ

namespace FreeM

/-- Flip a coin. -/
def coin : coinOracle.FreeM Bool := lift (P := coinOracle) ⟨⟩

@[simp]
theorem toMeasure_coin : coin.toMeasure fairCoins = uniformOn Set.univ :=
  toMeasure_lift _ _

/-- Read a bit followed by a number below `2 ^ j` as a number below `2 ^ (j + 1)`, the bit being
the most significant. -/
def consBit (j : ℕ) : Bool × Fin (2 ^ j) ≃ Fin (2 ^ (j + 1)) :=
  (finTwoEquiv.symm.prodCongr (.refl _)).trans
    (finProdFinEquiv.trans (finCongr (pow_succ' 2 j).symm))

/-- Flip `j` coins and read them as a number below `2 ^ j`, the first flip being the most
significant bit. -/
def bits : (j : ℕ) → coinOracle.FreeM (Fin (2 ^ j))
  | 0 => pure 0
  | j + 1 => coin >>= fun b => (fun v => consBit j (b, v)) <$> bits j

/-- Flip `j` coins after the bit `b`, and read all of them as a number below `2 ^ (j + 1)`. -/
def bitsAfter (b : Bool) (j : ℕ) : coinOracle.FreeM (Fin (2 ^ (j + 1))) :=
  (fun v => consBit j (b, v)) <$> bits j

theorem bits_succ (j : ℕ) : bits (j + 1) = coin.bind (bitsAfter · j) := rfl

/-- `j` fair coins read as a number are uniform below `2 ^ j`. -/
theorem toMeasure_bits (j : ℕ) : (bits j).toMeasure fairCoins = uniformOn Set.univ := by
  induction j with
  | zero =>
    refine Measure.ext_of_singleton fun x => ?_
    obtain rfl := Subsingleton.elim (α := Fin 1) x 0
    simp [bits, uniformOn_univ]
  | succ j ih =>
    have : bits (j + 1) = consBit j <$> (coin >>= fun b => (b, ·) <$> bits j) := by
      simp [bits]
    rw [this, toMeasure_map_of_discrete' fairCoins, coin, toMeasure_lift_bind' fairCoins]
    simp only [toMeasure_map_of_discrete' fairCoins, ih]
    rw [uniformOn_univ_bind_map_prodMk, uniformOn_univ_map_equiv]

end FreeM

end PFunctor
