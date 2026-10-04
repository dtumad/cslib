/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Foundations.Data.PFunctor.Resumption.Uniform
public import Cslib.Foundations.Data.Nat.Bits
public import Cslib.Foundations.MeasureTheory.Uniform
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log

/-! # Finite sampling from random bits -/

@[expose] public section

namespace PFunctor.FreeM

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uA

variable {P : PFunctor.{uA, 0}}

/-- Sample a word using exactly one execution of `coin` per bit. -/
def sampleBits (coin : P.FreeM (Fin 2)) : (bits : ℕ) → P.FreeM (Fin (2 ^ bits))
  | 0 => pure 0
  | bits + 1 =>
    ((finProdFinEquiv.trans (finCongr (pow_succ 2 bits).symm)) :
      Fin (2 ^ bits) × Fin 2 ≃ Fin (2 ^ (bits + 1))) <$>
      (do
        let word ← sampleBits coin bits
        let bit ← coin
        pure (word, bit))

/-- Rejection sampling with a fixed attempt budget. Exhaustion returns `none`. -/
def sampleFin (coin : P.FreeM (Fin 2)) (n bits attempts : ℕ) : P.FreeM (Option (Fin n)) :=
  (Resumption.truncate attempts (Resumption.uniformFin n (2 ^ bits))).liftM
    (fun _ => sampleBits coin bits)

@[simp] theorem sampleFin_zero (coin : P.FreeM (Fin 2)) (n bits : ℕ) :
    sampleFin coin n bits 0 = pure none := by
  rw [sampleFin, Resumption.uniformFin, Resumption.repeatUntil_eq_query,
    Resumption.truncate_query_zero]
  rfl

/-- The next proposal either succeeds immediately or spends one attempt before retrying. -/
theorem sampleFin_succ (coin : P.FreeM (Fin 2)) (n bits attempts : ℕ) :
    sampleFin coin n bits (attempts + 1) = sampleBits coin bits >>= fun value =>
      (Resumption.acceptFin n value).elim (sampleFin coin n bits attempts) (pure ∘ some) := by
  conv_lhs => rw [sampleFin, Resumption.uniformFin, Resumption.repeatUntil_eq_query,
    Resumption.truncate_query_succ]
  change (sampleBits coin bits >>= fun value =>
    (Resumption.truncate attempts ((Resumption.acceptFin n value).elim
      (Resumption.uniformFin n (2 ^ bits)) Resumption.pure)).liftM
        (fun _ => sampleBits coin bits)) = _
  apply bind_congr
  intro value
  cases Resumption.acceptFin n value <;> simp [sampleFin]

/-- The numerical sample is the binary value of the sampled word, in sampling order.
The final sampled bit is the least significant bit. This equality is structural, before choosing
any interpretation of `coin`. -/
theorem val_sampleBits (coin : P.FreeM Bool) (bits : ℕ) :
    Fin.val <$> sampleBits ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin) bits =
      (fun word => Nat.ofBitsList word.reverse) <$>
        (List.replicate bits ()).mapM (fun _ => coin) := by
  induction bits with
  | zero => simp [sampleBits]
  | succ bits ih =>
    calc
      _ = (Fin.val <$> sampleBits ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
          bits) >>= fun n => coin >>= fun b => pure (Nat.bit b n) := by
        simp [sampleBits, bind_map_left, finProdFinEquiv, Nat.bit_val, Nat.add_comm]
      _ = _ := by
        rw [ih, List.replicate_succ', List.mapM_append]
        simp [bind_map_left, Nat.ofBitsList]

/-- A word uses at most its bit length times the cost of one coin. -/
theorem queryBound_sampleBits_le (coin : P.FreeM (Fin 2)) (bound : ℕ∞)
    (hcoin : queryBound coin ≤ bound) (bits : ℕ) :
    queryBound (sampleBits coin bits) ≤ bits * bound := by
  induction bits with
  | zero => simp [sampleBits]
  | succ bits ih =>
    apply (queryBound_map _ _).le.trans
    calc
      _ ≤ queryBound (sampleBits coin bits) + bound :=
        queryBound_bind_le _ _ bound fun word =>
          (queryBound_bind_le coin (fun bit => pure (word, bit)) 0 (fun _ => le_rfl)).trans
            (by simpa only [add_zero] using hcoin)
      _ ≤ (bits : ℕ∞) * bound + bound := add_le_add ih le_rfl
      _ = _ := by simp [add_mul]

/-- The bounded binary sampler charges at most `bits * attempts` coin executions. -/
theorem queryBound_sampleFin_le (coin : P.FreeM (Fin 2)) (bound : ℕ∞)
    (hcoin : queryBound coin ≤ bound) (n bits attempts : ℕ) :
    queryBound (sampleFin coin n bits attempts) ≤ attempts * bits * bound := by
  unfold sampleFin
  calc
    _ ≤ queryBound (Resumption.truncate attempts (Resumption.uniformFin n (2 ^ bits))) *
        ((bits : ℕ∞) * bound) :=
      queryBound_liftM_le _ _ (fun _ => queryBound_sampleBits_le coin bound hcoin bits) _
    _ ≤ (attempts : ℕ∞) * ((bits : ℕ∞) * bound) := by
      gcongr
      exact queryBound_truncate _ _
    _ = _ := (mul_assoc _ _ _).symm

variable [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  (μ : (op : P.A) → Measure (P.B op)) (coin : P.FreeM (Fin 2))
  (hcoin : denote μ coin = uniformOn Set.univ)

include hcoin

/-- Fair bits give an exactly uniform word, including the zero-bit word. -/
theorem denote_sampleBits (bits : ℕ) :
    denote μ (sampleBits coin bits) = uniformOn Set.univ := by
  induction bits with
  | zero =>
    apply Measure.ext_of_singleton
    intro x
    have hx : x = 0 := by omega
    simp [sampleBits, hx, uniformOn_univ]
  | succ bits ih =>
    rw [sampleBits, ← map_eq_map, denote_map _ _ _ Measurable.of_discrete]
    have hpair := denote_bind_bind_prod_mk μ (sampleBits coin bits) coin
    simp only [bind_eq_bind] at hpair
    rw [hpair, ih, hcoin, prod_uniformOn_univ, map_uniformOn_univ]

/-- Compiling proposals into actual coin flips preserves the complete result measure. -/
theorem denote_sampleFin (n bits attempts : ℕ) :
    denote μ (sampleFin coin n bits attempts) =
      denote (P := ⟨Unit, fun _ => Fin (2 ^ bits)⟩) (fun _ => uniformOn Set.univ)
        (Resumption.truncate attempts (Resumption.uniformFin n (2 ^ bits))) := by
  rw [sampleFin, denote_liftM]
  simp only [denote_sampleBits μ coin hcoin]

/-- The binary implementation has the same geometric failure probability as rejection sampling. -/
theorem denote_sampleFin_none (n bits attempts : ℕ) (h : n ≤ 2 ^ bits) :
    denote μ (sampleFin coin n bits attempts) {none} =
      (1 - (n : ℝ≥0∞) / 2 ^ bits) ^ attempts := by
  rw [denote_sampleFin μ coin hcoin, Resumption.denote_truncate_uniformFin_none h]
  simp

/-- Every returned value has its exact finite geometric weight. -/
theorem denote_sampleFin_some (n bits attempts : ℕ) (h : n ≤ 2 ^ bits) (a : Fin n) :
    denote μ (sampleFin coin n bits attempts) {some a} =
      (∑ j ∈ Finset.range attempts, (1 - (n : ℝ≥0∞) / 2 ^ bits) ^ j) / 2 ^ bits := by
  rw [denote_sampleFin μ coin hcoin]
  have hset : ({some a} : Set (Option (Fin n))) = some '' ({a} : Set (Fin n)) := by simp
  rw [hset, Resumption.denote_truncate_some (P := ⟨Unit, fun _ => Fin (2 ^ bits)⟩)
    _ _ _ _ (measurableSet_singleton _), Resumption.uniformFin,
    Resumption.outputMeasure_repeatUntil_apply (P := ⟨Unit, fun _ => Fin (2 ^ bits)⟩)
      _ _ _ _ _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  rw [Resumption.uniformOn_acceptFin_none h, Resumption.setOf_acceptFin_eq_some h, uniformOn_univ]
  simp [div_eq_mul_inv]

omit hcoin in
private theorem pow_clog_two_le_twice (n : ℕ) [NeZero n] : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  by_cases hn : n = 1
  · simp [hn]
  have hn' : 1 < n := by have := NeZero.ne n; omega
  have hk := Nat.clog_pos (by decide : 1 < 2) hn'
  calc
    _ = 2 ^ ((Nat.clog 2 n).pred + 1) :=
      congrArg (fun k => 2 ^ k) (Nat.succ_pred_eq_of_pos hk).symm
    _ = 2 ^ (Nat.clog 2 n).pred * 2 := pow_succ _ _
    _ ≤ n * 2 := Nat.mul_le_mul_right 2 (Nat.pow_pred_clog_lt_self (by decide) hn').le
    _ = _ := Nat.mul_comm _ _

/-- A proposal range at most twice the requested range gives geometric failure at rate `1/2`. -/
theorem denote_sampleFin_none_le_of_bounds (n bits attempts : ℕ)
    (hcover : n ≤ 2 ^ bits) (hsize : 2 ^ bits ≤ 2 * n) :
    denote μ (sampleFin coin n bits attempts) {none} ≤ (2 : ℝ≥0∞)⁻¹ ^ attempts := by
  rw [denote_sampleFin_none μ coin hcoin _ _ _ hcover]
  apply pow_le_pow_left'
  have hratio : (2 : ℝ≥0∞)⁻¹ ≤ (n : ℝ≥0∞) / 2 ^ bits := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
    rw [mul_comm, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)]
    exact_mod_cast (show 2 ^ bits ≤ n * 2 by simpa [Nat.mul_comm] using hsize)
  calc
    _ ≤ 1 - (2 : ℝ≥0∞)⁻¹ := tsub_le_tsub_left hratio 1
    _ = _ := by norm_num

/-- Using the bit length of the range, each extra attempt halves the failure bound. -/
theorem denote_sampleFin_none_le (n attempts : ℕ) [NeZero n] :
    denote μ (sampleFin coin n (Nat.clog 2 n) attempts) {none} ≤ (2 : ℝ≥0∞)⁻¹ ^ attempts :=
  denote_sampleFin_none_le_of_bounds μ coin hcoin n _ attempts
    (Nat.le_pow_clog (by decide) _) (pow_clog_two_le_twice n)

/-- The length of the binary bound is also a suitable proposal width, including at powers of two. -/
theorem denote_sampleFin_size_none_le (n attempts : ℕ) [NeZero n] :
    denote μ (sampleFin coin n n.size attempts) {none} ≤ (2 : ℝ≥0∞)⁻¹ ^ attempts :=
  denote_sampleFin_none_le_of_bounds μ coin hcoin n _ attempts
    (Nat.lt_size_self n).le (Nat.two_pow_size_le_twice n (Nat.pos_of_ne_zero (NeZero.ne n)))

end PFunctor.FreeM
