/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sampling
public import Cslib.Computability.PolynomialTime.Iteration
public import Cslib.Computability.PolynomialTime.List

/-!
# Bounded iteration with fresh private randomness

Each iteration draws a fixed-width block of independent bits. Sampling the entire tape first
preserves the joint result and oracle state, even when the step depends on earlier samples.
The deterministic loop compiler charges for splitting the tape and executing every step.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib PFunctor MeasureTheory ProbabilityTheory MultiTapeTM

/-- Execute a bounded loop from successive blocks of a saved private tape. -/
def iterateFromBlocks {State : Type} (step : State → Word → State) (bits : ℕ) :
    ℕ → Word → State → State
  | 0, _, state => state
  | count + 1, coins, state =>
    iterateFromBlocks step bits count (coins.drop bits) (step state (coins.take bits))

variable {Oracle S State : Type}
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace State]

omit [Countable S] in
/-- Presampling fixed-width blocks preserves adaptive bounded iteration. Unused bits have no
observable effect, and no sampling failure is introduced by preparing the tape. -/
theorem runKernel_iterateFromBlocks
    (oracle : Oracle → Word → Kernel S (Word × S))
    (step : State → Word → State) (bits count : ℕ) (initial : State) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((fun coins => iterateFromBlocks step bits count coins initial) <$>
        (List.replicate (bits * count) ()).mapM (fun _ => coin)) state =
      FreeM.runKernel (effectKernel oracle)
        ((List.replicate count ()).foldlM (fun current _ =>
          step current <$> (List.replicate bits ()).mapM (fun _ => coin)) initial) state := by
  induction count generalizing initial state with
  | zero => simp [iterateFromBlocks]
  | succ count ih =>
    rw [Nat.mul_succ, Nat.add_comm (bits * count) bits, List.replicate_add, List.mapM_append]
    simp only [map_bind, map_pure, List.replicate_succ, List.foldlM_cons, bind_map_left]
    apply FreeM.runKernel_bind_congr_of_canReturn
    intro word hword state
    have hlength : word.length = bits := by
      simpa using FreeM.length_of_canReturn_mapM (fun _ : Unit => coin) _ hword
    have htake (rest : Word) : (word ++ rest).take bits = word := by
      rw [← hlength, List.take_left]
    have hdrop (rest : Word) : (word ++ rest).drop bits = rest := by
      rw [← hlength, List.drop_left]
    simpa only [iterateFromBlocks, htake, hdrop, map_eq_pure_bind] using
      ih (step initial word) state

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace State] in
/-- An invariant and a polynomial size bound give one uniform machine for a randomized loop.
The step certificate covers the actual computation on each private block, including any explicit
failure value carried in the state. Only representation sizes remain as bounds on the loop. -/
theorem isPPT_iterate_sampleBits {α : Type} [Finite Oracle]
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {bits count : α → ℕ} {step : α → State → Word → State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPolyTime (pairEncoding input (pairEncoding stateEncoding wordEncoding))
      (fun pair => stateEncoding (step pair.1 pair.2.1 pair.2.2)))
    (invariant : α → ℕ → State → Prop) (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a index current coins, index < count a → invariant a index current →
      coins.length ≤ bits a → invariant a (index + 1) (step a current coins))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a index current, index ≤ count a → invariant a index current →
      (stateEncoding current).length ≤ size (input a).length) :
    IsPPT input stateEncoding (fun a =>
      (List.replicate (count a) ()).foldlM (fun current _ =>
        step a current <$> (List.replicate (bits a) ()).mapM (fun _ => coin (Oracle := Oracle)))
          (initial a)) := by
  let captured := pairEncoding input wordEncoding
  let loopState := pairEncoding wordEncoding stateEncoding
  let advance (a : α) (pair : Word × State) :=
    (pair.1.drop (bits a), step a pair.2 (pair.1.take (bits a)))
  have htrace (a : α) (coins : Word) (current : State) (index : ℕ) :
      ((advance a)^[index] (coins, current)).2 =
        iterateFromBlocks (step a) (bits a) index coins current := by
    induction index generalizing coins current with
    | zero => rfl
    | succ index ih =>
      simpa only [Function.iterate_succ_apply, advance, iterateFromBlocks] using
        ih (coins.drop (bits a)) (step a current (coins.take (bits a)))
  have ha := (isPolyTime_fst captured loopState).fst
  have hcoins := (isPolyTime_snd captured loopState).fst
  have hcurrent := (isPolyTime_snd captured loopState).snd
  have hb := hbits.comp_encoded ha
  have hcall := hstep.comp_encoded (ha.pair (hcurrent.pair (hcoins.take hb)))
  have hbody : IsPolyTime (pairEncoding captured loopState)
      (fun pair => loopState (advance pair.1.1 pair.2)) :=
    (hcoins.drop hb).pair hcall
  obtain ⟨c, d, hpoly⟩ := hsize
  have hloop := ((isPolyTime_snd input wordEncoding).pair
    (hinitial.comp_encoded (isPolyTime_fst input wordEncoding))).iterate_with_spec
    (step := fun pair st => advance pair.1 st)
    (hcount.comp_encoded (isPolyTime_fst input wordEncoding)) hbody
    (fun pair index st => st.1.length ≤ pair.2.length ∧ invariant pair.1 index st.2)
    (fun pair => ⟨le_rfl, hinit pair.1⟩)
    (by
      rintro pair index ⟨coins, current⟩ hi ⟨hlen, hinv⟩
      exact ⟨(by simpa only [advance, List.length_drop] using
        (Nat.sub_le coins.length (bits pair.1)).trans hlen),
        hpreserve pair.1 index current _ hi hinv (List.length_take_le _ _)⟩)
    (size := fun n => 2 * n + c * (n + 1) ^ d + 1) (by fun_prop)
    (by
      rintro pair index ⟨coins, current⟩ hi ⟨hlen, hinv⟩
      have hs := (hbound pair.1 index current hi hinv).trans (hpoly _)
      have hin : (input pair.1).length ≤ (captured pair).length := by
        simp only [captured, length_pairEncoding]
        omega
      have hc : pair.2.length ≤ (captured pair).length := by
        simp only [captured, length_pairEncoding, wordEncoding, Function.Embedding.refl_apply]
        omega
      have hp := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hin 1) d)
      simp only [captured, length_pairEncoding, wordEncoding,
        Function.Embedding.refl_apply] at hp ⊢
      dsimp only at hlen
      omega)
  have hcompiled := (isPPT_sampleBits_of_isPolyTime (Oracle := Oracle)
    (hbits.unary_mul hcount)).map_with
    (f := fun a coins => iterateFromBlocks (step a) (bits a) (count a) coins (initial a))
    (by simpa only [htrace] using hloop.1.snd)
  let : Countable State := stateEncoding.injective.countable
  let : MeasurableSpace State := ⊤
  apply hcompiled.congr
  intro a S _ _ _ oracle state
  exact runKernel_iterateFromBlocks oracle (step a) (bits a) (count a) (initial a) state

end Turing.MultiTapePTM
