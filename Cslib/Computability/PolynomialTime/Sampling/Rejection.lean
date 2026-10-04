/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sampling
public import Cslib.Computability.PolynomialTime.Rejection
public import Cslib.Foundations.Data.PFunctor.Free.Random

/-!
# Uniform machine certificates for bounded rejection sampling

Draw the complete polynomial-length random tape, then inspect its blocks with the certified
binary selector. Unused private randomness has no effect on the joint result-and-oracle-state
kernel. The implementation therefore realizes the existing `FreeM.sampleFin`, including failure.
-/

public section

namespace Turing.MultiTapePTM

open Cslib PFunctor MeasureTheory ProbabilityTheory MultiTapeTM

variable {Oracle S α : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S] [MeasurableSpace α]

private theorem runKernel_mapM_coin_const
    (oracle : Oracle → Word → Kernel S (Word × S)) (bits : ℕ)
    (program : (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((List.replicate bits ()).mapM (fun _ => coin) >>= fun _ => program) state =
      FreeM.runKernel (effectKernel oracle) program state := by
  induction bits with
  | zero => simp
  | succ bits ih =>
    simp only [List.replicate_succ, List.mapM_cons, bind_assoc, pure_bind]
    rw [runKernel_coin_bind]
    simp only [ih, Measure.bind_const, measure_univ, one_smul]

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
private theorem val_sampleFin_succ (coin : (effects Oracle).FreeM Bool)
    (bound bits attempts : ℕ) :
    Option.map Fin.val <$>
      FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
        bound bits (attempts + 1) =
      (List.replicate bits ()).mapM (fun _ => coin) >>= fun word =>
        if Nat.ofBitsList word.reverse < bound then pure (some (Nat.ofBitsList word.reverse))
        else Option.map Fin.val <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            bound bits attempts := by
  let next (value : ℕ) : (effects Oracle).FreeM (Option ℕ) :=
    if value < bound then pure (some value) else
      Option.map Fin.val <$>
        FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
          bound bits attempts
  calc
    _ = (Fin.val <$>
        FreeM.sampleBits ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin) bits) >>=
        next := by
      rw [FreeM.sampleFin_succ]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro value
      by_cases hv : value.val < bound <;> simp [next, Resumption.acceptFin, hv]
    _ = _ := by rw [FreeM.val_sampleBits]; simp [bind_map_left, next]

/-- Sampling the whole random tape first realizes the same bounded rejection program.
The equality retains every shared oracle state, even though these programs make no oracle calls. -/
theorem runKernel_selectBelow
    (oracle : Oracle → Word → Kernel S (Word × S)) (bound bits attempts : ℕ) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      (selectBelow bound bits attempts <$>
        (List.replicate (bits * attempts) ()).mapM (fun _ => coin)) state =
      FreeM.runKernel (effectKernel oracle)
        (Option.map Fin.val <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            bound bits attempts) state := by
  induction attempts generalizing state with
  | zero => simp [selectBelow]
  | succ attempts ih =>
    rw [val_sampleFin_succ, Nat.mul_succ, Nat.add_comm (bits * attempts) bits,
      List.replicate_add, List.mapM_append]
    simp only [map_bind, map_pure]
    apply FreeM.runKernel_bind_congr_of_canReturn
    intro word hword state
    have hlength : word.length = bits := by
      simpa using FreeM.length_of_canReturn_mapM (fun _ : Unit => coin) _ hword
    have htake (rest : Word) : (word ++ rest).take bits = word := by
      rw [← hlength, List.take_left]
    have hdrop (rest : Word) : (word ++ rest).drop bits = rest := by
      rw [← hlength, List.drop_left]
    simp only [selectBelow, htake, hdrop]
    by_cases h : Nat.ofBitsList word.reverse < bound
    · simp only [h, ↓reduceIte]
      exact runKernel_mapM_coin_const oracle _ _ state
    · simp only [h, ↓reduceIte]
      simpa only [← map_eq_pure_bind] using ih state

variable [Finite Oracle]

omit [MeasurableSpace α] in
/-- A binary range and polynomial unary width and attempt budget suffice for one uniform machine.
The certificate includes tape generation, binary comparisons, selection, and output encoding. -/
theorem isPPT_sampleFin {input : α ↪ Word} {bound bits attempts : α → ℕ}
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a))) :
    IsPPT (Oracle := Oracle) input (optionEncoding binaryEncoding) (fun a =>
      Option.map Fin.val <$>
        FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
          (bound a) (bits a) (attempts a)) := by
  have hsampler := isPPT_sampleBits_of_isPolyTime (Oracle := Oracle)
    (hbits.unary_mul hattempts)
  have hinput := isPolyTime_fst input wordEncoding
  have heval := (hbound.comp_encoded hinput).selectBelow
    (hbits.comp_encoded hinput) (hattempts.comp_encoded hinput)
    (isPolyTime_snd input wordEncoding)
  have hcompiled := hsampler.map_with (output := optionEncoding binaryEncoding)
    (f := fun a word => selectBelow (bound a) (bits a) (attempts a) word) heval
  apply hcompiled.congr
  intro a S _ _ _ oracle state
  exact runKernel_selectBelow oracle (bound a) (bits a) (attempts a) state

omit [MeasurableSpace α] in
/-- The proposal width can be computed from the binary range itself. -/
theorem isPPT_sampleFin_size {input : α ↪ Word} {bound attempts : α → ℕ}
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a))) :
    IsPPT (Oracle := Oracle) input (optionEncoding binaryEncoding) (fun a =>
      Option.map Fin.val <$>
        FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
          (bound a) (bound a).size (attempts a)) :=
  isPPT_sampleFin hbound hbound.binary_size hattempts

end Turing.MultiTapePTM
