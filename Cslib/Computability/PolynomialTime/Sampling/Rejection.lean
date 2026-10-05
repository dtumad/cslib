/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sampling
public import Cslib.Computability.PolynomialTime.Sampling.Iteration
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
      exact runKernel_sampleBits_const oracle _ _ state
    · simp only [h, ↓reduceIte]
      simpa only [← map_eq_pure_bind] using ih state

/-- Discarding a bounded sample, including exhaustion, leaves the shared state unchanged. -/
theorem runKernel_sampleFin_const
    (oracle : Oracle → Word → Kernel S (Word × S)) (bound bits attempts : ℕ)
    (program : (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      (FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
        bound bits attempts >>= fun _ => program) state =
      FreeM.runKernel (effectKernel oracle) program state := by
  have h := congrArg (fun measure => measure.bind
      (fun out : Option ℕ × S => FreeM.runKernel (effectKernel oracle) program out.2))
    (runKernel_selectBelow oracle bound bits attempts state)
  rw [← FreeM.runKernel_bind _ _ (fun _ => program) state,
    ← FreeM.runKernel_bind _ _ (fun _ => program) state] at h
  simp only [FreeM.bind_eq_bind, bind_map_left] at h
  exact h.symm.trans (runKernel_sampleBits_const oracle _ program state)

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

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
private theorem foldlM_sample {m : Type → Type*} [Monad m] [LawfulMonad m] {β : Type}
    (draw : m β) (count : ℕ) (values : List β) :
    (List.replicate count ()).foldlM (fun values _ =>
      (fun value => values ++ [value]) <$> draw) values =
        (fun rest => values ++ rest) <$> (List.replicate count ()).mapM (fun _ => draw) := by
  induction count generalizing values with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, List.foldlM_cons, List.mapM_cons, bind_map_left, ih,
      map_bind, map_pure, List.append_assoc, List.singleton_append]
    simp only [map_eq_pure_bind]

omit [MeasurableSpace α] in
/-- Prepare a polynomial number of independent bounded samples. Every slot is sampled, and
its possible exhaustion is retained; callers can reject the whole tape if any slot failed. -/
theorem isPPT_replicate_sampleFin {input : α ↪ Word} {bound bits attempts count : α → ℕ}
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a))) :
    IsPPT (Oracle := Oracle) input (listEncoding (optionEncoding binaryEncoding)) (fun a =>
      (List.replicate (count a) ()).mapM (fun _ =>
        Option.map Fin.val <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            (bound a) (bits a) (attempts a))) := by
  let output := listEncoding (optionEncoding binaryEncoding)
  let step a (values : List (Option ℕ)) (coins : Word) :=
    values ++ [selectBelow (bound a) (bits a) (attempts a) coins]
  let encoding := pairEncoding input (pairEncoding output wordEncoding)
  have hi := isPolyTime_input encoding
  have hdraw := (hbound.comp_encoded hi.fst).selectBelow
    (hbits.comp_encoded hi.fst) (hattempts.comp_encoded hi.fst) hi.snd.snd
  have hstep : IsPolyTime encoding (fun arg => output (step arg.1 arg.2.1 arg.2.2)) :=
    hi.snd.fst.list_append
      (hdraw.list_cons (rest := fun _ => []) (isPolyTime_const encoding []))
  obtain ⟨cb, db, hb⟩ := hbits.length_le
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hb hc
  have hloop := isPPT_iterate_sampleBits (Oracle := Oracle) (stateEncoding := output)
    (initial := fun _ : α => []) (step := step) (isPolyTime_const input [])
    (hbits.unary_mul hattempts) hcount hstep
    (fun a index values => (output values).length ≤ index * (2 * (bits a + 1) + 1))
    (fun _ => by simp [output]) (by
      intro a index values coins _ hvalues _
      have hdraw := length_selectBelow_le (bound a) (bits a) (attempts a) coins
      simp only [step, output, listEncoding_append, List.length_append, listEncoding_cons,
        length_pairEncoding, listEncoding_nil, List.length_nil, Nat.add_zero]
      dsimp only [output] at hvalues
      nlinarith)
    (size := fun n => cc * (n + 1) ^ dc * (2 * (cb * (n + 1) ^ db + 1) + 1))
    (by fun_prop) (by
      intro a index values hindex hvalues
      refine hvalues.trans (Nat.mul_le_mul (hindex.trans (hc a)) ?_)
      have := hb a
      omega)
  let : MeasurableSpace (List (Option ℕ)) := ⊤
  apply hloop.congr
  intro a S _ _ _ oracle state
  have hstepRun current : step a current <$>
      (List.replicate (bits a * attempts a) ()).mapM (fun _ => coin (Oracle := Oracle)) =
      (fun value => current ++ [value]) <$>
        (selectBelow (bound a) (bits a) (attempts a) <$>
          (List.replicate (bits a * attempts a) ()).mapM (fun _ => coin)) := by
    rw [Functor.map_map]
  simp only [hstepRun]
  rw [foldlM_sample]
  simp only [List.nil_append, id_map']
  have hkernel (count : ℕ) (state : S) :
      FreeM.runKernel (effectKernel oracle)
        ((List.replicate count ()).mapM (fun _ =>
          selectBelow (bound a) (bits a) (attempts a) <$>
            (List.replicate (bits a * attempts a) ()).mapM (fun _ => coin))) state =
      FreeM.runKernel (effectKernel oracle)
        ((List.replicate count ()).mapM (fun _ =>
          Option.map Fin.val <$>
            FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
              (bound a) (bits a) (attempts a))) state := by
    induction count generalizing state with
    | zero => rfl
    | succ count ih =>
      simp only [List.replicate_succ, List.mapM_cons, ← FreeM.bind_eq_bind]
      rw [FreeM.runKernel_bind, FreeM.runKernel_bind, runKernel_selectBelow]
      apply Measure.bind_congr_right
      refine Filter.Eventually.of_forall fun out => ?_
      simp only [FreeM.bind_eq_bind, ← map_eq_pure_bind, ← FreeM.map_eq_map,
        FreeM.runKernel_map]
      exact congrArg (Measure.map (fun value => (out.1 :: value.1, value.2))) (ih out.2)
  exact hkernel (count a) state

end Turing.MultiTapePTM
