/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sampling.Rejection
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.PolynomialTime.Encoding.Finite
public import Cslib.Computability.PolynomialTime.Option

/-! # Uniform sampling in indexed finite types -/

public section

namespace Turing.MultiTapePTM

open Cslib PFunctor MultiTapeTM

variable {Oracle α : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Retain the input with a bounded sample from an indexed finite type. The equivalence chooses
the binary representation; the same sampling machine works for every input and range. -/
theorem isPPT_sampleFin_equiv {input : α ↪ Word} {β : α → Type} {bound attempts : α → ℕ}
    (equiv : ∀ a, β a ≃ Fin (bound a))
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a))) :
    IsPPT (Oracle := Oracle) input
      (sigmaEncoding input (fun a => optionEncoding (finEquivEncoding (equiv a))))
      (fun a => (fun result => ⟨a, result.map (equiv a).symm⟩) <$>
        FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
          (bound a) (bound a).size (attempts a)) := by
  apply isPPT_map_encoding_iff.mp
  have h := ((isPPT_sampleFin_size (Oracle := Oracle) hbound hattempts).pair
    (isPolyTime_input input))
  apply isPPT_map_encoding_iff.mpr at h
  convert h using 1
  funext a
  simp only [← comp_map, Function.comp_def]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some value => simp [sigmaEncoding, pairEncoding_apply, finEquivEncoding_apply]

/-- Sample a complete tape in an indexed finite type and reject it if any slot failed.
The input is retained so that subsequent computation can use its indexed representation. -/
theorem isPPT_replicate_sampleFin_equiv {input : α ↪ Word} {β : α → Type}
    {bound attempts count : α → ℕ} (equiv : ∀ a, β a ≃ Fin (bound a))
    (hbound : IsPolyTime input (fun a => binaryEncoding (bound a)))
    (hattempts : IsPolyTime input (fun a => unaryEncoding (attempts a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a))) :
    IsPPT (Oracle := Oracle) input
      (sigmaEncoding input (fun a => optionEncoding (listEncoding (finEquivEncoding (equiv a)))))
      (fun a => (fun results => ⟨a, (results.mapM id).map (List.map (equiv a).symm)⟩) <$>
        (List.replicate (count a) ()).mapM (fun _ =>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            (bound a) (bound a).size (attempts a))) := by
  have hsample := isPPT_replicate_sampleFin (Oracle := Oracle)
    hbound hbound.binary_size hattempts hcount
  have hcollect := hsample.map
    (isPolyTime_input (listEncoding (optionEncoding binaryEncoding))).list_sequence
  have h := isPPT_map_encoding_iff.mpr (hcollect.pair (isPolyTime_input input))
  apply isPPT_map_encoding_iff.mp
  convert h using 1
  funext a
  have hmap {γ δ : Type} (f : γ → δ) (draw : (effects Oracle).FreeM γ) (count : ℕ) :
      (List.replicate count ()).mapM (fun _ => f <$> draw) =
        List.map f <$> (List.replicate count ()).mapM (fun _ => draw) := by
    induction count with
    | zero => rfl
    | succ count ih =>
      simp only [List.replicate_succ, List.mapM_cons, ih, bind_map_left, map_bind,
        map_pure, List.map_cons]
  simp only [hmap, ← comp_map, Function.comp_def]
  congr 1
  funext results
  have heq (results : List (Option (Fin (bound a)))) :
      optionEncoding (listEncoding (finEquivEncoding (equiv a)))
        ((results.mapM id).map (List.map (equiv a).symm)) =
      optionEncoding (listEncoding binaryEncoding)
        ((results.map (Option.map Fin.val)).mapM id) := by
    induction results with
    | nil => rfl
    | cons value results ih =>
      cases value with
      | none => simp
      | some value =>
        simp only [List.map_cons, Option.map_some, List.mapM_cons, id_eq]
        cases hrest : results.mapM id with
        | none =>
          simp only [hrest, Option.map_none, optionEncoding_none] at ih ⊢
          cases hother : (results.map (Option.map Fin.val)).mapM id <;> simp_all
        | some rest =>
          simp only [hrest, Option.map_some] at ih ⊢
          cases hother : (results.map (Option.map Fin.val)).mapM id <;>
            simp_all [optionEncoding, listEncoding_cons, pairEncoding_apply,
              finEquivEncoding_apply]
  exact congrArg (List.BitPair.encode (input a)) (heq results)

end Turing.MultiTapePTM
