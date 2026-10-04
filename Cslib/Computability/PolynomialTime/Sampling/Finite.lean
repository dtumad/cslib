/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Sampling.Rejection
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.PolynomialTime.Encoding.Finite

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

end Turing.MultiTapePTM
