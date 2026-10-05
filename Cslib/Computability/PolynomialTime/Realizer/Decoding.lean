/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding.Decoding
public import Cslib.Computability.PolynomialTime.Realizer.CoinTape

/-!
# Recovering typed results from a chosen machine

Checked decoding rejects timeout and malformed output. A realization certificate proves that
neither can occur, even with adversarial oracle replies. The saved-tape form keeps the private
randomness explicit and preserves every source postcondition on every sufficiently long tape.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Realizer

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  {input : α ↪ Word} {output : Computability.Encoding β Bool}
  {program : α → (effects Oracle).FreeM β}
  (implementation : Realizer input output.toEmbedding program)

/-- Run the chosen machine and check its output representation. -/
def runDecoded (a : α) : (effects Oracle).FreeM (Option β) :=
  (fun result => result.bind output.decodeChecked) <$> implementation.run a

/-- Decode a machine execution with an explicit private tape. -/
def runDecodedFromCoins (a : α) (coins : Word) : (effects Oracle).FreeM (Option β) :=
  (fun result => result.bind output.decodeChecked) <$> implementation.runFromCoins a coins

/-- Every returned decoded result is a source result. Timeout and malformed output are
impossible for a realizing machine, without making any assumption on oracle replies. -/
theorem canReturn_runDecoded_iff (a : α) (result : Option β) :
    MonadAttach.CanReturn (implementation.runDecoded a) result ↔
      ∃ value, MonadAttach.CanReturn (program a) value ∧ some value = result := by
  rw [runDecoded, ← FreeM.map_eq_map, FreeM.canReturn_map]
  simp only [implementation.canReturn_run_iff]
  constructor
  · rintro ⟨word, ⟨value, hvalue, rfl⟩, h⟩
    exact ⟨value, hvalue, by simpa using h⟩
  · rintro ⟨value, hvalue, rfl⟩
    exact ⟨some (output.encode value), ⟨value, hvalue, rfl⟩, by simp⟩

/-- Keeping the private tape fixed still preserves structural source postconditions. -/
theorem canReturn_runDecodedFromCoins (a : α) (coins : Word)
    (hlen : coins.length = implementation.clock (input a).length) (result : Option β)
    (hresult : MonadAttach.CanReturn (implementation.runDecodedFromCoins a coins) result) :
    ∃ value, MonadAttach.CanReturn (program a) value ∧ some value = result := by
  obtain ⟨word, hword, hresult⟩ := (FreeM.canReturn_map _ _ _).mp hresult
  obtain ⟨value, hvalue, rfl⟩ := implementation.canReturn_runFromCoins a coins hlen word hword
  exact ⟨value, hvalue, by simpa using hresult⟩

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Typed decoding preserves the whole joint output-and-state measure. -/
theorem runKernel_runDecoded (a : α) {S : Type}
    [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S)) (state : S) :
    FreeM.runKernel (effectKernel oracle) (implementation.runDecoded a) state =
      FreeM.runKernel (effectKernel oracle) (some <$> program a) state := by
  let : Countable β := output.encode_injective.countable
  rw [runDecoded, ← FreeM.map_eq_map, FreeM.runKernel_map, implementation.runKernel_run]
  simp only [← FreeM.map_eq_map, FreeM.runKernel_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Computability.Encoding.toEmbedding_apply, Option.bind_some,
    Computability.Encoding.decodeChecked_encode]

/-- Presampling and then decoding retains the source's joint observation. The same explicit
tape can subsequently be reused, rather than independently resampling a second run. -/
theorem runKernel_sample_runDecodedFromCoins (a : α) {S : Type}
    [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S)) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => coin) >>=
        implementation.runDecodedFromCoins a) state =
      FreeM.runKernel (effectKernel oracle) (some <$> program a) state := by
  let : Countable β := output.encode_injective.countable
  unfold runDecodedFromCoins
  rw [← map_bind]
  rw [← FreeM.map_eq_map, FreeM.runKernel_map, implementation.runKernel_sample_runFromCoins,
    ← implementation.runKernel_run]
  simpa only [runDecoded, ← FreeM.map_eq_map, FreeM.runKernel_map] using
    implementation.runKernel_runDecoded a oracle state

end Turing.MultiTapePTM.Realizer
