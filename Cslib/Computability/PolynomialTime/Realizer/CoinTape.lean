/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Realizer
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Measure

/-!
# Explicit private tapes for uniform realizers

The chosen machine can run with a supplied private tape. Sampling that tape up front preserves
the original program's whole joint output-and-oracle-state measure. Forking this saved-tape
program keeps the private tape fixed; oracle randomness remains in the visible operations.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Realizer

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  {input : α ↪ Word} {output : β ↪ Word} {program : α → (effects Oracle).FreeM β}
  (implementation : Realizer input output program)

/-- Execute the chosen machine using the supplied private tape and the original oracle names. -/
def runFromCoins (a : α) (coins : Word) : (effects Oracle).FreeM (Option Word) :=
  (output? <$> implementation.machine.runConfigFromCoins query coins
    (implementation.machine.initialConfig (input a))).liftM (rename implementation.dispatch)

/-- Every saved-tape execution is an execution of the same machine and transition clock. -/
theorem canReturn_run_of_coins (a : α) (coins : Word)
    (hlen : coins.length = implementation.clock (input a).length) (result : Option Word)
    (hresult : MonadAttach.CanReturn (implementation.runFromCoins a coins) result) :
    MonadAttach.CanReturn (implementation.run a) result := by
  rw [runFromCoins, canReturn_liftM_rename] at hresult
  rw [run, canReturn_liftM_rename]
  obtain ⟨final, hfinal, hresult⟩ := (FreeM.canReturn_map _ _ _).mp hresult
  apply (FreeM.canReturn_map _ _ _).mpr
  exact ⟨final, hlen ▸ canReturn_runConfigFrom_of_coins implementation.machine coins _ final hfinal,
    hresult⟩

/-- Fixing the entire private tape preserves structural specifications and cannot time out.
The tape need not be random for this pathwise statement. -/
theorem canReturn_runFromCoins (a : α) (coins : Word)
    (hlen : coins.length = implementation.clock (input a).length) (result : Option Word)
    (hresult : MonadAttach.CanReturn (implementation.runFromCoins a coins) result) :
    ∃ value, MonadAttach.CanReturn (program a) value ∧ some (output value) = result :=
  (implementation.canReturn_run_iff a result).mp
    (implementation.canReturn_run_of_coins a coins hlen result hresult)

/-- Presampling the witness's private tape preserves its complete joint observation, including
the state of any oracle that logs requests or answers. This is a single-run marginal law;
the fixed tape is explicit data when forming a two-run coupling. -/
theorem runKernel_sample_runFromCoins (a : α) {S : Type}
    [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S)) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => coin) >>=
        implementation.runFromCoins a) state =
      FreeM.runKernel (effectKernel oracle) ((fun value => some (output value)) <$> program a)
        state := by
  let native := (List.replicate (implementation.clock (input a).length) ()).mapM
    (fun _ => coin (Oracle := Fin implementation.ports)) >>= fun coins =>
      output? <$> implementation.machine.runConfigFromCoins query coins
        (implementation.machine.initialConfig (input a))
  calc
    _ = FreeM.runKernel (effectKernel oracle)
        (native.liftM (rename implementation.dispatch)) state := by
      simp only [native, FreeM.liftM_bind, liftM_rename_sampleBits]
      rfl
    _ = FreeM.runKernel (effectKernel (fun port => oracle (implementation.dispatch port)))
        native state := runKernel_liftM_rename _ _ _ _
    _ = FreeM.runKernel (effectKernel (fun port => oracle (implementation.dispatch port)))
        (implementation.machine.run (implementation.clock (input a).length) (input a)) state := by
      simpa only [native, Turing.MultiTapePTM.run, runFrom, map_eq_pure_bind] using
        (runKernel_runConfigFromCoins implementation.machine
          (fun port => oracle (implementation.dispatch port))
          (implementation.clock (input a).length)
          (implementation.machine.initialConfig (input a)) (fun final => pure (output? final))
          state).symm
    _ = _ := implementation.realizes a S oracle state

end Turing.MultiTapePTM.Realizer
