/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot

/-!
# Sampling private machine coins in advance

Replaying a uniformly sampled tape has the same joint result-and-oracle-state measure as
sampling each coin at its transition. Unused coins after halting are discarded. Oracle calls
retain their adaptive order and share their original state throughout.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor MeasureTheory ProbabilityTheory

variable {k : ℕ} {State Oracle S α : Type} [DecidableEq Oracle] {input : List Bool}
  [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S] [MeasurableSpace α]

/-- Sampling a saved tape before execution preserves every observation of the final configuration.
Configurations themselves need no measurable structure or countability hypothesis. -/
theorem runKernel_runConfigFromCoins
    (machine : MultiTapePTM k Bool State Oracle)
    (oracle : Oracle → List Bool → Kernel S (List Bool × S)) (fuel : ℕ)
    (cfg : Config k Bool State Oracle input)
    (observe : Config k Bool State Oracle input → (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle) (machine.runConfigFrom fuel cfg >>= observe) state =
      FreeM.runKernel (effectKernel oracle)
        ((List.replicate fuel ()).mapM (fun _ => coin) >>= fun coins =>
          machine.runConfigFromCoins query coins cfg >>= observe) state := by
  induction fuel generalizing cfg state with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runConfigFrom_halted _ _ _ hs, runConfigFromCoins_halted _ _ _ _ hs, pure_bind]
      exact (runKernel_sampleBits_const oracle _ _ _).symm
    | some q =>
      simp only [runConfigFrom, step, hs, bind_assoc, List.replicate_succ,
        List.mapM_cons, pure_bind]
      rw [runKernel_coin_bind, runKernel_coin_bind]
      apply Measure.bind_congr_right
      refine Filter.Eventually.of_forall fun bit => ?_
      cases ha : machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simpa only [runConfigFromCoins, hs, ha, pure_bind] using
          ih (cfg.step action symbol move) state
      | query port next =>
        simp only [runConfigFromCoins, hs, ha, bind_assoc]
        rw [← runKernel_sampleBits_comm]
        conv_lhs => rw [← FreeM.bind_eq_bind, FreeM.runKernel_bind]
        conv_rhs => rw [← FreeM.bind_eq_bind, FreeM.runKernel_bind]
        apply Measure.bind_congr_right
        exact Filter.Eventually.of_forall fun out => ih (cfg.receive port next out.1) out.2

/-- The finite saved-tape interpreter preserves the original machine's completed-output measure,
including timeout and the final shared oracle state. -/
theorem runKernel_runSnapshotFromCoins
    (machine : MultiTapePTM k Bool State Oracle)
    (oracle : Oracle → List Bool → Kernel S (List Bool × S)) (fuel : ℕ)
    (snapshot : Snapshot k Bool State Oracle) (cfg : Config k Bool State Oracle input)
    (h : snapshot.Represents cfg) (state : S) :
    FreeM.runKernel (effectKernel oracle) (machine.runFrom fuel cfg) state =
      FreeM.runKernel (effectKernel oracle)
        ((List.replicate fuel ()).mapM (fun _ => coin) >>= fun coins =>
          (fun final => if final.state.isNone then some final.output else none) <$>
            machine.runSnapshotFromCoins input query coins snapshot) state := by
  simp only [runFrom, map_eq_pure_bind]
  rw [runKernel_runConfigFromCoins]
  apply congrArg (fun program => FreeM.runKernel (effectKernel oracle) program state)
  apply bind_congr
  intro coins
  simpa only [map_eq_pure_bind] using
    (runSnapshotFromCoins_output machine query coins snapshot cfg h).symm

end Turing.MultiTapePTM
