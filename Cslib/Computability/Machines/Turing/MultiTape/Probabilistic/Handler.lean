/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Snapshot
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure

/-! # Executing oracle handlers with fresh private randomness -/

@[expose] public section

namespace Turing.MultiTapePTM

open PFunctor MultiTapeMachine MeasureTheory ProbabilityTheory

variable {Oracle Target α : Type}

/-- Substitute implementations for named requests while preserving native private coins. -/
def oracleHandler (handler : Oracle → List Bool → (effects Target).FreeM (List Bool))
    (op : (effects Oracle).A) : (effects Target).FreeM ((effects Oracle).B op) :=
  match op with
  | .inl _ => coin
  | .inr (port, request) => handler port request

@[simp] theorem liftM_oracleHandler_coin
    (handler : Oracle → List Bool → (effects Target).FreeM (List Bool)) :
    (coin (Oracle := Oracle)).liftM (oracleHandler handler) = coin :=
  FreeM.liftM_lift _ _

@[simp] theorem liftM_oracleHandler_query
    (handler : Oracle → List Bool → (effects Target).FreeM (List Bool))
    (port : Oracle) (request : List Bool) :
    (query port request).liftM (oracleHandler handler) = handler port request :=
  FreeM.liftM_lift _ _

variable [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
  {S : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace α]

/-- Substitution retains the complete interaction with the remaining shared oracle state. -/
theorem runKernel_liftM_oracleHandler
    (oracle : Target → List Bool → Kernel S (List Bool × S))
    (handler : Oracle → List Bool → (effects Target).FreeM (List Bool))
    (program : (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle) (program.liftM (oracleHandler handler)) state =
      FreeM.runKernel (effectKernel (fun port request =>
        FreeM.runKernel (effectKernel oracle) (handler port request))) program state := by
  rw [FreeM.runKernel_liftM]
  congr 2
  funext op
  cases op with
  | inl token =>
    ext state : 1
    exact FreeM.runKernel_lift (effectKernel oracle) (.inl ()) state
  | inr request => rfl

variable {k : ℕ} {State : Type} [DecidableEq Oracle]

/-- One deterministic transition uses a leading machine coin and the remaining block for the
selected handler. Unused handler bits are discarded on ordinary transitions and after halting. -/
def stepWithRandomness (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → List Bool → List Bool)
    (snapshot : Snapshot k Bool State Oracle) (coins : List Bool) :
    Snapshot k Bool State Oracle :=
  Id.run (machine.stepSnapshot input (fun port request => pure (handler port request coins.tail))
    (coins.headD false) snapshot)

/-- Fixed-width independent blocks implement the original adaptive oracle execution. The
observation may depend on the whole reached snapshot, so this law also applies before halting. -/
theorem runKernel_stepWithRandomness [Countable S]
    (machine : MultiTapePTM k Bool State Oracle) (input : List Bool)
    (handler : Oracle → List Bool → List Bool → List Bool) (bits fuel : ℕ)
    (oracle : Target → List Bool → Kernel S (List Bool × S))
    (snapshot : Snapshot k Bool State Oracle) (cfg : Config k Bool State Oracle input)
    (h : snapshot.Represents cfg)
    (observeSnapshot : Snapshot k Bool State Oracle → (effects Target).FreeM α)
    (observeConfig : Config k Bool State Oracle input → (effects Target).FreeM α)
    (hobserve : ∀ snapshot cfg, snapshot.Represents cfg →
      observeSnapshot snapshot = observeConfig cfg) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      ((List.replicate fuel ()).foldlM (fun current _ =>
        machine.stepWithRandomness input handler current <$>
          (List.replicate (bits + 1) ()).mapM (fun _ => coin)) snapshot >>= observeSnapshot)
      state =
      FreeM.runKernel (effectKernel oracle)
        (((machine.runConfigFrom fuel cfg).liftM (oracleHandler (fun port request =>
          handler port request <$> (List.replicate bits ()).mapM (fun _ => coin)))) >>=
            observeConfig) state := by
  induction fuel generalizing snapshot cfg state with
  | zero => simpa using congrArg (fun program =>
      FreeM.runKernel (effectKernel oracle) program state) (hobserve snapshot cfg h)
  | succ fuel ih =>
    rw [List.replicate_succ (n := fuel), List.foldlM_cons]
    simp only [bind_assoc, bind_map_left]
    cases hs : cfg.tapes.state with
    | none =>
      have hstep (coins : List Bool) :
          machine.stepWithRandomness input handler snapshot coins = snapshot := by
        simp [stepWithRandomness, stepSnapshot, h.state, hs]
      simp only [hstep, runConfigFrom_halted _ _ _ hs, FreeM.liftM_pure, pure_bind]
      rw [runKernel_sampleBits_const]
      simpa only [runConfigFrom_halted _ _ _ hs, FreeM.liftM_pure, pure_bind] using
        ih snapshot cfg h state
    | some q =>
      rw [List.replicate_succ, List.mapM_cons]
      simp only [bind_assoc, pure_bind, runConfigFrom, step, hs,
        FreeM.liftM_bind, liftM_oracleHandler_coin]
      rw [runKernel_coin_bind, runKernel_coin_bind]
      apply Measure.bind_congr_right
      refine Filter.Eventually.of_forall fun bit => ?_
      simp only [stepWithRandomness, stepSnapshot, h.state, hs, h.inputSymbol,
        h.workSymbols, h.answerSymbols, List.headD_cons, List.tail_cons]
      cases ha : machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simp only [FreeM.liftM_pure, pure_bind, Id.run_pure]
        rw [runKernel_sampleBits_const]
        simpa only [List.replicate_succ, List.mapM_cons] using
          ih _ _ (h.step action symbol move) state
      | query port next =>
        simp only [FreeM.liftM_bind, liftM_oracleHandler_query, FreeM.liftM_pure,
          bind_map_left, pure_bind, Id.run_pure, h.queryBuffer, bind_assoc]
        apply FreeM.runKernel_bind_congr_of_canReturn
        intro coins _ state
        simpa only [List.replicate_succ, List.mapM_cons] using
          ih _ _ (h.receive port next (handler port (cfg.channels port).queryBuffer coins)) state

end Turing.MultiTapePTM
