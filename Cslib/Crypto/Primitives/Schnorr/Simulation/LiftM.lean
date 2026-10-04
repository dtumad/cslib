/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation
public import Cslib.Foundations.Control.Monad.IsMonadHom.Transformers

/-! # Inlining the effects used by the Schnorr signing simulator -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {P Q R : PFunctor.{0, 0}} {F G M : Type}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]

/-- Sampling implementations commute with simulated signing, including its abort. -/
theorem liftM_simulateSign (interp : (op : Q.A) → R.FreeM (Q.B op))
    (sample : Q.FreeM F) (g pk : G) (message : M) (cache : List ((M × G) × F)) :
    (((simulateSign sample g pk message).run cache).run).liftM interp =
      ((simulateSign (sample.liftM interp) g pk message).run cache).run := by
  simp only [simulateSign, simulateTranscript, StateT.run, OptionT.run, OptionT.mk,
    bind_assoc, pure_bind, FreeM.liftM_bind, FreeM.liftM_pure]

/-- Inlining each underlying effect commutes with the combined signing and hash handler. -/
theorem liftM_simulatedSignatureHandler (interp : (op : Q.A) → R.FreeM (Q.B op))
    (ambient : (op : P.A) → Q.FreeM (P.B op)) (sample : Q.FreeM F)
    (hashSample : M × G → Q.FreeM F) (g pk : G)
    (op : (signatureEffects P M G F).A) (state : List M × List ((M × G) × F)) :
    (((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run).liftM interp =
      ((simulatedSignatureHandler (fun op => (ambient op).liftM interp) (sample.liftM interp)
        (fun input => (hashSample input).liftM interp) g pk op).run state).run := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl op => simp [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk]
  | inr op =>
    cases op with
    | inl input =>
      simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        FreeM.liftM_bind, FreeM.liftM_pure]
      rw [RandomOracle.map_query (FreeM.isMonadHom_liftM interp)]
    | inr message =>
      dsimp only [simulatedSignatureHandler, StateT.run, OptionT.run, Bind.bind,
        OptionT.instMonad, OptionT.bind, OptionT.mk]
      rw [FreeM.bind_eq_bind, FreeM.liftM_bind]
      have h := liftM_simulateSign interp sample g pk message cache
      dsimp only [StateT.run, OptionT.run] at h
      rw [h]
      congr 1
      funext out
      cases out <;> exact FreeM.liftM_pure _ _

/-- An implementation can replace fresh hash operations after the simulator has been inlined.
The equality includes the signing log, shared cache, aborts, and final verification. -/
theorem liftM_simulatedForgery (interp : (op : Q.A) → R.FreeM (Q.B op))
    (ambient : (op : P.A) → Q.FreeM (P.B op)) (sample : Q.FreeM F)
    (hashSample : M × G → Q.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    ((simulatedForgery ambient sample hashSample g pk adversary).run).liftM interp =
      (simulatedForgery (fun op => (ambient op).liftM interp) (sample.liftM interp)
        (fun input => (hashSample input).liftM interp) g pk adversary).run := by
  have hhandler : (fun op state => OptionT.mk
      ((((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run).liftM
        interp)) =
      simulatedSignatureHandler (fun op => (ambient op).liftM interp) (sample.liftM interp)
        (fun input => (hashSample input).liftM interp) g pk := by
    funext op state
    exact liftM_simulatedSignatureHandler interp ambient sample hashSample g pk op state
  have hstate := congrFun (((FreeM.isMonadHom_liftM interp).optionT.stateT
    (List M × List ((M × G) × F))).map_pfunctorFreeMLiftM
      (simulatedSignatureHandler ambient sample hashSample g pk) (adversary pk)) ([], [])
  rw [hhandler] at hstate
  dsimp only [OptionT.mk, OptionT.run, StateT.run] at hstate
  dsimp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk]
  rw [FreeM.bind_eq_bind, FreeM.liftM_bind]
  congr 1
  funext out
  cases out with
  | none => exact FreeM.liftM_pure _ _
  | some out =>
    rcases out with ⟨⟨message, signature⟩, messages, cache⟩
    simp only [verify, StateT.run_bind, StateT.run_pure, monadLift, MonadLift.monadLift,
      OptionT.lift, OptionT.mk, FreeM.bind_eq_bind, bind_assoc, pure_bind, FreeM.liftM_bind]
    dsimp only [StateT.run]
    rw [RandomOracle.map_query (FreeM.isMonadHom_liftM interp)]
    congr 1
    funext out
    split <;> exact FreeM.liftM_pure _ _

end Cslib.Crypto.Schnorr
