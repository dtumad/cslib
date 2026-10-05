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

variable {P : PFunctor.{0, 0}} {F G M : Type}
  [Field F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
  {m n : Type → Type*} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  {f : ∀ {α}, m α → n α} (hf : IsMonadHom m n f)

include hf

/-- Sampling implementations commute with simulated signing, including its abort. -/
theorem map_simulateSign (sample : m F) (g pk : G) (message : M)
    (cache : List ((M × G) × F)) :
    f ((simulateSign sample g pk message).run cache).run =
      ((simulateSign (f sample) g pk message).run cache).run := by
  simp only [simulateSign, simulateTranscript, StateT.run, OptionT.run, OptionT.mk,
    bind_assoc, pure_bind, hf.map_bind, hf.map_pure]

/-- Inlining each underlying effect commutes with the combined signing and hash handler. -/
theorem map_simulatedSignatureHandler
    (ambient : (op : P.A) → m (P.B op)) (sample : m F)
    (hashSample : M × G → m F) (g pk : G)
    (op : (signatureEffects P M G F).A) (state : List M × List ((M × G) × F)) :
    f ((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run =
      ((simulatedSignatureHandler (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk op).run state).run := by
  rcases state with ⟨messages, cache⟩
  cases op with
  | inl op =>
    simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
      hf.map_bind, hf.map_pure]
  | inr op =>
    cases op with
    | inl input =>
      simp only [simulatedSignatureHandler, StateT.run, OptionT.run, OptionT.mk,
        hf.map_bind, hf.map_pure]
      rw [RandomOracle.map_query hf]
    | inr message =>
      dsimp only [simulatedSignatureHandler, StateT.run, OptionT.run, Bind.bind,
        OptionT.instMonad, OptionT.bind, OptionT.mk]
      rw [hf.map_bind]
      have h := map_simulateSign hf sample g pk message cache
      dsimp only [StateT.run, OptionT.run] at h
      rw [h]
      congr 1
      funext out
      cases out <;> exact hf.map_pure _

/-- An implementation can replace fresh hash operations after the simulator has been inlined.
The equality includes the signing log, shared cache, aborts, and final verification. -/
theorem map_simulatedForgery
    (ambient : (op : P.A) → m (P.B op)) (sample : m F)
    (hashSample : M × G → m F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    f (simulatedForgery ambient sample hashSample g pk adversary).run =
      (simulatedForgery (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk adversary).run := by
  have hhandler : (fun op state => OptionT.mk
      (f ((simulatedSignatureHandler ambient sample hashSample g pk op).run state).run)) =
      simulatedSignatureHandler (fun op => f (ambient op)) (f sample)
        (fun input => f (hashSample input)) g pk := by
    funext op state
    exact map_simulatedSignatureHandler hf ambient sample hashSample g pk op state
  have hstate := congrFun ((hf.optionT.stateT
    (List M × List ((M × G) × F))).map_pfunctorFreeMLiftM
      (simulatedSignatureHandler ambient sample hashSample g pk) (adversary pk)) ([], [])
  rw [hhandler] at hstate
  dsimp only [OptionT.mk, OptionT.run, StateT.run] at hstate
  dsimp only [simulatedForgery, OptionT.run, Bind.bind, OptionT.bind, OptionT.mk, StateT.run]
  rw [hf.map_bind, hstate]
  congr 1
  funext out
  cases out with
  | none => exact hf.map_pure _
  | some out =>
    rcases out with ⟨⟨message, signature⟩, messages, cache⟩
    simp only [verify, monadLift, MonadLift.monadLift,
      OptionT.lift, OptionT.mk, bind_assoc, pure_bind, hf.map_bind]
    dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
    simp only [hf.map_bind, hf.map_pure, bind_assoc, pure_bind]
    rw [RandomOracle.map_query hf]
    congr 1
    funext out
    split <;> exact hf.map_pure _

end Cslib.Crypto.Schnorr
