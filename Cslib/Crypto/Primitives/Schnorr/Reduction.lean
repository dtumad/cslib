/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Crypto.DiscreteLog
public import Cslib.Crypto.Primitives.Schnorr.Fork
public import Cslib.Crypto.Primitives.Schnorr.Simulation.LiftM

/-! # A discrete-logarithm reduction from a Schnorr signature adversary -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor

variable {P : PFunctor.{0, 0}} {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M]

/-- Simulate signing and fork the adversary, then implement every fresh hash draw using `sample`.
The resulting reduction uses only the original ambient effects and the supplied public key. -/
def dlogReduction (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (pk : G) :
    P.FreeM (Option F) :=
  let close : (op : (P + PFunctor.mk (M × G) (fun _ => F)).A) →
      P.FreeM ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := fun
    | .inl op => FreeM.lift op
    | .inr _ => sample
  (signatureExtractor sample g pk adversary).liftM close

/-- Every value returned by the closed reduction is a logarithm of its input public key. -/
theorem dlogReduction_sound (sample : P.FreeM F) (g : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) (pk : G) {secret : F}
    (h : MonadAttach.CanReturn (dlogReduction sample g adversary pk) (some secret)) :
    secret • g = pk :=
  signatureExtractor_sound sample g pk adversary (FreeM.canReturn_of_liftM _ _ h)

omit [DecidableEq F] in
/-- Closing the simulator's explicit hash effects recovers the ordinary signing simulation. -/
theorem liftM_simulatedForgery_hash (sample : P.FreeM F) (g pk : G)
    (adversary : G → (signatureEffects P M G F).FreeM (M × G × F)) :
    let ambient := fun op : P.A =>
      FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inl op)
    let close : (op : (P + PFunctor.mk (M × G) (fun _ => F)).A) → P.FreeM
      ((P + PFunctor.mk (M × G) (fun _ => F)).B op) := fun
        | .inl op => FreeM.lift op
        | .inr _ => sample
    ((simulatedForgery ambient (sample.liftM ambient)
      (fun input => FreeM.lift (P := P + PFunctor.mk (M × G) (fun _ => F)) (.inr input))
      g pk adversary).run).liftM close =
        (simulatedForgery FreeM.lift sample (fun _ => sample) g pk adversary).run := by
  dsimp only
  rw [liftM_simulatedForgery]
  simp only [FreeM.liftM_comp,
    FreeM.liftM_lift (P := P + PFunctor.mk (M × G) (fun _ => F)), FreeM.liftM_lift_eq_self]

end Cslib.Crypto.Schnorr
