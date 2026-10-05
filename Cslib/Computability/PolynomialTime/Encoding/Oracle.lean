/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding.Decoding
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Free.Cost

/-!
# Typed queries at a machine's word interface

An ordinary polynomial signature supplies the typed requests and replies. Mathlib encodings
translate them to a single named word oracle; canonical decoding rejects malformed messages.
Private coins pass through unchanged. The round-trip law is a program equality in any lawful
monad, so it retains shared state, traces, and the order of effects.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeTM PFunctor

variable {P : PFunctor.{0, 0}} {m : Type → Type*} [Monad m]

/-- Encode a typed request and reject replies outside its canonical representation. -/
def encodeQuery (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool) (op : P.A) :
    OptionT (effects Unit).FreeM (P.B op) :=
  OptionT.mk ((response op).decodeChecked <$> query () (request.encode op))

/-- Decode a word request, run its typed handler, and encode the reply. Invalid requests fail
before the handler is called. -/
def decodeQuery (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (handler : (op : P.A) → m (P.B op)) (word : Word) : OptionT m Word := do
  let op ← OptionT.mk (pure (request.decodeChecked word))
  let answer ← monadLift (handler op)
  pure ((response op).encode answer)

/-- Encode external requests while keeping private coins as native machine coins. -/
def encodeEffects (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool) :
    (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) →
      OptionT (effects Unit).FreeM ((PFunctor.mk Unit (fun _ => Bool) + P).B op)
  | .inl _ => monadLift (coin (Oracle := Unit))
  | .inr op => encodeQuery request response op

/-- Interpret a machine's coins and word queries through the original typed handler. -/
def decodeEffects (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (handler : (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) →
      m ((PFunctor.mk Unit (fun _ => Bool) + P).B op)) :
    (op : (effects Unit).A) → OptionT m ((effects Unit).B op)
  | .inl token => monadLift (handler (.inl token))
  | .inr (_, word) => decodeQuery request response (fun op => handler (.inr op)) word

variable [LawfulMonad m]

@[simp] theorem decodeQuery_encode (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (handler : (op : P.A) → m (P.B op)) (op : P.A) :
    (decodeQuery request response handler (request.encode op)).run =
      (fun answer => some ((response op).encode answer)) <$> handler op := by
  simp [decodeQuery, OptionT.run_bind, OptionT.run_monadLift]

/-- The adapter has no failure on canonically encoded calls and replies. Both optional layers
are retained: request rejection belongs to the interpreter, reply rejection to the caller. -/
theorem liftM_encodeEffects (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (handler : (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) →
      m ((PFunctor.mk Unit (fun _ => Bool) + P).B op)) {α : Type}
    (program : (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α) :
    (((program.liftM (encodeEffects request response)).run).liftM
      (decodeEffects request response handler)).run =
        (fun value => some (some value)) <$> program.liftM handler := by
  induction program with
  | pure value => simp
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift, OptionT.run_bind]
    cases op with
    | inl token =>
      cases token
      simp only [encodeEffects, OptionT.run_monadLift, coin, Option.elimM, monadLift_self,
        bind_map_left, Option.elim_some, FreeM.liftM_bind, FreeM.liftM_lift, decodeEffects,
        OptionT.run_bind, ih, map_bind]
    | inr op =>
      simp only [encodeEffects, encodeQuery, OptionT.run_mk, Option.elimM, bind_map_left,
        query, FreeM.liftM_bind, OptionT.run_bind]
      rw [FreeM.liftM_lift]
      simp only [decodeEffects, decodeQuery_encode, bind_map_left, Option.elim_some,
        Computability.Encoding.decodeChecked_encode, ih, map_bind]
      rfl

/-- Every typed query path occurs at the word interface by supplying canonical replies.
In particular, a word-level machine clock can bound selected source requests. -/
theorem queryBoundP_le_encodeEffects (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool) (select : P.A → Bool)
    {α : Type} (program : (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α) :
    FreeM.queryBoundP (Sum.elim (fun _ => false) select) program ≤
      FreeM.queryBoundP
        (Sum.elim (fun _ => false) (fun query => (request.decodeChecked query.2).any select))
        (program.liftM (encodeEffects request response)).run := by
  induction program with
  | pure value => simp
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind, FreeM.queryBoundP_lift_bind, FreeM.liftM_lift_bind,
      OptionT.run_bind, Option.elimM]
    cases op with
    | inl token =>
      cases token
      simp only [encodeEffects, OptionT.run_monadLift, monadLift_self, coin,
        bind_map_left, Option.elim_some, FreeM.queryBoundP_lift_bind, Sum.elim_inl,
        Bool.false_eq_true, ↓reduceIte, zero_add]
      convert iSup_mono ih using 1
      rfl
    | inr op =>
      simp only [encodeEffects, encodeQuery, OptionT.run_mk, bind_map_left, query,
        FreeM.queryBoundP_lift_bind (P := effects Unit), Sum.elim_inr,
        Computability.Encoding.decodeChecked_encode, Option.any_some]
      apply add_le_add le_rfl
      apply iSup_le
      intro answer
      refine (ih answer).trans (le_trans ?_ (le_iSup _ ((response op).encode answer)))
      simp only [Computability.Encoding.decodeChecked_encode, Option.elim_some, le_refl]

end Turing.MultiTapePTM
