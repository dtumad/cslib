/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation.PrivateTape
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.TracedExecution

/-!
# The typed source of a saved-coin Schnorr machine

Canonical word decoding gives an ordinary optional polynomial program. Its private machine
coins are fixed before the program is built. Interpreting its signature operations reproduces
the actual snapshot interpreter, including malformed requests, timeout, and invalid output.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
  (element : Computability.Encoding G Bool) (scalar : Computability.Encoding F Bool)

/-- Decode a clocked word machine into typed signing and hash requests, keeping its entire
private coin tape fixed. Invalid interfaces, timeout, and invalid candidate encodings reject. -/
def signatureMachineProgram {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) :
    OptionT (signatureEffects 0 Word G F).FreeM (Word × G × F) := do
  let final ← machine.runSnapshotFromCoins word
    (fun _ => decodeQuery
      (P := PFunctor.mk (Word × G) (fun _ => F) + PFunctor.mk Word (fun _ => G × F))
      (signatureRequestEncoding (Computability.encodingList Bool) element)
      (signatureResponseEncoding element scalar)
      (fun op => FreeM.lift (P := signatureEffects 0 Word G F) (.inr op))) coins snapshot
  OptionT.mk (pure (do
    let output ← if final.state.isNone then some final.output else none
    let candidate ← ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.decodeChecked output
    candidate))

private def interpretSignature {α : Type} (g pk : G)
    (program : OptionT (signatureEffects 0 Word G F).FreeM α) :
    StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) Option α := fun state => do
  let (out, state') ← (program.run.liftM (P := signatureEffects 0 Word G F)
    (m := StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) Option)
    (fun | .inl op => isEmptyElim op
         | .inr op => traceSeededCall (seededSignatureHandler g pk op))) state
  let value ← out
  pure (value, state')

private theorem isMonadHom_interpretSignature (g pk : G) :
    IsMonadHom (OptionT (signatureEffects 0 Word G F).FreeM)
      (StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
        List ((Word × G) × F)) Option) (interpretSignature g pk) := by
  have hf := (FreeM.isMonadHom_liftM (P := signatureEffects 0 Word G F)
    (m := StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) Option)
    (fun | .inl op => isEmptyElim op
         | .inr op => traceSeededCall (seededSignatureHandler g pk op))).optionT
  exact (isMonadHom_optionT_stateT_option _).comp hf

private theorem interpretSignature_decodeQuery (g pk : G) (word : Word)
    (state : ((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) :
    interpretSignature g pk (decodeQuery
      (P := PFunctor.mk (Word × G) (fun _ => F) + PFunctor.mk Word (fun _ => G × F))
      (signatureRequestEncoding (Computability.encodingList Bool) element)
      (signatureResponseEncoding element scalar)
      (fun op => FreeM.lift (P := signatureEffects 0 Word G F) (.inr op)) word) state =
        traceSeededCall
          (seededSignatureWordHandler element scalar.toEmbedding g pk word) state := by
  cases word with
  | nil => rfl
  | cons bit payload =>
    cases bit with
    | false =>
      simp only [interpretSignature, decodeQuery, signatureRequestEncoding,
        OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, OptionT.run_pure]
      rw [Computability.Encoding.decodeChecked_bitSum_false]
      cases h : ((Computability.encodingList Bool).bitPair element).decodeChecked payload with
      | none =>
        simp only [seededSignatureWordHandler, traceSeededCall, h]
        rfl
      | some input =>
        dsimp only [Option.map, Option.elimM, Option.elim, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Option.bind, monadLift_self, Functor.map, StateT.map,
          FreeM.liftM, FreeM.lift, FreeM.bind, FreeM.map, OptionT.run, OptionT.mk]
        simp only [seededSignatureWordHandler, h, traceSeededCall]
        dsimp +instances only [Bind.bind, Option.bind, Pure.pure]
        cases seededSignatureHandler g pk (.inl input) state.1 <;> rfl
    | true =>
      simp only [interpretSignature, decodeQuery, signatureRequestEncoding,
        OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, OptionT.run_pure]
      rw [Computability.Encoding.decodeChecked_bitSum_true]
      have h : (Computability.encodingList Bool).decodeChecked payload = some payload :=
        Computability.Encoding.decodeChecked_encode (Computability.encodingList Bool) payload
      rw [h]
      dsimp only [Option.map, Option.elimM, Option.elim, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, Option.bind, monadLift_self, Functor.map, StateT.map,
        FreeM.liftM, FreeM.lift, FreeM.bind, FreeM.map, OptionT.run, OptionT.mk]
      simp only [seededSignatureWordHandler, traceSeededCall]
      dsimp +instances only [Bind.bind, Option.bind, Pure.pure]
      cases seededSignatureHandler g pk (.inr payload) state.1 <;> rfl

private theorem interpretSignature_mk_pure {α : Type} (g pk : G) (value : Option α)
    (state : ((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) :
    interpretSignature g pk (OptionT.mk (pure value)) state =
      value.map (fun value => (value, state)) := by
  cases value <;> rfl

/-- Decoding a clocked machine and then interpreting its typed operations gives the actual
word-handler execution, with the identical state and successful trace. -/
theorem signatureMachineProgram_traced {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (state : ((List Word × List ((Word × G) × F)) × (List F × List F)) ×
      List ((Word × G) × F)) :
    (do
      let (candidate, state') ← ((signatureMachineProgram element scalar machine word coins
          snapshot).run
        |>.liftM (P := signatureEffects 0 Word G F)
          (m := StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
            List ((Word × G) × F)) Option)
          (fun | .inl op => isEmptyElim op
               | .inr op => traceSeededCall (seededSignatureHandler g pk op))) state
      let candidate ← candidate
      pure (candidate, state')) = (do
        let (final, state') ← machine.runSnapshotFromCoins (m := StateT _ Option) word
          (fun _ request => traceSeededCall
            (seededSignatureWordHandler element scalar.toEmbedding g pk request))
            coins snapshot state
        let output ← if final.state.isNone then some final.output else none
        let candidate ← ((Computability.encodingList Bool).bitPair
          (element.bitPair scalar)).bitOption.decodeChecked output
        let candidate ← candidate
        pure (candidate, state')) := by
  change interpretSignature g pk
    (signatureMachineProgram element scalar machine word coins snapshot) state = _
  unfold signatureMachineProgram
  rw [(isMonadHom_interpretSignature g pk).map_bind,
    map_runSnapshotFromCoins (isMonadHom_interpretSignature g pk)]
  have hhandler : (fun (_ : Fin ports) request => interpretSignature g pk (decodeQuery
      (P := PFunctor.mk (Word × G) (fun _ => F) + PFunctor.mk Word (fun _ => G × F))
      (signatureRequestEncoding (Computability.encodingList Bool) element)
      (signatureResponseEncoding element scalar)
      (fun op => FreeM.lift (P := signatureEffects 0 Word G F) (.inr op)) request)) =
      (fun _ request => traceSeededCall
        (seededSignatureWordHandler element scalar.toEmbedding g pk request)) := by
    funext port request state
    exact interpretSignature_decodeQuery element scalar g pk request state
  rw [hhandler]
  dsimp +instances only [Bind.bind, StateT.bind]
  congr 1
  funext out
  rw [interpretSignature_mk_pure]
  cases out.1.state <;> simp [Option.map_eq_bind, Option.bind_assoc]

/-- Run the actual checked machine on a fresh hash tape, sharing its fixed private coins and
simulator scalars. The result is precisely the successful trace needed by the replay compiler. -/
def runSignatureFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars hashScalars : List F) :
    Option ((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) := do
  let (final, state) ← machine.runSnapshotFromCoins (m := StateT _ Option) word
    (fun _ request => traceSeededCall
      (seededSignatureWordHandler element scalar.toEmbedding g pk request)) coins snapshot
        ((([], []), privateScalars, hashScalars), [])
  let (candidate, state) ← traceSeededCall
    (checkSeededForgeryOutput element scalar g pk
      (if final.state.isNone then some final.output else none)) state
  pure (candidate, state.2.map (fun event => ⟨event.1, event.2⟩))

/-- The machine's complete successful trace equals the hash-only source trace, pointwise in
both saved random tapes. Rejected requests, timeout, invalid output, and failed verification
all become the same `none` on both sides. -/
theorem runSignatureFromAnswers_eq {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars hashScalars : List F) :
    runSignatureFromAnswers element scalar machine word coins snapshot g pk privateScalars
        hashScalars =
      (FreeM.runFromAnswers (FreeM.trace (privateForgery g pk
        (signatureMachineProgram element scalar machine word coins snapshot) privateScalars))
          hashScalars).bind (fun out => out.1.map (fun candidate => (candidate, out.2))) := by
  rw [← privateForgery_traced]
  have hsource := signatureMachineProgram_traced element scalar machine word coins snapshot g pk
    ((([], []), privateScalars, hashScalars), [])
  have h := congrArg (fun result => result.bind (fun out => do
      let (candidate, state') ← traceSeededCall (checkSeededForgery g pk out.1) out.2
      pure (candidate, state'.2.map (fun event => (⟨event.1, event.2⟩ :
        Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))))) hsource
  dsimp +instances only [Bind.bind, Pure.pure] at h ⊢
  simp only [Option.bind_assoc, Option.bind_some] at h
  convert h.symm using 1
  · unfold runSignatureFromAnswers
    dsimp +instances only [Bind.bind]
    congr 1
    funext out
    cases out.1.state <;>
      simp [traceSeededCall, checkSeededForgeryOutput, Option.bind_assoc]
  · congr 2
    apply congrFun
    apply congrArg (fun handler => FreeM.liftM (P := signatureEffects 0 Word G F)
      (m := StateT (((List Word × List ((Word × G) × F)) × (List F × List F)) ×
        List ((Word × G) × F)) Option) handler
      (signatureMachineProgram element scalar machine word coins snapshot).run)
    funext op
    cases op with
    | inl op => exact isEmptyElim op
    | inr op => rfl

section Indexed

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool)
  (scalar : ∀ n, Computability.Encoding (F n) Bool)

/-- Fixing a parameter and key commutes with the uniform checked interpreter. In particular,
the encoded candidate and fresh-hash transcript have the same joint rejection behavior. -/
theorem runSignatureFromAnswers_encode {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (n : ℕ) (g pk : G n)
    (privateScalars hashScalars : List (F n)) :
    (runSignatureFromAnswers (element n) (scalar n) machine word coins snapshot g pk
      privateScalars hashScalars).map (fun out => pairEncoding
        (pairEncoding wordEncoding (pairEncoding (element n).toEmbedding (scalar n).toEmbedding))
        (listEncoding (sigmaEncoding (pairEncoding wordEncoding (element n).toEmbedding)
          (fun _ => (scalar n).toEmbedding))) out) =
    (runCheckedTracedSignatureMachine element scalar machine word coins snapshot
      ⟨n, (g, pk, ([], []), privateScalars, hashScalars), []⟩).map (fun out =>
        List.BitPair.encode out.1 (listEncoding
          (pairEncoding (pairEncoding wordEncoding (element out.2.1).toEmbedding)
            (scalar out.2.1).toEmbedding) out.2.2.2)) := by
  let embed (state : (((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n))) × List ((Word × G n) × F n))) :=
    (⟨n, (g, pk, state.1), state.2⟩ : Σ n, (G n × G n ×
      ((List Word × List ((Word × G n) × F n)) × (List (F n) × List (F n)))) ×
        List ((Word × G n) × F n))
  have hrun := runSnapshotFromCoins_map_state machine word
    (fun _ => tracedSignatureMachineHandler element (fun n => (scalar n).toEmbedding))
    (fun _ request => traceSeededCall
      (seededSignatureWordHandler (element n) (scalar n).toEmbedding g pk request))
    embed (fun _ request state => by
      dsimp +instances only [embed, tracedSignatureMachineHandler]
      cases traceSeededCall
        (seededSignatureWordHandler (element n) (scalar n).toEmbedding g pk request) state <;>
        rfl) coins snapshot ((([], []), privateScalars, hashScalars), [])
  unfold runSignatureFromAnswers runCheckedTracedSignatureMachine
  change _ = ((machine.runSnapshotFromCoins (m := StateT _ Option) word
    (fun _ => tracedSignatureMachineHandler element (fun n => (scalar n).toEmbedding))
      coins snapshot (embed ((([], []), privateScalars, hashScalars), []))).bind _).map _
  rw [← hrun]
  dsimp +instances only [Bind.bind, Pure.pure]
  simp only [Option.map_bind, Option.bind_map]
  congr 1
  funext out
  dsimp +instances only [Function.comp_apply, Bind.bind, Pure.pure, Option.map_some,
    checkTracedSignatureMachine, embed]
  simp only [Option.map_bind, Function.comp_def, Option.map_some]
  congr 1
  funext checked
  simp only [pairEncoding_apply]
  congr 2
  apply listEncoding_map
  intro event
  rfl

end Indexed

end Cslib.Crypto.Schnorr
