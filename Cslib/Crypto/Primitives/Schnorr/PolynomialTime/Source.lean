/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation.PrivateTape
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.TracedExecution
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Cost
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape

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

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Each saved machine transition makes at most one typed request. Canonical decoding,
output checking, and rejection add no source operations. -/
theorem queryBound_signatureMachineProgram_le {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) :
    FreeM.queryBound (signatureMachineProgram element scalar machine word coins snapshot).run ≤
      coins.length := by
  apply (FreeM.queryBound_optionT_bind_le _ _ 0 (fun _ => le_rfl)).trans
  simp only [add_zero]
  apply (queryBound_runSnapshotFromCoins_optionT_le machine word _ 1 ?_ coins snapshot).trans_eq
  · exact mul_one _
  · intro port request
    simp only [decodeQuery, OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_pure_comp,
      pure_bind]
    cases (signatureRequestEncoding (Computability.encodingList Bool) element).decodeChecked
      request <;>
      simp [FreeM.queryBound_lift (P := signatureEffects 0 Word G F)]

/-- A saved execution and its final verifier fit in a hash tape one longer than the clock. -/
theorem queryBound_privateForgery_signatureMachineProgram_le {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G) (privateScalars : List F) :
    FreeM.queryBound (privateForgery g pk
      (signatureMachineProgram element scalar machine word coins snapshot) privateScalars) ≤
      (coins.length + 1 : ℕ) := by
  apply (queryBound_privateForgery_le g pk _ privateScalars).trans
  simpa only [Nat.cast_add, Nat.cast_one] using
    add_le_add (queryBound_signatureMachineProgram_le element scalar machine word coins
      snapshot) (le_rfl : (1 : ℕ∞) ≤ 1)

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

/-- Every successful checked run selects an accepting hash within its clock-derived budget.
The final verifier supplies a position even when the adversary never requested that hash. -/
theorem runSignatureFromAnswers_forkPoint {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars hashScalars : List F)
    {out : (Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)}
    (h : runSignatureFromAnswers element scalar machine word coins snapshot g pk
      privateScalars hashScalars = some out) :
    ∃ n < coins.length + 1, findForkPoint g pk (some out.1)
      (out.2.map (fun event => (event.1, event.2))) = some n := by
  have hlength : out.2.length ≤ coins.length + 1 := by
    rw [runSignatureFromAnswers_eq] at h
    obtain ⟨⟨candidate, events⟩, htrace, h⟩ := Option.bind_eq_some_iff.mp h
    cases candidate with
    | none => cases h
    | some candidate =>
      cases h
      have hreturn := FreeM.canReturn_of_runFromAnswers _ _ htrace
      have hcost := (FreeM.countP_trace_le_queryBoundP (fun _ => true) _ hreturn).trans
        (by
          simpa only [FreeM.queryBoundP_true] using
            (queryBound_privateForgery_signatureMachineProgram_le element scalar machine word
              coins snapshot g pk privateScalars))
      simpa only [List.countP_true, ENat.natCast_le_natCast] using hcost
  unfold runSignatureFromAnswers at h
  obtain ⟨result, hrun, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨checked, hcheck, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have hrecorded := runSnapshotFromCoins_preserves machine word
    (fun _ request => traceSeededCall
      (seededSignatureWordHandler element scalar.toEmbedding g pk request))
    (fun state => ∀ input challenge, state.1.1.2.lookup input = some challenge →
      input.1 ∈ state.1.1.1 ∨ (input, challenge) ∈ state.2)
    (fun _ request state hstate result hresult =>
      traceSeededSignatureWordHandler_recorded element scalar.toEmbedding g pk request
        state.1 state.2 hstate hresult) coins snapshot
    ((([], []), privateScalars, hashScalars), []) (by simp) hrun
  have hplain := congrArg (Option.map (fun out => (out.1, out.2.1))) hcheck
  rw [traceSeededCall_forget] at hplain
  obtain ⟨candidate, houtput, _⟩ := (checkSeededForgeryOutput_eq_some_iff
    element scalar g pk _ _ _).mp hplain
  rw [houtput, checkSeededForgeryOutput_encode] at hcheck
  obtain ⟨heq, challenge, haccepts, hmem⟩ := traceSeededCall_check_recorded g pk candidate
    result.2.1 result.2.2 (fun input challenge hlookup => hrecorded input challenge (by
      simpa only [List.lookup_eq_some_iff, bne_iff_ne] using hlookup)) hcheck
  have hexists : (findForkPoint g pk (some checked.1) checked.2.2).isSome := by
    simp only [heq, findForkPoint,
      List.findIdx?_isSome, List.any_eq_true, decide_eq_true_eq]
    exact ⟨((candidate.1, candidate.2.1), challenge), hmem, rfl, haccepts⟩
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hexists
  refine ⟨n, ?_, ?_⟩
  · exact lt_of_lt_of_le (List.findIdx?_eq_some_iff_findIdx_eq.mp hn).1
      (by simpa only [List.length_map] using hlength)
  · simpa [List.map_map, Function.comp_def] using hn


section Measures

open MeasureTheory

variable {P : PFunctor.{0, 0}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
  [MeasurableSpace G] [DiscreteMeasurableSpace G] [Countable G]
  [MeasurableSpace (List F)] [DiscreteMeasurableSpace (List F)]
  [MeasurableSpace (List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))]
  [DiscreteMeasurableSpace (List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))]
  (μ : OutputMeasure P) [∀ op, IsProbabilityMeasure (μ op)]

/-- Sampling one private seed and two hash tapes implements the complete semantic fork of
the fixed-seed machine source. The same coins and simulator scalars are reused by both runs;
all rejections retain their mass at `none`. -/
theorem toMeasure_forkSignatureFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (seed : P.FreeM (Word × List F)) (sample : P.FreeM F) (clock : ℕ)
    (hcoins : ∀ saved, MonadAttach.CanReturn seed saved → saved.1.length ≤ clock) :
    let run saved := runSignatureFromAnswers element scalar machine word saved.1 snapshot
      g pk saved.2
    let choose (out : (Word × G × F) ×
        List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) :=
      findForkPoint g pk (some out.1) (out.2.map (fun event => (event.1, event.2)))
    let source saved := privateForgery g pk
      (signatureMachineProgram element scalar machine word saved.1 snapshot) saved.2
    let tape := (List.replicate (clock + 1) ()).mapM (fun _ => sample)
    (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (FreeM.forkFromTracedAnswers (run saved) choose answers fresh)).toMeasure μ =
        (seed.toMeasure μ).bind (fun saved =>
          ((FreeM.fork (fun _ => true)
            (fun out => out.1.bind (fun value => choose (value, out.2)))
            (FreeM.trace (source saved))).toMeasure
              (.ofMeasure (fun _ => sample.toMeasure μ))).map (fun out => do
                let first ← out.1.1
                let ⟨op, answer, answer', second, events⟩ ← out.2
                let second ← second
                pure ((first, out.1.2), (⟨op, answer, answer', second, events⟩ :
                  (_ : Word × G) × F × F ×
                    ((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))))))
    := by
  intro run choose source tape
  change FreeM.denote μ _ = _
  rw [FreeM.denote_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [FreeM.ae_canReturn μ seed] with saved hsaved
  apply FreeM.denote_forkFromTracedAnswers μ sample (source saved) (run saved)
    (runSignatureFromAnswers_eq element scalar machine word saved.1 snapshot g pk saved.2)
    choose (clock + 1)
  exact (queryBound_privateForgery_signatureMachineProgram_le element scalar machine word
    saved.1 snapshot g pk saved.2).trans (by
      exact_mod_cast Nat.add_le_add_right (hcoins saved hsaved) 1)

open scoped ENNReal

/-- The actual two-run machine interpreter satisfies the shared-seed forking inequality.
Every checked first-run forgery is covered by the clock-derived hash budget. -/
theorem le_toMeasure_forkSignatureFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (seed : P.FreeM (Word × List F)) (sample : P.FreeM F) (clock : ℕ) (r : ℝ≥0∞)
    (hcoins : ∀ saved, MonadAttach.CanReturn seed saved → saved.1.length ≤ clock)
    (hanswer : ∀ answer, sample.toMeasure μ {answer} ≤ r) :
    let run saved := runSignatureFromAnswers element scalar machine word saved.1 snapshot
      g pk saved.2
    let choose (out : (Word × G × F) ×
        List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) :=
      findForkPoint g pk (some out.1) (out.2.map (fun event => (event.1, event.2)))
    let tape := (List.replicate (clock + 1) ()).mapM (fun _ => sample)
    let ε := (seed >>= fun saved => run saved <$> tape).toMeasure μ
      {out | out.isSome}
    ε * (ε / (clock + 1 : ℕ) - r) ≤ (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (FreeM.forkFromTracedAnswers (run saved) choose answers fresh)).toMeasure μ
        {out | ∃ value, out = some value ∧ (value.1, some value.2) ∈ ⋃ n,
          FreeM.forkSuccess (P := PFunctor.mk (Word × G) (fun _ => F)) choose n} := by
  intro run choose tape
  have hfork := FreeM.le_denote_forkFromTracedAnswers_bind μ seed sample
    (fun saved => privateForgery g pk
      (signatureMachineProgram element scalar machine word saved.1 snapshot) saved.2)
    run (fun saved _ => runSignatureFromAnswers_eq element scalar machine word saved.1
      snapshot g pk saved.2) choose (clock + 1) (clock + 1) r
    (fun saved hsaved =>
      (queryBound_privateForgery_signatureMachineProgram_le element scalar machine word
        saved.1 snapshot g pk saved.2).trans (by
          exact_mod_cast Nat.add_le_add_right (hcoins saved hsaved) 1)) hanswer (by
      intro saved hsaved out hout n hn
      have h := (List.findIdx?_eq_some_iff_findIdx_eq.mp hn).1
      simpa only [List.length_map] using h)
  have hprob : FreeM.denote μ (seed >>= fun saved => run saved <$> tape)
      {out | ∃ value, out = some value ∧ ∃ n < clock + 1, choose value = some n} =
      FreeM.denote μ (seed >>= fun saved => run saved <$> tape) {out | out.isSome} := by
    apply measure_congr
    filter_upwards [FreeM.ae_canReturn μ (seed >>= fun saved => run saved <$> tape)] with out hout
    apply propext
    constructor
    · rintro ⟨value, rfl, _⟩
      rfl
    · intro hsuccess
      obtain ⟨saved, hsaved, hout⟩ := (FreeM.canReturn_bind _ _ _).mp hout
      obtain ⟨answers, _, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hout
      cases hr : run saved answers with
      | none => simp only [hr, Option.isSome_none, Bool.false_eq_true] at hsuccess
      | some result =>
        obtain ⟨n, hn, hchoose⟩ := runSignatureFromAnswers_forkPoint element scalar machine word
          saved.1 snapshot g pk saved.2 answers hr
        exact ⟨result, rfl, n, hn.trans_le (Nat.add_le_add_right (hcoins saved hsaved) 1),
          hchoose⟩
  dsimp only at hfork ⊢
  rw [hprob] at hfork
  exact hfork

end Measures


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
