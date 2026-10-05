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
public import Cslib.Crypto.Primitives.Schnorr.Fork.Trace
public import Cslib.Computability.PolynomialTime.Realizer.Encoding

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

private def interpretSignatureM {S : Type} {Q : PFunctor.{0, 0}}
    (handler : (op : (signatureEffects 0 Word G F).A) →
      StateT S (OptionT Q.FreeM) ((signatureEffects 0 Word G F).B op))
    {α : Type} (program : OptionT (signatureEffects 0 Word G F).FreeM α) :
    StateT S (OptionT Q.FreeM) α := fun state => do
  let (out, state') ← (program.run.liftM handler) state
  let value ← OptionT.mk (pure out)
  pure (value, state')

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem isMonadHom_interpretSignatureM {S : Type} {Q : PFunctor.{0, 0}}
    (handler : (op : (signatureEffects 0 Word G F).A) →
      StateT S (OptionT Q.FreeM) ((signatureEffects 0 Word G F).B op)) :
    IsMonadHom (OptionT (signatureEffects 0 Word G F).FreeM)
      (StateT S (OptionT Q.FreeM)) (interpretSignatureM handler) :=
  (isMonadHom_optionT_stateT_optionT S).comp (FreeM.isMonadHom_liftM handler).optionT

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem interpretSignatureM_mk_pure {S : Type} {Q : PFunctor.{0, 0}}
    (handler : (op : (signatureEffects 0 Word G F).A) →
      StateT S (OptionT Q.FreeM) ((signatureEffects 0 Word G F).B op))
    {α : Type} (value : Option α) (state : S) :
    interpretSignatureM handler (OptionT.mk (pure value)) state =
      OptionT.mk (pure (value.map (fun value => (value, state)))) := by
  cases value <;> rfl

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Typed snapshot decoding commutes with every aborting stateful interpreter. The identity
retains the joint result and state, and rejects malformed requests and outputs. -/
theorem liftM_signatureMachineProgram {k ports : ℕ} {State S : Type}
    {Q : PFunctor.{0, 0}}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports))
    (handler : (op : (signatureEffects 0 Word G F).A) →
      StateT S (OptionT Q.FreeM) ((signatureEffects 0 Word G F).B op)) (state : S) :
    (do
      let (out, state') ← ((signatureMachineProgram element scalar machine word coins snapshot).run
        |>.liftM handler) state
      let candidate ← OptionT.mk (pure out)
      pure (candidate, state')) = (do
        let (final, state') ← machine.runSnapshotFromCoins (m := StateT S (OptionT Q.FreeM))
          word (fun _ request => fun state =>
          ((signatureRequestEncoding (Computability.encodingList Bool) element).decodeChecked
            request).elim failure (fun op =>
              (fun out => ((signatureResponseEncoding element scalar op).encode out.1, out.2)) <$>
                handler (.inr op) state)) coins snapshot state
        OptionT.mk (pure (do
          let output ← if final.state.isNone then some final.output else none
          let candidate ← ((Computability.encodingList Bool).bitPair
            (element.bitPair scalar)).bitOption.decodeChecked output
          let candidate ← candidate
          pure (candidate, state')))) := by
  change interpretSignatureM handler
    (signatureMachineProgram element scalar machine word coins snapshot) state = _
  unfold signatureMachineProgram
  rw [(isMonadHom_interpretSignatureM handler).map_bind,
    map_runSnapshotFromCoins (isMonadHom_interpretSignatureM handler)]
  have hquery (request : Word) : interpretSignatureM handler (decodeQuery
      (P := PFunctor.mk (Word × G) (fun _ => F) + PFunctor.mk Word (fun _ => G × F))
      (signatureRequestEncoding (Computability.encodingList Bool) element)
      (signatureResponseEncoding element scalar)
      (fun op => FreeM.lift (P := signatureEffects 0 Word G F) (.inr op)) request) =
      fun state =>
        ((signatureRequestEncoding (Computability.encodingList Bool) element).decodeChecked
          request).elim failure (fun op =>
            (fun out => ((signatureResponseEncoding element scalar op).encode out.1, out.2)) <$>
              handler (.inr op) state) := by
    funext state
    simp only [interpretSignatureM, decodeQuery, OptionT.run_bind, OptionT.run_mk,
      OptionT.run_monadLift, OptionT.run_pure, Option.elimM, pure_bind]
    cases ((signatureRequestEncoding (Computability.encodingList Bool) element).decodeChecked
      request) with
    | none => rfl
    | some op =>
      simp only [Option.elim_some, monadLift_self,
        bind_map_left, ← map_eq_pure_bind, FreeM.liftM_map,
        FreeM.liftM_lift (P := signatureEffects 0 Word G F)]
      dsimp +instances only [Bind.bind, StateT.bind, Functor.map, StateT.map,
        OptionT.run, OptionT.mk, OptionT.bind, OptionT.pure, Pure.pure]
      simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, bind_assoc, pure_bind]
      congr 1
      funext out
      cases out <;> rfl
  simp only [hquery]
  dsimp +instances only [Bind.bind, StateT.bind]
  congr 1
  funext out
  rw [interpretSignatureM_mk_pure]
  congr 2
  cases out.1.state <;> simp [Option.map_eq_bind, Option.bind_assoc]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The chosen machine's first typed execution has the original adversary's whole joint law.
The private tape is sampled once. Decoder failures, interpreter failures, and timeout are
retained as `none`, so the equality can be used before any final verification. -/
theorem toMeasure_sample_signatureMachineProgram {Input S : Type} {Q : PFunctor.{0, 0}}
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    [MeasurableSpace F] [MeasurableSpace G]
    [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
    (μ : OutputMeasure Q) [∀ op, MeasureTheory.IsProbabilityMeasure (μ op)]
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element scalar))).run)
    (bit : Q.FreeM Bool)
    (hbit : bit.toMeasure μ = ProbabilityTheory.uniformOn Set.univ)
    (handler : (op : (Word × G) ⊕ Word) → StateT S (OptionT Q.FreeM)
      ((signatureEffects 0 Word G F).B (.inr op))) (state : S) :
    let typed : (op : (signatureEffects 0 Word G F).A) →
        StateT S (OptionT Q.FreeM) ((signatureEffects 0 Word G F).B op)
      | .inl op => isEmptyElim op
      | .inr op => handler op
    let original : (op : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).A) →
        StateT S (OptionT Q.FreeM)
          ((signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).B op)
      | .inl _ => fun state => OptionT.mk ((fun bit => some (bit, state)) <$> bit)
      | .inr op => handler op
    (do
      let coins ← (List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => bit)
      let out ← (((signatureMachineProgram element scalar implementation.machine (input a)
        coins (Snapshot.initial implementation.machine.initial)).run.liftM typed) state).run
      pure (out.bind (fun out => out.1.map (fun value => (value, out.2))))).toMeasure μ =
        (((source.liftM original) state).run).toMeasure μ := by
  intro typed original
  let interpret : (op : (effects Unit).A) → StateT S (OptionT Q.FreeM) ((effects Unit).B op)
    | .inl _ => fun state => OptionT.mk ((fun bit => some (bit, state)) <$> bit)
    | .inr (_, word) => fun state =>
        ((signatureRequestEncoding (Computability.encodingList Bool) element).decodeChecked
          word).elim failure (fun op =>
            (fun out => ((signatureResponseEncoding element scalar op).encode out.1, out.2)) <$>
              handler op state)
  let output := (Computability.encodingList Bool).bitPair (element.bitPair scalar)
  let finish (out : Option (Option Word × S)) : Option ((Word × G × F) × S) := do
    let (word, state) ← out
    let word ← word
    let candidate ← output.bitOption.decodeChecked word
    let candidate ← candidate
    pure (candidate, state)
  have h := implementation.toMeasure_sample_typed μ a
    (signatureRequestEncoding (Computability.encodingList Bool) element)
    (signatureResponseEncoding element scalar) output.bitOption.encode source hsource original
    (fun state => by
      change ((fun bit => some (bit, state)) <$> bit).toMeasure μ = _
      rw [FreeM.toMeasure, ← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete]
      exact congrArg (MeasureTheory.Measure.map _) hbit) state
  change FreeM.denote μ _ = FreeM.denote μ _ at h ⊢
  have h' := congrArg (MeasureTheory.Measure.map finish) h
  rw [← FreeM.denote_map _ _ _ Measurable.of_discrete,
    ← FreeM.denote_map _ _ _ Measurable.of_discrete] at h'
  have hbits (count : ℕ) (state : S) :
      (((List.replicate count ()).mapM (fun _ => coin (Oracle := Unit))).liftM interpret
        state).run =
      (fun coins => some (coins, state)) <$> (List.replicate count ()).mapM (fun _ => bit) := by
    induction count generalizing state with
    | zero => rfl
    | succ count ih =>
      have hcoin : (coin (Oracle := Unit)).liftM interpret =
          fun state => OptionT.mk ((fun bit => some (bit, state)) <$> bit) := by
        simp only [coin, FreeM.liftM_lift (P := effects Unit), interpret]
        rfl
      simp only [List.replicate_succ, List.mapM_cons, FreeM.liftM_bind, FreeM.liftM_pure,
        hcoin]
      dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run,
        OptionT.mk, Pure.pure, StateT.pure, OptionT.pure]
      have ih' (state : S) := ih state
      dsimp only [OptionT.run] at ih'
      simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, bind_map_left]
      rw [ih' state]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  have hmachine (coins : Word) :
      finish <$> (((implementation.runFromCoins a coins).liftM interpret) state).run =
        (fun out => out.bind (fun out => out.1.map (fun value => (value, out.2)))) <$>
          ((((signatureMachineProgram element scalar implementation.machine (input a) coins
            (Snapshot.initial implementation.machine.initial)).run).liftM typed) state).run := by
    have hsnapshot := liftM_signatureMachineProgram element scalar implementation.machine
      (input a) coins (Snapshot.initial implementation.machine.initial) typed state
    rw [implementation.liftM_runFromCoins interpret]
    change finish <$>
      (((fun final => if final.state.isNone then some final.output else none) <$>
        implementation.machine.runSnapshotFromCoins (input a)
          (fun port word => interpret (.inr (implementation.dispatch port, word))) coins
          (Snapshot.initial implementation.machine.initial)).run state).run = _
    rw [StateT.run_map, OptionT.run_map]
    simp only [Functor.map_map]
    have hsnapshot := congrArg OptionT.run hsnapshot
    dsimp +instances only [Bind.bind, OptionT.bind, OptionT.mk, OptionT.run, Pure.pure,
      OptionT.pure] at hsnapshot
    simp only [FreeM.bind_eq_bind, FreeM.pure_eq_pure, pure_bind] at hsnapshot
    simp only [map_eq_pure_bind]
    convert hsnapshot.symm using 1
    · congr 1
      funext out
      cases out with
      | none => rfl
      | some out => cases hs : out.1.state <;> simp [finish, output, hs]
    · congr 1
      funext out
      cases out with
      | none => rfl
      | some out => cases hx : out.1 <;> simp [hx]
  have hleft : FreeM.map finish
      ((((List.replicate (implementation.clock (input a).length) ()).mapM
        (fun _ => coin) >>= implementation.runFromCoins a).liftM interpret) state).run =
      (do
        let coins ← (List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => bit)
        let out ← (((signatureMachineProgram element scalar implementation.machine (input a)
          coins (Snapshot.initial implementation.machine.initial)).run.liftM typed) state).run
        pure (out.bind (fun out => out.1.map (fun value => (value, out.2))))) := by
    rw [FreeM.liftM_bind]
    dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run, OptionT.mk]
    have hbits' := hbits (implementation.clock (input a).length) state
    dsimp only [OptionT.run] at hbits'
    rw [hbits']
    simp only [FreeM.bind_eq_bind, FreeM.map_eq_map, bind_map_left, map_bind]
    apply bind_congr
    intro coins
    simpa only [OptionT.run, map_eq_pure_bind] using hmachine coins
  have hright : FreeM.map finish
      ((((fun value => some (output.bitOption.encode (some value))) <$>
        source.liftM original) state).run) = ((source.liftM original) state).run := by
    change finish <$>
      ((((fun value => some (output.bitOption.encode (some value))) <$>
        source.liftM original).run state).run) = _
    rw [StateT.run_map, OptionT.run_map]
    simp only [Functor.map_map]
    convert id_map' (((source.liftM original) state).run) using 1
    congr 1
    funext out
    cases out <;> simp [finish, Computability.Encoding.decodeChecked_encode]
  rw [← hleft, ← hright]
  convert h' using 2
  congr 1

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

/-- Saving the chosen machine's coins and the simulator's scalar tape preserves the original
checked forgery distribution, including the final random-oracle query and every rejection. -/
theorem toMeasure_sample_privateForgery {Input : Type} {Q : PFunctor.{0, 0}}
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    [MeasurableSpace G] [DiscreteMeasurableSpace G] [Countable G]
    [MeasurableSpace (List Word × List ((Word × G) × F))]
    [DiscreteMeasurableSpace (List Word × List ((Word × G) × F))]
    [∀ op, MeasurableSpace (Q.B op)]
    [∀ op, DiscreteMeasurableSpace (Q.B op)]
    (μ : OutputMeasure Q)
    [∀ op, MeasureTheory.IsProbabilityMeasure (μ op)]
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element scalar))).run)
    (bit : Q.FreeM Bool) (sample : Q.FreeM F)
    (hbit : bit.toMeasure μ = ProbabilityTheory.uniformOn Set.univ) (g pk : G) :
    (do
      let coins ← (List.replicate (implementation.clock (input a).length) ()).mapM
        (fun _ => bit)
      let tape ← (List.replicate (2 * implementation.clock (input a).length) ()).mapM
        (fun _ => sample)
      (privateForgery g pk (signatureMachineProgram element scalar implementation.machine
        (input a) coins (Snapshot.initial implementation.machine.initial)) tape).liftM
          (fun _ => sample)).toMeasure μ =
      ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
        (fun _ => source)).run).toMeasure μ := by
  classical
  let handler := simulatedSignatureHandler (P := 0) (m := Q.FreeM) (M := Word)
    (fun op => isEmptyElim op) sample (fun _ => sample) g pk
  let finish (out : Option ((Word × G × F) × List Word × List ((Word × G) × F))) :
      Q.FreeM (Option (Word × G × F)) :=
    match out with
    | none => pure (none : Option (Word × G × F))
    | some (candidate, messages, cache) => do
      let (valid, _) ← (verify (fun input => RandomOracle.query sample input)
        g pk candidate.1 candidate.2).run cache
      pure (if valid && decide (candidate.1 ∉ messages) then some candidate else none)
  let clock := implementation.clock (input a).length
  let bits := (List.replicate clock ()).mapM (fun _ => bit)
  let machineSource coins := signatureMachineProgram element scalar implementation.machine
    (input a) coins (Snapshot.initial implementation.machine.initial)
  have h := toMeasure_sample_signatureMachineProgram element scalar μ implementation a
    source hsource bit hbit (fun op => handler (.inr op)) ([], [])
  have htyped : (fun op : (signatureEffects 0 Word G F).A => match op with
      | .inl op => isEmptyElim op | .inr op => handler (.inr op)) = handler := by
    funext op
    cases op with
    | inl op => exact isEmptyElim op
    | inr op => rfl
  have horiginal : (fun op :
      (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).A => match op with
      | .inl _ => fun state => OptionT.mk ((fun bit => some (bit, state)) <$> bit)
      | .inr op => handler (.inr op)) =
        simulatedSignatureHandler (fun _ => bit) sample (fun _ => sample) g pk := by
    funext op
    cases op with
    | inl op => simp only [simulatedSignatureHandler, map_eq_pure_bind]; rfl
    | inr op => cases op <;> rfl
  dsimp only at h
  rw [htyped, horiginal] at h
  have h := congrArg (fun measure => measure.bind (fun out => (finish out).toMeasure μ)) h
  change FreeM.denote μ _ = FreeM.denote μ _
  rw [FreeM.denote_bind_of_discrete]
  calc
    _ = (FreeM.denote μ (do
        let coins ← bits
        let out ← (((machineSource coins).run.liftM handler) ([], [])).run
        pure (out.bind (fun out => out.1.map (fun value => (value, out.2)))))).bind
          (fun out => FreeM.denote μ (finish out)) := by
      rw [FreeM.denote_bind_of_discrete, MeasureTheory.Measure.bind_bind
        Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      apply MeasureTheory.Measure.bind_congr_right
      filter_upwards [FreeM.ae_canReturn μ bits] with coins hcoins
      have hlength : coins.length = clock := by
        simpa only [List.length_replicate] using
          List.length_of_canReturn_mapM (fun _ : Unit => bit) _ hcoins
      have hcount : FreeM.queryBound (machineSource coins).run * 2 ≤ (2 * clock : ℕ) := by
        calc
          _ ≤ (coins.length : ℕ∞) * 2 := by
            gcongr
            exact queryBound_signatureMachineProgram_le element scalar implementation.machine
              (input a) coins (Snapshot.initial implementation.machine.initial)
          _ = _ := by simp [hlength, mul_comm]
      rw [← FreeM.denote_bind_of_discrete]
      have hp := toMeasure_privateForgery_liftM μ sample g pk (machineSource coins)
        (2 * clock) hcount
      change FreeM.denote μ _ = FreeM.denote μ _ at hp
      rw [hp]
      congr 1
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro out
      cases out with
      | none => rfl
      | some out =>
        rcases out with ⟨candidate, messages, cache⟩
        cases candidate with
        | none => rfl
        | some candidate =>
          simp only [finish, Option.bind_some, Option.map_some]
          congr 1
          funext out
          cases out
          simp only [Bool.and_eq_true, decide_eq_true_eq]
    _ = _ := by
      convert h using 1
      · simp only [FreeM.toMeasure]
        rw [← FreeM.denote_bind_of_discrete]
      · simp only [FreeM.toMeasure]
        rw [← FreeM.denote_bind_of_discrete]
        congr 1
        simp only [simulatedForgery, OptionT.run_bind, Option.elimM]
        apply bind_congr
        intro out
        cases out with
        | none => rfl
        | some out =>
          rcases out with ⟨⟨message, signature⟩, messages, cache⟩
          simp only [finish, monadLift, MonadLift.monadLift, OptionT.lift,
            OptionT.run_mk, bind_assoc, pure_bind]
          apply bind_congr
          intro out
          simp only [Option.elim_some, Bool.and_eq_true, decide_eq_true_eq]
          split <;> rfl

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


/-- Replay the checked machine at the selected hash and compute a discrete-log candidate.
The discrete-log experiment checks the answer; unsuccessful forks may yield an incorrect guess. -/
def dlogReductionFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars answers fresh : List F) : Option F :=
  (FreeM.forkFromTracedAnswers
    (runSignatureFromAnswers element scalar machine word coins snapshot g pk privateScalars)
    (fun out => findForkPoint g pk (some out.1)
      (out.2.map (fun event => (event.1, event.2)))) answers fresh).map fun out =>
        extract out.2.2.1 out.1.1.2.2 out.2.2.2.1 out.2.2.2.2.1.2.2

/-- The actual replay returns a correct logarithm on the event counted by the forking bound.
This is a pathwise result for arbitrary tapes, without assuming a random input distribution. -/
theorem dlogReductionFromAnswers_correct_of_forkSuccess {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars answers fresh : List F) :
    let run := runSignatureFromAnswers element scalar machine word coins snapshot g pk
      privateScalars
    let choose (out : (Word × G × F) ×
        List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) :=
      findForkPoint g pk (some out.1) (out.2.map (fun event => (event.1, event.2)))
    ∀ out, FreeM.forkFromTracedAnswers run choose answers fresh = some out →
      (out.1, some out.2) ∈ ⋃ n,
        FreeM.forkSuccess (P := PFunctor.mk (Word × G) (fun _ => F)) choose n →
      ∃ secret, dlogReductionFromAnswers element scalar machine word coins snapshot g pk
        privateScalars answers fresh = some secret ∧ secret • g = pk := by
  intro run choose out hrun hsuccess
  rcases out with ⟨⟨first, events⟩, ⟨input, challenge, challenge', second, events'⟩⟩
  obtain ⟨n, event, hevent, hfirst, hsecond, hne⟩ := Set.mem_iUnion.mp hsuccess
  cases hevent
  let source := privateForgery g pk
    (signatureMachineProgram element scalar machine word coins snapshot) privateScalars
  have htrace := FreeM.canReturn_of_forkFromTracedAnswers source run
    (runSignatureFromAnswers_eq element scalar machine word coins snapshot g pk privateScalars)
    choose answers fresh hrun
  have hchoose : (fun out : Option (Word × G × F) ×
        List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B) =>
      out.1.bind (fun value => choose (value, out.2))) =
      (fun out => findForkPoint g pk out.1 (out.2.map (fun event => (event.1, event.2)))) := by
    funext ⟨candidate, events⟩
    cases candidate <;> rfl
  rw [hchoose] at htrace
  obtain ⟨response, response', heq, heq', haccepts, haccepts'⟩ :=
    accepts_of_findForkPoint_eq g pk source htrace (hsecond.trans hfirst.symm)
  cases Option.some.inj heq
  cases Option.some.inj heq'
  refine ⟨extract challenge response challenge' response', ?_,
    extract_smul g pk input.2 hne haccepts haccepts'⟩
  change (FreeM.forkFromTracedAnswers run choose answers fresh).map _ = _
  rw [hrun]
  rfl

section Measures

open MeasureTheory

variable {P : PFunctor.{0, 0}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
  [MeasurableSpace G] [DiscreteMeasurableSpace G] [Countable G]
  (μ : OutputMeasure P) [∀ op, IsProbabilityMeasure (μ op)]

/-- Presampling the hash tape of a saved machine execution preserves its complete checked
output law. The extra slot covers final verification. -/
theorem toMeasure_runSignatureFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word coins : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (privateScalars : List F) (sample : P.FreeM F) (clock : ℕ)
    (hcoins : coins.length ≤ clock) :
    ((fun answers => (runSignatureFromAnswers element scalar machine word coins snapshot
      g pk privateScalars answers).map Prod.fst) <$>
        (List.replicate (clock + 1) ()).mapM (fun _ => sample)).toMeasure μ =
      ((privateForgery g pk (signatureMachineProgram element scalar machine word coins snapshot)
        privateScalars).liftM (fun _ => sample)).toMeasure μ := by
  let source := privateForgery g pk
    (signatureMachineProgram element scalar machine word coins snapshot) privateScalars
  have hbound : FreeM.queryBound source ≤ (clock + 1 : ℕ) :=
    (queryBound_privateForgery_signatureMachineProgram_le element scalar machine word coins
      snapshot g pk privateScalars).trans (by exact_mod_cast Nat.add_le_add_right hcoins 1)
  have htape := FreeM.denote_runFromAnswers μ sample source (clock + 1) hbound
  have htape := congrArg (Measure.map Option.join) htape
  rw [← FreeM.denote_map _ _ _ Measurable.of_discrete,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete] at htape
  simp only [Function.comp_def, Option.join_some, Measure.map_id'] at htape
  change FreeM.denote μ _ = FreeM.denote μ _
  rw [FreeM.denote_liftM]
  rw [← htape]
  simp only [FreeM.map_eq_map, Functor.map_map]
  congr 2
  funext answers
  rw [runSignatureFromAnswers_eq]
  have htrace := congrArg (fun program => FreeM.runFromAnswers program answers)
    (FreeM.map_fst_trace source)
  rw [FreeM.runFromAnswers_map] at htrace
  rw [← htrace]
  cases FreeM.runFromAnswers (FreeM.trace source) answers with
  | none => rfl
  | some out => rcases out with ⟨candidate, events⟩; cases candidate <;> rfl

/-- The concrete saved-tape machine has the original adversary's simulated-forgery law.
This includes private machine coins, private signing scalars, and the verifier's last hash. -/
theorem toMeasure_sample_runSignatureFromAnswers {Input : Type}
    [MeasurableSpace (List Word × List ((Word × G) × F))]
    [DiscreteMeasurableSpace (List Word × List ((Word × G) × F))]
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element scalar))).run)
    (bit : P.FreeM Bool) (sample : P.FreeM F)
    (hbit : bit.toMeasure μ = ProbabilityTheory.uniformOn Set.univ) (g pk : G) :
    (do
      let coins ← (List.replicate (implementation.clock (input a).length) ()).mapM
        (fun _ => bit)
      let privateScalars ←
        (List.replicate (2 * implementation.clock (input a).length) ()).mapM (fun _ => sample)
      let answers ← (List.replicate (implementation.clock (input a).length + 1) ()).mapM
        (fun _ => sample)
      pure ((runSignatureFromAnswers element scalar implementation.machine (input a) coins
        (Snapshot.initial implementation.machine.initial) g pk privateScalars answers).map
          Prod.fst)).toMeasure μ =
      ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
        (fun _ => source)).run).toMeasure μ := by
  let : MeasurableSpace (List F) := ⊤
  refine Eq.trans ?_ (toMeasure_sample_privateForgery element scalar μ implementation a
    source hsource bit sample hbit g pk)
  simp only [FreeM.toMeasure, FreeM.denote_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [FreeM.ae_canReturn μ
    ((List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => bit))]
      with coins hcoins
  apply Measure.bind_congr_right
  filter_upwards [] with privateScalars
  have hlength : coins.length = implementation.clock (input a).length := by
    simpa only [List.length_replicate] using
      List.length_of_canReturn_mapM (fun _ : Unit => bit) _ hcoins
  simpa only [FreeM.toMeasure, map_eq_pure_bind, FreeM.denote_bind_of_discrete] using
    toMeasure_runSignatureFromAnswers element scalar μ implementation.machine (input a) coins
      (Snapshot.initial implementation.machine.initial) g pk privateScalars sample
      (implementation.clock (input a).length) hlength.le

variable [MeasurableSpace (List F)] [DiscreteMeasurableSpace (List F)]
  [MeasurableSpace (List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))]
  [DiscreteMeasurableSpace (List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))]

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

/-- The shared-seed forking bound counts correct answers of the actual discrete-log reduction,
including its checked replay and scalar extraction. The challenge key is supplied externally. -/
theorem le_toMeasure_dlogReductionFromAnswers {k ports : ℕ} {State : Type}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports)) (word : Word)
    (snapshot : Snapshot k Bool State (Fin ports)) (g pk : G)
    (seed : P.FreeM (Word × List F)) (sample : P.FreeM F) (clock : ℕ) (r : ℝ≥0∞)
    (hcoins : ∀ saved, MonadAttach.CanReturn seed saved → saved.1.length ≤ clock)
    (hanswer : ∀ answer, sample.toMeasure μ {answer} ≤ r) :
    let tape := (List.replicate (clock + 1) ()).mapM (fun _ => sample)
    let ε := (seed >>= fun saved => runSignatureFromAnswers element scalar machine word
      saved.1 snapshot g pk saved.2 <$> tape).toMeasure μ {out | out.isSome}
    ε * (ε / (clock + 1 : ℕ) - r) ≤ (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (dlogReductionFromAnswers element scalar machine word saved.1 snapshot g pk
        saved.2 answers fresh)).toMeasure μ {out | ∃ secret, out = some secret ∧ secret • g = pk}
    := by
  intro tape
  let run (saved : Word × List F) :=
    runSignatureFromAnswers element scalar machine word saved.1 snapshot g pk
    saved.2
  let choose (out : (Word × G × F) ×
      List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) :=
    findForkPoint g pk (some out.1) (out.2.map (fun event => (event.1, event.2)))
  let replay := do
    let saved ← seed
    let answers ← tape
    let fresh ← tape
    pure (FreeM.forkFromTracedAnswers (run saved) choose answers fresh)
  let finish := Option.map (fun out :
      ((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) ×
      ((_ : Word × G) × F × F ×
        ((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))) =>
    extract out.2.2.1 out.1.1.2.2 out.2.2.2.1 out.2.2.2.2.1.2.2)
  let : DiscreteMeasurableSpace (Option
      (((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B)) ×
      ((_ : Word × G) × F × F ×
        ((Word × G × F) × List (Sigma (PFunctor.mk (Word × G) (fun _ => F)).B))))) :=
    MeasurableSingletonClass.toDiscreteMeasurableSpace
  have heq : (do
      let saved ← seed
      let answers ← tape
      let fresh ← tape
      pure (dlogReductionFromAnswers element scalar machine word saved.1 snapshot g pk
        saved.2 answers fresh)) = finish <$> replay := by
    simp only [replay, dlogReductionFromAnswers, map_bind, map_pure]
    rfl
  refine (le_toMeasure_forkSignatureFromAnswers element scalar μ machine word snapshot g pk
    seed sample clock r hcoins hanswer).trans ?_
  rw [heq]
  change FreeM.denote μ replay _ ≤ FreeM.denote μ (finish <$> replay) _
  rw [← FreeM.map_eq_map, FreeM.denote_map _ _ _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  apply measure_mono_ae
  filter_upwards [FreeM.ae_canReturn μ replay] with out hout
  intro hsuccess
  obtain ⟨saved, _, hout⟩ := (FreeM.canReturn_bind _ _ _).mp hout
  obtain ⟨answers, _, hout⟩ := (FreeM.canReturn_bind _ _ _).mp hout
  obtain ⟨fresh, _, hout⟩ := (FreeM.canReturn_bind _ _ _).mp hout
  have hout : out = FreeM.forkFromTracedAnswers (run saved) choose answers fresh := hout
  subst out
  obtain ⟨value, hvalue, hgood⟩ := hsuccess
  exact dlogReductionFromAnswers_correct_of_forkSuccess element scalar machine word saved.1
    snapshot g pk saved.2 answers fresh value hvalue hgood

/-- The original typed adversary's simulated success is bounded by the chosen machine's
actual shared-seed reduction. The machine certificate supplies both the first-run equality
and the clock; neither a source replay assumption nor an additional query budget is needed. -/
theorem le_toMeasure_dlogReductionFromAnswers_typed {Input : Type}
    [MeasurableSpace (List Word × List ((Word × G) × F))]
    [DiscreteMeasurableSpace (List Word × List ((Word × G) × F))]
    {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}
    (implementation : Realizer input wordEncoding program) (a : Input)
    (source : (signatureEffects (PFunctor.mk Unit (fun _ => Bool)) Word G F).FreeM
      (Word × G × F))
    (hsource : program a = ((Computability.encodingList Bool).bitPair
      (element.bitPair scalar)).bitOption.encode <$>
        (source.liftM (encodeEffects
          (signatureRequestEncoding (Computability.encodingList Bool) element)
          (signatureResponseEncoding element scalar))).run)
    (bit : P.FreeM Bool) (sample : P.FreeM F)
    (hbit : bit.toMeasure μ = ProbabilityTheory.uniformOn Set.univ) (g pk : G) (r : ℝ≥0∞)
    (hanswer : ∀ answer, sample.toMeasure μ {answer} ≤ r) :
    let clock := implementation.clock (input a).length
    let ε := ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
      (fun _ => source)).run).toMeasure μ {out | out.isSome}
    ε * (ε / (clock + 1 : ℕ) - r) ≤ (do
      let coins ← (List.replicate clock ()).mapM (fun _ => bit)
      let privateScalars ← (List.replicate (2 * clock) ()).mapM (fun _ => sample)
      let answers ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      let fresh ← (List.replicate (clock + 1) ()).mapM (fun _ => sample)
      pure (dlogReductionFromAnswers element scalar implementation.machine (input a) coins
        (Snapshot.initial implementation.machine.initial) g pk
        privateScalars answers fresh)).toMeasure μ
          {out | ∃ secret, out = some secret ∧ secret • g = pk} := by
  intro clock
  let seed := do
    let coins ← (List.replicate clock ()).mapM (fun _ => bit)
    let privateScalars ← (List.replicate (2 * clock) ()).mapM (fun _ => sample)
    pure (coins, privateScalars)
  let first := seed >>= fun saved => runSignatureFromAnswers element scalar
    implementation.machine (input a) saved.1 (Snapshot.initial implementation.machine.initial)
      g pk saved.2 <$> (List.replicate (clock + 1) ()).mapM (fun _ => sample)
  have h := le_toMeasure_dlogReductionFromAnswers element scalar μ implementation.machine
    (input a) (Snapshot.initial implementation.machine.initial) g pk seed sample clock r
    (fun saved hsaved => by
      obtain ⟨coins, hcoins, hsaved⟩ := (FreeM.canReturn_bind _ _ _).mp hsaved
      obtain ⟨privateScalars, _, hsaved⟩ := (FreeM.canReturn_bind _ _ _).mp hsaved
      have hsaved : saved = (coins, privateScalars) := hsaved
      rw [hsaved]
      have hlength : coins.length = clock := by
        simpa only [List.length_replicate] using
          List.length_of_canReturn_mapM (fun _ : Unit => bit) _ hcoins
      exact hlength.le) hanswer
  have hfirst := toMeasure_sample_runSignatureFromAnswers element scalar μ implementation a
    source hsource bit sample hbit g pk
  have hmap : (Option.map Prod.fst <$> first).toMeasure μ =
      ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
        (fun _ => source)).run).toMeasure μ := by
    convert hfirst using 2
    simp only [first, seed, clock, map_eq_pure_bind, bind_assoc, pure_bind]
  have hprob : first.toMeasure μ {out | out.isSome} =
      ((simulatedForgery (fun _ => bit) sample (fun _ => sample) g pk
        (fun _ => source)).run).toMeasure μ {out | out.isSome} := by
    rw [← hmap]
    simp only [FreeM.toMeasure]
    rw [← FreeM.map_eq_map,
      FreeM.denote_map _ _ _ Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    congr 1
    ext out
    cases out <;> simp
  change first.toMeasure μ _ * (first.toMeasure μ _ / (clock + 1 : ℕ) - r) ≤ _ at h
  rw [hprob] at h
  simpa only [seed, bind_assoc, pure_bind] using h

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
