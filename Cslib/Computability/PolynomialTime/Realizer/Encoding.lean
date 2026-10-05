/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding.Oracle
public import Cslib.Computability.PolynomialTime.Realizer.CoinTape
public import Cslib.Computability.PolynomialTime.Realizer.Queries
public import Cslib.Foundations.Data.PFunctor.Free.Kernel

/-! # Joint correctness at a typed oracle interface -/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

section Typed

variable {P : PFunctor.{0, 0}} {S α : Type}
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, MeasurableSingletonClass (P.B op)]
  [∀ op, Countable (P.B op)]

/-- Present a typed oracle as a word oracle, retaining its entire shared state. Malformed
requests have zero measure; they never arise from `encodeQuery`. -/
noncomputable def encodedOracle (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (impl : (op : P.A) → Kernel S (P.B op × S)) : Unit → Word → Kernel S (Word × S) :=
  fun _ word =>
    ⟨fun state => (request.decodeChecked word).elim 0
      (fun op => (impl op state).map (fun out => ((response op).encode out.1, out.2))),
      Measurable.of_discrete⟩

variable (request : Computability.Encoding P.A Bool)
  (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
  (impl : (op : P.A) → Kernel S (P.B op × S))

/-- Encoding and decoding a call preserves the joint reply-and-state measure. -/
theorem runKernel_encodeQuery (op : P.A) (state : S) :
    FreeM.runKernel (effectKernel (encodedOracle request response impl))
      (encodeQuery request response op).run state =
        (impl op state).map (fun out => (some out.1, out.2)) := by
  rw [encodeQuery, OptionT.run_mk, ← FreeM.map_eq_map, FreeM.runKernel_map]
  simp only [query, FreeM.runKernel_lift (P := effects Unit), effectKernel, encodedOracle,
    Kernel.coe_mk, Computability.Encoding.decodeChecked_encode, Option.elim_some]
  change ((impl op state).map (fun out => ((response op).encode out.1, out.2))).map
    (fun out => ((response op).decodeChecked out.1, out.2)) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Computability.Encoding.decodeChecked_encode]

/-- The interface preserves an adaptive typed program's whole joint measure. -/
theorem runKernel_liftM_encodeQuery [MeasurableSpace α] (program : P.FreeM α) (state : S) :
    FreeM.runKernel (effectKernel (encodedOracle request response impl))
      (program.liftM (encodeQuery request response)).run state =
        FreeM.runKernel impl (some <$> program) state :=
  FreeM.runKernel_liftM_optionT impl _ _ (runKernel_encodeQuery request response impl) program state

/-- Coins retain their standard measurable space; external replies retain the typed one. -/
local instance (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) :
    MeasurableSpace ((PFunctor.mk Unit (fun _ => Bool) + P).B op) :=
  match op with
  | .inl _ => inferInstanceAs (MeasurableSpace Bool)
  | .inr op => inferInstanceAs (MeasurableSpace (P.B op))

local instance (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) :
    MeasurableSingletonClass ((PFunctor.mk Unit (fun _ => Bool) + P).B op) := by
  cases op with
  | inl _ => exact inferInstanceAs (MeasurableSingletonClass Bool)
  | inr op => exact inferInstanceAs (MeasurableSingletonClass (P.B op))

local instance (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) :
    Countable ((PFunctor.mk Unit (fun _ => Bool) + P).B op) := by
  cases op with
  | inl _ => exact inferInstanceAs (Countable Bool)
  | inr op => exact inferInstanceAs (Countable (P.B op))

/-- Native private coins and encoded external requests preserve the complete typed execution.
Only the word interface changes; oracle state remains shared across every call. -/
theorem runKernel_encodeEffects [MeasurableSpace α]
    (program : (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel (encodedOracle request response impl))
      (program.liftM (encodeEffects request response)).run state =
        FreeM.runKernel (P := PFunctor.mk Unit (fun _ => Bool) + P) (fun
          | .inl _ => effectKernel (encodedOracle request response impl) (.inl ())
          | .inr op => impl op) (some <$> program) state := by
  apply FreeM.runKernel_liftM_optionT
  intro op state
  cases op with
  | inl token =>
    cases token
    simp only [encodeEffects, OptionT.run_monadLift, monadLift_self, ← FreeM.map_eq_map,
      FreeM.runKernel_map, coin, FreeM.runKernel_lift (P := effects Unit)]
  | inr op => exact runKernel_encodeQuery request response impl op state

/-- Executing a chosen word machine for an encoded typed program preserves the joint typed
experiment. Interface failure and machine timeout have distinct encodings, and neither occurs
with canonical typed replies. -/
theorem Realizer.runKernel_typed [Countable S] {Input : Type} {input : Input ↪ Word}
    {output : α ↪ Word} {program : Input → (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α}
    (implementation : Realizer input (optionEncoding output)
      (fun a => ((program a).liftM (encodeEffects request response)).run))
    (a : Input) (state : S) :
    FreeM.runKernel (effectKernel (encodedOracle request response impl))
      (implementation.run a) state =
        FreeM.runKernel (P := PFunctor.mk Unit (fun _ => Bool) + P) (fun
          | .inl _ => effectKernel (encodedOracle request response impl) (.inl ())
          | .inr op => impl op)
            ((fun value => some (optionEncoding output (some value))) <$> program a) state := by
  let : MeasurableSpace α := ⊤
  let : Countable α := output.injective.countable
  rw [implementation.runKernel_run]
  simp only [← FreeM.map_eq_map, FreeM.runKernel_map]
  rw [runKernel_encodeEffects request response impl]
  simp only [← FreeM.map_eq_map, FreeM.runKernel_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Sampling the entire private tape once gives the same first execution as the typed source,
including a shared oracle's transcript and final state. The tape remains explicit for replay. -/
theorem Realizer.runKernel_sample_typed [Countable S] {Input : Type} {input : Input ↪ Word}
    {output : α ↪ Word} {program : Input → (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α}
    (implementation : Realizer input (optionEncoding output)
      (fun a => ((program a).liftM (encodeEffects request response)).run))
    (a : Input) (state : S) :
    FreeM.runKernel (effectKernel (encodedOracle request response impl))
      ((List.replicate (implementation.clock (input a).length) ()).mapM (fun _ => coin) >>=
        implementation.runFromCoins a) state =
        FreeM.runKernel (P := PFunctor.mk Unit (fun _ => Bool) + P) (fun
          | .inl _ => effectKernel (encodedOracle request response impl) (.inl ())
          | .inr op => impl op)
            ((fun value => some (optionEncoding output (some value))) <$> program a) state := by
  rw [implementation.runKernel_sample_runFromCoins, ← implementation.runKernel_run]
  exact implementation.runKernel_typed request response impl a state

end Typed

private theorem liftM_run_optionT {P Q : PFunctor.{0, 0}} {m : Type → Type*}
    [Monad m] [LawfulMonad m]
    (encode : (op : P.A) → OptionT Q.FreeM (P.B op))
    (interpret : (op : Q.A) → m (Q.B op)) (handler : (op : P.A) → m (P.B op))
    (h : ∀ op, (encode op).run.liftM interpret = some <$> handler op)
    {α : Type} (program : P.FreeM α) :
    (program.liftM encode).run.liftM interpret = some <$> program.liftM handler := by
  induction program with
  | pure value => simp
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift (P := P), OptionT.run_bind,
      FreeM.liftM_bind, h, bind_map_left, Option.elimM, Option.elim_some, ih, map_bind]

section Aborting

variable {P Q : PFunctor.{0, 0}} {Input α S : Type}
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  {input : Input ↪ Word} {program : Input → (effects Unit).FreeM Word}

/-- A chosen encoded machine preserves an aborting typed interpreter's complete joint law.
Canonical decoding supplies the interface round trip. The interpreter may abort on programming
collisions without conditioning either experiment, and malformed machine requests reject. -/
theorem Realizer.toMeasure_sample_typed (μ : OutputMeasure Q)
    [∀ op, IsProbabilityMeasure (μ op)]
    (implementation : Realizer input wordEncoding program) (a : Input)
    (request : Computability.Encoding P.A Bool)
    (response : (op : P.A) → Computability.Encoding (P.B op) Bool)
    (result : Option α → Word) (source : (PFunctor.mk Unit (fun _ => Bool) + P).FreeM α)
    (hsource : program a = result <$> (source.liftM (encodeEffects request response)).run)
    (handler : (op : (PFunctor.mk Unit (fun _ => Bool) + P).A) →
      StateT S (OptionT Q.FreeM) ((PFunctor.mk Unit (fun _ => Bool) + P).B op))
    (hcoin : ∀ state, FreeM.toMeasure (α := Option (Bool × S))
      (handler (.inl ()) state).run μ =
      (uniformOn (Set.univ : Set Bool)).map (fun bit => some (bit, state))) (state : S) :
    let interpret : (op : (effects Unit).A) →
        StateT S (OptionT Q.FreeM) ((effects Unit).B op)
      | .inl token => handler (.inl token)
      | .inr (_, word) => fun state => (request.decodeChecked word).elim failure fun op =>
        (fun out => ((response op).encode out.1, out.2)) <$> handler (.inr op) state
    ((((List.replicate (implementation.clock (input a).length) ()).mapM
      (fun _ => coin) >>= implementation.runFromCoins a).liftM interpret) state).run.toMeasure μ =
      (((fun value => some (result (some value))) <$> source.liftM handler) state).run.toMeasure
        μ := by
  intro interpret
  have hencode : ∀ op, (encodeEffects request response op).run.liftM interpret =
      some <$> handler op := by
    intro op
    cases op with
    | inl token =>
      cases token
      simp only [encodeEffects, OptionT.run_monadLift, monadLift_self, FreeM.liftM_map,
        coin, FreeM.liftM_lift (P := effects Unit), interpret]
    | inr op =>
      simp only [encodeEffects, encodeQuery, OptionT.run_mk, FreeM.liftM_map, query,
        FreeM.liftM_lift (P := effects Unit), interpret]
      funext state
      change (fun out => ((response op).decodeChecked out.1, out.2)) <$>
        ((request.decodeChecked (request.encode op)).elim failure fun op =>
          (fun out => ((response op).encode out.1, out.2)) <$> handler (.inr op) state) = _
      simp only [Computability.Encoding.decodeChecked_encode, Option.elim_some, Functor.map_map]
      rfl
  rw [implementation.toMeasure_sample_runFromCoins μ a interpret hcoin state, hsource]
  simp only [FreeM.liftM_map, liftM_run_optionT (encodeEffects request response) interpret handler
    hencode, Functor.map_map, wordEncoding, Function.Embedding.refl_apply]

end Aborting

variable {Input Output : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- A chosen uniform machine's clock bounds the original typed requests. The signature and
result encoding may vary with the input; private source coins are left uncounted. -/
theorem Realizer.queryBoundP_typed {input : Input ↪ Word} {output : Output ↪ Word}
    {signature : Input → PFunctor.{0, 0}} {Result : Input → Type}
    (request : ∀ a, Computability.Encoding (signature a).A Bool)
    (response : ∀ a op, Computability.Encoding ((signature a).B op) Bool)
    (result : ∀ a, Option (Result a) → Output)
    (program : ∀ a, (PFunctor.mk Unit (fun _ => Bool) + signature a).FreeM (Result a))
    (implementation : Realizer input output (fun a => result a <$>
      ((program a).liftM (encodeEffects (request a) (response a))).run))
    (a : Input) (select : (signature a).A → Bool) :
    FreeM.queryBoundP (Sum.elim (fun _ => false) select) (program a) ≤
      implementation.clock (input a).length := by
  apply (queryBoundP_le_encodeEffects (request a) (response a) select (program a)).trans
  simpa only [FreeM.queryBoundP_map] using implementation.queryBoundP_le a
    (Sum.elim (fun _ => false) (fun query => ((request a).decodeChecked query.2).any select)) rfl


/-- A uniform certificate at the word interface bounds selected typed requests, even when
the signature, result type, and their encodings vary with the input parameter. -/
theorem IsPPT.queryBoundP_typed {input : Input ↪ Word} {output : Output ↪ Word}
    {signature : Input → PFunctor.{0, 0}} {Result : Input → Type}
    (request : ∀ a, Computability.Encoding (signature a).A Bool)
    (response : ∀ a op, Computability.Encoding ((signature a).B op) Bool)
    (result : ∀ a, Option (Result a) → Output)
    (program : ∀ a, (PFunctor.mk Unit (fun _ => Bool) + signature a).FreeM (Result a))
    (h : IsPPT input output (fun a => result a <$>
      ((program a).liftM (encodeEffects (request a) (response a))).run)) :
    ∃ c d : ℕ, ∀ a (select : (signature a).A → Bool),
      FreeM.queryBoundP (Sum.elim (fun _ => false) select) (program a) ≤
        (c * ((input a).length + 1) ^ d : ℕ) := by
  obtain ⟨implementation⟩ := isPPT_iff_nonempty_realizer.mp h
  exact ⟨implementation.coefficient, implementation.degree,
    implementation.queryBoundP_typed request response result program⟩

end Turing.MultiTapePTM
