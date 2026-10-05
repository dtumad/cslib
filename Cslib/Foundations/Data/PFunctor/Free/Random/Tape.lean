/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Free.Cost
public import Cslib.Foundations.MeasureTheory.Option
public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Cslib.Foundations.Control.Monad.IsMonadHom.Transformers

/-!
# Finite answer tapes

For operations with one common answer type, a finite list can supply the answers in order.
Exhaustion is explicit. Sampling a tape long enough for every path preserves the entire result
measure, including when requests depend on earlier answers and some tape entries go unused.
-/

@[expose] public section

namespace PFunctor.FreeM

section Answers

open MeasureTheory

universe uA uQ u

variable {Operation Answer α : Type u}

/-- Consume the next saved answer, failing if the tape is exhausted. -/
def readAnswer : StateT (List Answer) Option Answer
  | [] => none
  | answer :: rest => some (answer, rest)

/-- Interpret each request using the next tape entry. Unused entries are discarded on return. -/
def runFromAnswers (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) : Option α :=
  ((program.liftM (m := StateT (List Answer) Option) (fun _ => readAnswer)).run answers).map
    Prod.fst

@[simp] theorem runFromAnswers_pure (value : α) (answers : List Answer) :
    runFromAnswers (Operation := Operation) (pure value) answers = some value := rfl

@[simp] theorem runFromAnswers_lift_bind_nil (op : Operation)
    (cont : Answer → (PFunctor.mk Operation (fun _ => Answer)).FreeM α) :
    runFromAnswers (lift op >>= cont) [] = none := rfl

@[simp] theorem runFromAnswers_lift_bind_cons (op : Operation)
    (cont : Answer → (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answer : Answer) (rest : List Answer) :
    runFromAnswers (lift op >>= cont) (answer :: rest) = runFromAnswers (cont answer) rest := rfl

/-- Postprocessing does not consume answers or hide exhaustion. -/
@[simp] theorem runFromAnswers_map {β : Type u} (f : α → β)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α) (answers : List Answer) :
    runFromAnswers (f <$> program) answers = (runFromAnswers program answers).map f := by
  induction program generalizing answers with
  | pure value => rfl
  | lift_bind op cont ih =>
    cases answers with
    | nil => rfl
    | cons answer rest => exact ih answer rest

/-- Supplying answers cannot create a result absent from the source program. -/
theorem canReturn_of_runFromAnswers
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) {value : α} (h : runFromAnswers program answers = some value) :
    MonadAttach.CanReturn program value := by
  induction program generalizing answers with
  | pure result => simpa using h.symm
  | lift_bind op cont ih =>
    cases answers with
    | nil => cases h
    | cons answer rest => exact ⟨answer, ih answer rest h⟩

/-- Every tape at least as long as the worst-case query count suffices, regardless of its
contents. This is independent of any sampling distribution. -/
theorem runFromAnswers_isSome
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (answers : List Answer) (h : queryBound program ≤ answers.length) :
    (runFromAnswers program answers).isSome := by
  induction program generalizing answers with
  | pure value => rfl
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le (fun _ => true) op cont answers.length (by simpa using h)
    cases answers with
    | nil => simp at hcost
    | cons answer rest =>
      exact ih answer rest (by simpa using hcost.2 answer)

variable {P : PFunctor.{uA, u}}
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  [∀ op, IsProbabilityMeasure (μ op)] in
/-- Independent copies depend only on the sample's law, not its source interface. -/
theorem denote_replicate_congr {Q : PFunctor.{uQ, u}}
    [∀ op, MeasurableSpace (Q.B op)] [∀ op, DiscreteMeasurableSpace (Q.B op)]
    [MeasurableSpace (List Answer)] [DiscreteMeasurableSpace (List Answer)]
    (ν : (op : Q.A) → Measure (Q.B op))
    (sample : P.FreeM Answer) (sample' : Q.FreeM Answer)
    (h : denote μ sample = denote ν sample') (count : ℕ) :
    denote μ ((List.replicate count ()).mapM (fun _ => sample)) =
      denote ν ((List.replicate count ()).mapM (fun _ => sample')) := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, List.mapM_cons, denote_bind_of_discrete]
    rw [h]
    congr 1
    funext value
    simp only [ih, denote_pure]

omit [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer]
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
  [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [∀ op, IsProbabilityMeasure (μ op)] in
/-- A presampled tape can be split into consecutive independent blocks. -/
theorem bind_replicate_add (sample : P.FreeM Answer) (first second : ℕ)
    (cont : List Answer → List Answer → P.FreeM α) :
    ((List.replicate (first + second) ()).mapM (fun _ => sample) >>= fun tape =>
      cont (tape.take first) (tape.drop first)) =
    (do
      let before ← (List.replicate first ()).mapM (fun _ => sample)
      let after ← (List.replicate second ()).mapM (fun _ => sample)
      cont before after) := by
  rw [List.replicate_add, List.mapM_append]
  simp only [bind_assoc]
  apply bind_congr_of_canReturn
  intro before hbefore
  have hlength : before.length = first := by
    simpa only [List.length_replicate] using length_of_canReturn_mapM _ _ hbefore
  apply bind_congr
  intro after
  simp [← hlength]

/-- Presampling independent answers preserves the whole output measure of an adaptive
program. The pathwise bound ensures that tape exhaustion has zero probability. -/
theorem denote_runFromAnswers (sample : P.FreeM Answer)
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α)
    (count : ℕ) (hcount : queryBound program ≤ count) :
    denote μ (runFromAnswers program <$> (List.replicate count ()).mapM (fun _ => sample)) =
      (denote (P := PFunctor.mk Operation (fun _ => Answer))
        (fun _ => denote μ sample) program).map some := by
  let : MeasurableSpace (List Answer) := ⊤
  induction program generalizing count with
  | pure value =>
    change denote μ ((fun _ : List Answer => some value) <$>
      (List.replicate count ()).mapM (fun _ => sample)) = _
    rw [← map_eq_map, denote_map μ _ _ Measurable.of_discrete, Measure.map_const]
    simp
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le (fun _ => true) op cont count (by simpa using hcount)
    cases count with
    | zero => simp at hcost
    | succ count =>
      have hrun : runFromAnswers (lift op >>= cont) <$>
          (List.replicate (count + 1) ()).mapM (fun _ => sample) =
            sample >>= fun answer => runFromAnswers (cont answer) <$>
              (List.replicate count ()).mapM (fun _ => sample) := by
        simp only [List.replicate_succ, List.mapM_cons, map_eq_pure_bind,
          LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
        rfl
      rw [bind_eq_bind, hrun, denote_bind_of_discrete]
      apply Measure.ext
      intro event hevent
      rw [Measure.bind_apply hevent Measurable.of_discrete.aemeasurable,
        Measure.map_apply Measurable.of_discrete hevent,
        denote_bind_of_discrete, denote_lift,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      apply lintegral_congr
      intro answer
      rw [ih answer count (by simpa using hcost.2 answer),
        Measure.map_apply Measurable.of_discrete hevent]

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α] in
/-- Preparing all fallible draws before checking them has the same optional output law as
stopping at the first failure. Unused draws have total mass one. -/
theorem denote_mapM_optionT {Index : Type u}
    [MeasurableSpace (List Answer)] [DiscreteMeasurableSpace (List Answer)]
    (sample : Index → P.FreeM (Option Answer)) (indices : List Index) :
    denote μ (indices.mapM (fun index => OptionT.mk (sample index))).run =
      denote μ (List.mapM id <$> indices.mapM sample) := by
  let : MeasurableSpace (List (Option Answer)) := ⊤
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp only [List.mapM_cons, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
      Option.elimM, ← bind_eq_bind, ← map_eq_map, FreeM.map_bind, FreeM.map_pure]
    simp only [bind_eq_bind]
    rw [denote_bind_of_discrete, denote_bind_of_discrete]
    apply Measure.bind_congr_right
    refine Filter.Eventually.of_forall fun value => ?_
    cases value with
    | none =>
      simp only [Option.elim_none, id_eq, ← map_eq_pure_bind]
      change denote μ (pure none) = denote μ ((fun _ : List (Option Answer) =>
        (none : Option (List Answer))) <$> indices.mapM sample)
      rw [← map_eq_map, denote_map μ _ _ Measurable.of_discrete, Measure.map_const]
      simp
    | some value =>
      have hcont (out : Option (List Answer)) :
          out.elim (pure none : P.FreeM (Option (List Answer)))
            (fun rest => pure (some (value :: rest))) = pure (out.map (value :: ·)) := by
        cases out <;> rfl
      simp only [Option.elim_some, hcont, ← map_eq_pure_bind]
      change denote μ (Option.map (value :: ·) <$>
        (indices.mapM (fun index => OptionT.mk (sample index))).run) = _
      rw [← map_eq_map, denote_map μ _ _ Measurable.of_discrete, ih]
      rw [← denote_map μ _ _ Measurable.of_discrete]
      simp only [map_eq_map, Functor.map_map]
      congr 1

end Answers

section PrivateAnswers

open Cslib MeasureTheory

universe u

variable {P : PFunctor.{u, u}} {Answer α : Type u}

/-- Supply saved answers to the right summand while retaining the left summand's effects.
The remaining tape is ordinary state, and exhaustion is an explicit failure. -/
def withAnswerTape (program : (P + PFunctor.mk Unit (fun _ => Answer)).FreeM α) :
    StateT (List Answer) (OptionT P.FreeM) α :=
  program.liftM (P := P + PFunctor.mk Unit (fun _ => Answer)) (fun
    | .inl op => fun answers => OptionT.mk
      ((fun answer => some (answer, answers)) <$> lift op)
    | .inr _ => fun answers => OptionT.mk (pure (readAnswer answers)))

/-- Supplying a private tape commutes with monadic sequencing, keeping its unused suffix. -/
theorem isMonadHom_withAnswerTape :
    IsMonadHom (P + PFunctor.mk Unit (fun _ => Answer)).FreeM
      (StateT (List Answer) (OptionT P.FreeM)) withAnswerTape :=
  isMonadHom_liftM _

@[simp] theorem withAnswerTape_pure (value : α) :
    withAnswerTape (P := P) (Answer := Answer) (pure value) = pure value := rfl

@[simp] theorem withAnswerTape_lift_left (op : P.A) (answers : List Answer) :
    (withAnswerTape (lift (P := P + PFunctor.mk Unit (fun _ => Answer)) (.inl op)) answers).run =
      (fun answer => some (answer, answers)) <$> lift op := by
  simp [withAnswerTape, liftM_lift (P := P + PFunctor.mk Unit (fun _ => Answer))]

@[simp] theorem withAnswerTape_lift_right (answers : List Answer) :
    (withAnswerTape (lift (P := P + PFunctor.mk Unit (fun _ => Answer)) (.inr ())) answers).run =
      (pure (readAnswer answers) : P.FreeM (Option (Answer × List Answer))) := by
  simp [withAnswerTape, liftM_lift (P := P + PFunctor.mk Unit (fun _ => Answer))]

theorem withAnswerTape_lift_bind_left (op : P.A)
    (cont : P.B op → (P + PFunctor.mk Unit (fun _ => Answer)).FreeM α)
    (answers : List Answer) :
    ((withAnswerTape (lift (P := P + PFunctor.mk Unit (fun _ => Answer))
      (.inl op) >>= cont)).run' answers).run = lift op >>= fun answer =>
        ((withAnswerTape (cont answer)).run' answers).run := by
  rw [isMonadHom_withAnswerTape.map_bind]
  simp only [StateT.run', OptionT.run_map]
  dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run, OptionT.mk]
  have h := withAnswerTape_lift_left (P := P) op answers
  dsimp only [OptionT.run] at h
  rw [h]
  simp [bind_eq_bind, _root_.bind_map_left, _root_.map_bind]

theorem withAnswerTape_lift_bind_right (cont : Answer →
    (P + PFunctor.mk Unit (fun _ => Answer)).FreeM α) (answer : Answer) (answers : List Answer) :
    ((withAnswerTape (lift (P := P + PFunctor.mk Unit (fun _ => Answer))
      (.inr ()) >>= cont)).run' (answer :: answers)).run =
        ((withAnswerTape (cont answer)).run' answers).run := by
  rw [isMonadHom_withAnswerTape.map_bind]
  simp only [StateT.run', OptionT.run_map]
  dsimp +instances only [Bind.bind, StateT.bind, OptionT.bind, OptionT.run, OptionT.mk]
  have h := withAnswerTape_lift_right (P := P) (answer :: answers)
  dsimp only [OptionT.run] at h
  rw [h]
  simp [readAnswer]

variable [∀ op, MeasurableSpace (P.B op)] [∀ op, DiscreteMeasurableSpace (P.B op)]
  [∀ op, Countable (P.B op)]
  [MeasurableSpace Answer] [DiscreteMeasurableSpace Answer] [Countable Answer]
  [MeasurableSpace α]
  (μ : (op : P.A) → Measure (P.B op)) [∀ op, IsProbabilityMeasure (μ op)]

/-- A sufficient private tape may be sampled before an adaptive computation. Visible effects
keep their order, unused private entries integrate out, and the whole output law is preserved. -/
theorem denote_withAnswerTape (sample : P.FreeM Answer)
    (program : (P + PFunctor.mk Unit (fun _ => Answer)).FreeM α)
    (count : ℕ) (hcount : queryBoundP Sum.isRight program ≤ count) :
    denote μ (do
      let answers ← (List.replicate count ()).mapM (fun _ => sample)
      (withAnswerTape program).run' answers |>.run) =
      denote μ (some <$> program.liftM (P := P + PFunctor.mk Unit (fun _ => Answer)) (fun
        | .inl op => lift op
        | .inr _ => sample)) := by
  let : MeasurableSpace (List Answer) := ⊤
  let : ∀ op, MeasurableSpace ((P + PFunctor.mk Unit (fun _ => Answer)).B op) :=
    OutputMeasure.sumMeasurableSpace P (PFunctor.mk Unit (fun _ => Answer))
  induction program generalizing count with
  | pure value =>
    simp only [withAnswerTape_pure, StateT.run', OptionT.run_map, liftM_pure]
    dsimp +instances only [Pure.pure, StateT.pure, OptionT.pure, OptionT.run, OptionT.mk]
    simp only [pure_eq_pure, Functor.map, map_pure, Option.map_some]
    rw [denote_bind_of_discrete μ]
    simp
  | lift_bind op cont ih =>
    have hcost := queryBoundP_cont_le Sum.isRight op cont count hcount
    rw [bind_eq_bind]
    cases op with
    | inl op =>
      simp only [withAnswerTape_lift_bind_left (P := P), liftM_bind,
        liftM_lift (P := P + PFunctor.mk Unit (fun _ => Answer)),
        _root_.map_bind, denote_bind_of_discrete, denote_lift]
      rw [Measure.bind_comm (Measurable.of_discrete)]
      apply Measure.bind_congr_right (Filter.Eventually.of_forall fun answer => ?_)
      simpa only [denote_bind_of_discrete] using
        ih answer count (by simpa using hcost.2 answer)
    | inr token =>
      cases token
      cases count with
      | zero => simp at hcost
      | succ count =>
        simp only [List.replicate_succ, List.mapM_cons, LawfulMonad.bind_assoc,
          LawfulMonad.pure_bind,
          withAnswerTape_lift_bind_right (P := P), liftM_bind,
          liftM_lift (P := P + PFunctor.mk Unit (fun _ => Answer)),
          _root_.map_bind, denote_bind_of_discrete]
        apply Measure.bind_congr_right (Filter.Eventually.of_forall fun answer => ?_)
        simpa only [denote_bind_of_discrete] using
          ih answer count (by simpa using hcost.2 answer)

end PrivateAnswers

section Tracing

variable {Operation Answer α : Type}

/-- Consume an answer and record the operation that requested it. Exhaustion rejects. -/
def readAnswerTrace (op : Operation) :
    StateT (List Answer × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option Answer
  | ([], _) => none
  | (answer :: rest, events) => some (answer, rest, events ++ [⟨op, answer⟩])

/-- Recording at each interpreted request gives exactly the program's structural trace,
retaining the unused answer suffix and appending to any initial record. -/
theorem liftM_readAnswerTrace
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM α) (answers : List Answer)
    (events : List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) :
    (program.liftM (m := StateT (List Answer ×
      List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option) readAnswerTrace)
      (answers, events) =
      (((trace program).liftM (m := StateT (List Answer) Option) (fun _ => readAnswer))
        answers).map (fun out => (out.1.1, out.2, events ++ out.1.2)) := by
  induction program generalizing answers events with
  | pure value =>
    change some (value, answers, events) = some (value, answers, events ++ [])
    rw [List.append_nil]
  | lift_bind op cont ih =>
    cases answers with
    | nil => rfl
    | cons answer answers =>
      change ((cont answer).liftM (m := StateT (List Answer ×
        List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option) readAnswerTrace)
          (answers, events ++ [⟨op, answer⟩]) = _
      rw [ih]
      rw [bind_eq_bind, trace_lift_bind op cont]
      simp only [liftM_bind, liftM_pure]
      rw [liftM_lift (P := PFunctor.mk Operation (fun _ => Answer))
        (m := StateT (List Answer) Option) (fun _ => readAnswer) op]
      dsimp +instances only [Bind.bind, StateT.bind, Pure.pure, StateT.pure,
        readAnswer, Option.bind]
      cases ((trace (cont answer)).liftM (m := StateT (List Answer) Option)
        (fun _ => readAnswer)) answers <;>
        simp only [Option.map_none, Option.map_some, List.append_assoc, List.singleton_append]

/-- Interpret a checked program on a saved answer tape. Failed programs discard the trace;
successful ones retain the complete chronological record and unused answer suffix. -/
def runTracedFromAnswers
    (program : OptionT (PFunctor.mk Operation (fun _ => Answer)).FreeM α) :
    StateT (List Answer × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option α :=
  fun state => do
    let (out, state') ← (program.run.liftM (m := StateT (List Answer ×
      List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option) readAnswerTrace) state
    let value ← out
    pure (value, state')

@[simp] theorem runTracedFromAnswers_mk_pure (value : Option α)
    (state : List Answer × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) :
    runTracedFromAnswers (OptionT.mk (pure value)) state =
      value.map (fun value => (value, state)) := by
  cases value <;> rfl

/-- A visible operation consumes and records one answer before continuing the checked program. -/
theorem runTracedFromAnswers_mk_lift_bind (op : Operation)
    (cont : Answer → (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (state : List Answer × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) :
    runTracedFromAnswers (OptionT.mk (lift op >>= cont)) state =
      (readAnswerTrace op state).bind (fun out =>
        runTracedFromAnswers (OptionT.mk (cont out.1)) out.2) := by
  simp only [runTracedFromAnswers, OptionT.run_mk]
  rw [liftM_lift_bind (P := PFunctor.mk Operation (fun _ => Answer))
    (m := StateT (List Answer ×
      List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option) readAnswerTrace op cont]
  dsimp +instances only [Bind.bind, StateT.bind]
  rw [Option.bind_assoc]

/-- Checked trace interpretation preserves sequential composition and all early failures. -/
theorem isMonadHom_runTracedFromAnswers :
    Cslib.IsMonadHom (OptionT (PFunctor.mk Operation (fun _ => Answer)).FreeM)
      (StateT (List Answer × List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option)
      runTracedFromAnswers := by
  have hf := (isMonadHom_liftM (P := PFunctor.mk Operation (fun _ => Answer))
    (m := StateT (List Answer ×
      List (Sigma (PFunctor.mk Operation (fun _ => Answer)).B)) Option) readAnswerTrace).optionT
  exact (Cslib.isMonadHom_optionT_stateT_option _).comp hf

/-- Forgetting the unused suffix gives the partial trace observation used by answer-tape
forking. Both tape exhaustion and a checked-program abort remain `none`. -/
theorem runTracedFromAnswers_eq
    (program : (PFunctor.mk Operation (fun _ => Answer)).FreeM (Option α))
    (answers : List Answer) :
    (runTracedFromAnswers (OptionT.mk program) (answers, [])).map
      (fun out => (out.1, out.2.2)) =
        (runFromAnswers (trace program) answers).bind
          (fun out => out.1.map (fun value => (value, out.2))) := by
  simp only [runTracedFromAnswers, OptionT.run_mk]
  rw [liftM_readAnswerTrace program answers []]
  simp only [List.nil_append]
  unfold runFromAnswers
  dsimp only [StateT.run]
  cases ((trace program).liftM (m := StateT (List Answer) Option)
    (fun _ => readAnswer)) answers with
  | none => rfl
  | some out =>
    rcases out with ⟨⟨out, events⟩, rest⟩
    cases out <;> rfl

end Tracing

end PFunctor.FreeM
