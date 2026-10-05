/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Random.Tape
public import Cslib.Foundations.Data.PFunctor.Free.Trace
public import Cslib.Foundations.Control.Monad.IsMonadHom.Transformers

/-! # Stateful interpretation of checked programs with a fresh-answer trace -/

@[expose] public section

namespace PFunctor.FreeM

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

end PFunctor.FreeM
