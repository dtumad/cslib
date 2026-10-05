/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Repetition controlled by a unary work tape

`repeatUnary body` runs a deterministic body once per true cell on a fresh last work tape. The
body must return with words on its work tapes and restore all heads between invocations. The words
may change on each invocation. The controller rewinds its own head before halting, so the same
interface supports stateful bounded loops and nested polynomial clocks.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Repeat the body along a unary counter on the last tape. The three controller states advance
the head, check for another iteration, and rewind the head, respectively. -/
@[simps] def repeatUnary (body : MultiTapeTM k Bool State) :
    MultiTapeTM (k + 1) Bool (State ⊕ Fin 3) where
  q₀ := .inr 1
  tr state symbol work :=
    match state with
    | .inl state =>
      let action := body.tr state symbol (fun i => work i.castSucc)
      { inputTape := action.inputTape
        workTapes := Fin.lastCases (none, 0) action.workTapes
        output := action.output
        state := some (action.state.elim (.inr 0) .inl) }
    | .inr phase =>
      if phase = 0 then
        { inputTape := 0, workTapes := Fin.lastCases (none, 1) (fun _ => (none, 0)),
          output := none, state := some (.inr 1) }
      else if phase = 1 then
        if work (Fin.last k) = some true then
          { inputTape := 0, workTapes := fun _ => (none, 0),
            output := none, state := some (.inl body.q₀) }
        else
          { inputTape := 0, workTapes := Fin.lastCases (none, -1) (fun _ => (none, 0)),
            output := none, state := some (.inr 2) }
      else if work (Fin.last k) = some true then
        { inputTape := 0, workTapes := Fin.lastCases (none, -1) (fun _ => (none, 0)),
          output := none, state := some (.inr 2) }
      else
        { inputTape := 0, workTapes := Fin.lastCases (none, 1) (fun _ => (none, 0)),
          output := none, state := none }

namespace UnaryRepeat

/-- Embed a body configuration; halting transfers control to the counter-advance phase. -/
def bodyConfig (cfg : Cfg k Bool State input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (State ⊕ Fin 3) input where
  state := some (cfg.state.elim (.inr 0) .inl)
  inputPos := cfg.inputPos
  workTapes := Fin.lastCases tape cfg.workTapes
  workTapePos := Fin.lastCases position cfg.workTapePos
  output := cfg.output

/-- A controller configuration between invocations, with all body heads restored. -/
def controlConfig (input : List Bool) (state : Option (State ⊕ Fin 3))
    (words : Fin k → List Bool) (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool) :
    Cfg (k + 1) Bool (State ⊕ Fin 3) input where
  state := state
  inputPos := 1
  workTapes := Fin.lastCases tape (fun i => tapeOfList (words i))
  workTapePos := Fin.lastCases position (fun _ => 0)
  output := output

theorem bodyConfig_words (state : Option State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool) :
    bodyConfig (wordsCfg input state words output) tape position =
      controlConfig input (some (state.elim (.inr 0) .inl)) words tape position output := rfl

theorem step_bodyConfig (body : MultiTapeTM k Bool State) (cfg : Cfg k Bool State input)
    (tape : ℤ → Option Bool) (position : ℤ) (h : cfg.state ≠ none) :
    body.repeatUnary.step (bodyConfig cfg tape position) =
      bodyConfig (body.step cfg) tape position := by
  obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp h
  simp only [step, bodyConfig, hs, Option.elim_some, repeatUnary_tr]
  simp only [Cfg.workTapeSymbols, Fin.lastCases_castSucc]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [Action.apply] <;> rfl

/-- A live prefix of the body runs unchanged inside the loop. -/
theorem runFrom_bodyConfig (body : MultiTapeTM k Bool State) (cfg : Cfg k Bool State input)
    (tape : ℤ → Option Bool) (position : ℤ) (time : ℕ)
    (hlive : ∀ t < time, (body.runFrom cfg t).state ≠ none) :
    body.repeatUnary.runFrom (bodyConfig cfg tape position) time =
      bodyConfig (body.runFrom cfg time) tape position := by
  induction time with
  | zero => rfl
  | succ time ih =>
    simp only [runFrom] at hlive ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun t ht => hlive t (by omega)), step_bodyConfig _ _ _ _ (hlive time (by omega))]

theorem step_check (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool)
    (h : tape position = some true) :
    body.repeatUnary.step (controlConfig input (some (.inr 1)) words tape position output) =
      bodyConfig (wordsCfg input (some body.q₀) words output) tape position := by
  simp only [step, controlConfig, repeatUnary_tr, Cfg.workTapeSymbols, Fin.lastCases_last,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, h]
  simp [Action.apply, bodyConfig, wordsCfg]

theorem step_advance (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool) :
    body.repeatUnary.step (controlConfig input (some (.inr 0)) words tape position output) =
      controlConfig input (some (.inr 1)) words tape (position + 1) output := by
  simp only [step, controlConfig, repeatUnary_tr, ↓reduceIte]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [Action.apply]

theorem step_check_end (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool)
    (h : tape position ≠ some true) :
    body.repeatUnary.step (controlConfig input (some (.inr 1)) words tape position output) =
      controlConfig input (some (.inr 2)) words tape (position - 1) output := by
  simp only [step, controlConfig, repeatUnary_tr, Cfg.workTapeSymbols, Fin.lastCases_last,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, h]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [Action.apply, sub_eq_add_neg]

theorem step_rewind (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool)
    (h : tape position = some true) :
    body.repeatUnary.step (controlConfig input (some (.inr 2)) words tape position output) =
      controlConfig input (some (.inr 2)) words tape (position - 1) output := by
  simp only [step, controlConfig, repeatUnary_tr, Cfg.workTapeSymbols, Fin.lastCases_last,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, h]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [Action.apply, sub_eq_add_neg]

theorem step_rewind_end (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (output : List Bool)
    (h : tape position ≠ some true) :
    body.repeatUnary.step (controlConfig input (some (.inr 2)) words tape position output) =
      controlConfig input none words tape (position + 1) output := by
  simp only [step, controlConfig, repeatUnary_tr, Cfg.workTapeSymbols, Fin.lastCases_last,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, h]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [Action.apply]

/-- Rewinding a unary counter restores its head without changing its contents. -/
theorem runFrom_rewind (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (count : ℕ) (output : List Bool) (index : ℕ) (h : index ≤ count) :
    body.repeatUnary.runFrom
      (controlConfig input (some (.inr 2)) words (tapeOfList (List.replicate count true))
        (index - 1 : ℤ) output) (index + 1) =
      controlConfig input none words (tapeOfList (List.replicate count true)) 0 output := by
  induction index with
  | zero =>
    rw [runFrom_one]
    rw [step_rewind_end _ _ _ _ _ (by change (none : Option Bool) ≠ some true; simp)]
    simp
  | succ index ih =>
    rw [runFrom, Function.iterate_succ_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [step_rewind _ _ _ _ _ (by simp [tapeOfList, show index < count by omega])]
    exact ih (by omega)

/-- A remaining segment of the counter executes the corresponding sequence of body states.
The body may halt earlier than the common bound on any invocation. -/
private theorem runFrom_check_states_exists (body : MultiTapeTM k Bool State)
    (words : ℕ → Fin k → List Bool) (output : ℕ → List Bool) (cost count : ℕ)
    (hbody : ∀ index < count,
      body.runFrom (wordsCfg input (some body.q₀) (words index) (output index)) cost =
        wordsCfg input none (words (index + 1)) (output (index + 1))) (remaining : ℕ) :
    ∀ index, index + remaining = count →
      ∃ time ≤ remaining * (cost + 2) + count + 2,
        body.repeatUnary.runFrom
          (controlConfig input (some (.inr 1)) (words index)
            (tapeOfList (List.replicate count true)) index (output index)) time =
          controlConfig input none (words count)
            (tapeOfList (List.replicate count true)) 0 (output count) := by
  induction remaining with
  | zero =>
    intro index h
    have : index = count := by lia
    subst index
    refine ⟨count + 2, by lia, ?_⟩
    rw [runFrom, Function.iterate_succ_apply]
    rw [step_check_end _ _ _ _ _ (by simp [tapeOfList])]
    exact runFrom_rewind body (words count) count (output count) count le_rfl
  | succ remaining ih =>
    intro index h
    have hi : index < count := by lia
    obtain ⟨time, htime, hhalts⟩ := exists_haltsAt (tm := body)
      (cfg := wordsCfg input (some body.q₀) (words index) (output index)) (t := cost)
      (by rw [hbody index hi]; rfl)
    have hrun :
        body.runFrom (wordsCfg input (some body.q₀) (words index) (output index)) time =
          wordsCfg input none (words (index + 1)) (output (index + 1)) := by
      rw [← hhalts.runFrom_eq htime, hbody index hi]
    have hblock : body.repeatUnary.runFrom
        (controlConfig input (some (.inr 1)) (words index)
          (tapeOfList (List.replicate count true)) index (output index)) (1 + time + 1) =
        controlConfig input (some (.inr 1)) (words (index + 1))
          (tapeOfList (List.replicate count true)) (index + 1 : ℕ) (output (index + 1)) := by
      rw [runFrom_add, runFrom_add, runFrom_one, runFrom_one]
      rw [step_check _ _ _ _ _ (by simp [tapeOfList, hi]),
        runFrom_bodyConfig _ _ _ _ _ hhalts.2, hrun, bodyConfig_words, Option.elim_none,
        step_advance]
      simp
    obtain ⟨tailTime, htailTime, htail⟩ := ih (index + 1) (by lia)
    refine ⟨1 + time + 1 + tailTime, ?_, ?_⟩
    · rw [Nat.succ_mul]
      lia
    · rw [runFrom_add, hblock, htail]

end UnaryRepeat

/-- A bounded loop may change its tape words and output on every invocation. A common runtime
bound is needed only for the configurations actually visited. All heads and the counter are
restored, and the final tape words and output are those of the last invocation. -/
theorem runFrom_repeatUnary_states (body : MultiTapeTM k Bool State)
    (words : ℕ → Fin k → List Bool) (output : ℕ → List Bool) (cost count : ℕ)
    (hbody : ∀ index < count,
      body.runFrom (wordsCfg input (some body.q₀) (words index) (output index)) cost =
        wordsCfg input none (words (index + 1)) (output (index + 1))) :
    body.repeatUnary.runFrom
      (wordsCfg input (some body.repeatUnary.q₀)
        (Fin.lastCases (List.replicate count true) (words 0)) (output 0))
      (count * (cost + 3) + 2) =
      wordsCfg input none (Fin.lastCases (List.replicate count true) (words count))
        (output count) := by
  have hcfg (state : Option (State ⊕ Fin 3)) (words : Fin k → List Bool) (output : List Bool) :
      wordsCfg input state (Fin.lastCases (List.replicate count true) words) output =
        UnaryRepeat.controlConfig input state words (tapeOfList (List.replicate count true))
          0 output := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
      simp [wordsCfg, UnaryRepeat.controlConfig]
  rw [hcfg, hcfg]
  simp only [repeatUnary_q₀]
  obtain ⟨time, htime, hrun⟩ :=
    UnaryRepeat.runFrom_check_states_exists body words output cost count hbody count 0 (by lia)
  simp only [Nat.cast_zero] at hrun
  have hle : time ≤ count * (cost + 3) + 2 := by simpa only [Nat.mul_succ] using htime
  rw [body.repeatUnary.runFrom_eq_of_halt _ hle (by rw [hrun]; rfl)]
  exact hrun

/-- The specialization to an output-producing body that preserves all its tape words. -/
theorem runFrom_repeatUnary (body : MultiTapeTM k Bool State) (words : Fin k → List Bool)
    (emit : List Bool → List Bool) (cost : ℕ)
    (hbody : ∀ output, body.runFrom (wordsCfg input (some body.q₀) words output) cost =
      wordsCfg input none words (emit output)) (count : ℕ) (output : List Bool) :
    body.repeatUnary.runFrom
      (wordsCfg input (some body.repeatUnary.q₀)
        (Fin.lastCases (List.replicate count true) words) output)
      (count * (cost + 3) + 2) =
      wordsCfg input none (Fin.lastCases (List.replicate count true) words)
        (emit^[count] output) := by
  apply runFrom_repeatUnary_states body (fun _ => words) (fun index => emit^[index] output)
  intro index _
  simpa only [Function.iterate_succ_apply'] using hbody (emit^[index] output)

/-- Iterate a tape-word transformation while a preserved invariant supplies a common body
bound. The body leaves the external output alone; all loop state lives on its work tapes. -/
theorem runFrom_repeatUnary_transform (body : MultiTapeTM k Bool State)
    (update : (Fin k → List Bool) → (Fin k → List Bool))
    (invariant : (Fin k → List Bool) → Prop) (cost count : ℕ)
    (hbody : ∀ words output, invariant words →
      body.runFrom (wordsCfg input (some body.q₀) words output) cost =
        wordsCfg input none (update words) output)
    (hpreserve : ∀ words, invariant words → invariant (update words))
    (words : Fin k → List Bool) (hwords : invariant words) (output : List Bool) :
    body.repeatUnary.runFrom
      (wordsCfg input (some body.repeatUnary.q₀)
        (Fin.lastCases (List.replicate count true) words) output)
      (count * (cost + 3) + 2) =
      wordsCfg input none (Fin.lastCases (List.replicate count true) (update^[count] words))
        output := by
  have hinvariant : ∀ index, invariant (update^[index] words) := by
    intro index
    induction index with
    | zero => exact hwords
    | succ index ih =>
      simpa only [Function.iterate_succ_apply'] using hpreserve _ ih
  apply runFrom_repeatUnary_states body (fun index => update^[index] words) (fun _ => output)
  intro index _
  simpa only [Function.iterate_succ_apply'] using hbody _ output (hinvariant index)

end Turing.MultiTapeTM
