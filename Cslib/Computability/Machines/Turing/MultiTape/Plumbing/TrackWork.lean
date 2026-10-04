/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tracking scratch-tape intervals

Each source work tape receives a companion tape whose head moves in lockstep. The origin is
marked `true`; all other visited cells are marked `false`. One transition executes the source
action, and another marks the newly reached cell. Initialization costs one additional transition.

`runFrom_machine` proves exact simulation after `2 * time + 1` transitions. The resulting
marker intervals cover every nonblank source cell, contain both the origin and current head,
and lie in `[-time, time]`. These are precisely the hypotheses required by `ClearWork`.
The proof also covers a source that halts early; tracking then remains halted with its final
markers intact. The construction adds no dependence on the input to the finite control.
-/

@[expose] public section

open Turing
namespace Turing.MultiTapeTM.TrackWork

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Simulate each source transition and mark the new work-head positions. -/
def machine (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + k) Bool (Option (State ⊕ Option State)) where
  q₀ := none
  tr phase symbol work :=
    match phase with
    | none =>
      { inputTape := 0, workTapes := Fin.addCases (fun _ => (none, 0))
          (fun _ => (some (some true), 0)),
        output := none, state := some (some (.inl tm.q₀)) }
    | some (.inl state) =>
      let action := tm.tr state symbol (fun i => work (i.castAdd k))
      { inputTape := action.inputTape,
        workTapes := Fin.addCases action.workTapes (fun i => (none, (action.workTapes i).2)),
        output := action.output, state := some (some (.inr action.state)) }
    | some (.inr state) =>
      { inputTape := 0,
        workTapes := Fin.addCases (fun _ => (none, 0))
          (fun i => (some (some ((work (Fin.natAdd k i)).getD false)), 0)),
        output := none, state := state.map (fun q => some (.inl q)) }

/-- Place the source tapes and their companion markers on two equal blocks of tapes. -/
def cfg (source : Cfg k Bool State input) (markers : Fin k → ℤ → Option Bool)
    (state : Option (Option (State ⊕ Option State))) :
    Cfg (k + k) Bool (Option (State ⊕ Option State)) input where
  state := state
  inputPos := source.inputPos
  workTapes := Fin.addCases source.workTapes markers
  workTapePos := Fin.addCases source.workTapePos source.workTapePos
  output := source.output

/-- A configuration ready for the next source transition, or halted with the source. -/
def ready (source : Cfg k Bool State input) (markers : Fin k → ℤ → Option Bool) :=
  cfg source markers (source.state.map (fun q => some (.inl q)))

private def pending (source : Cfg k Bool State input) (markers : Fin k → ℤ → Option Bool) :=
  cfg source markers (some (some (.inr source.state)))

private def mark (source : Cfg k Bool State input) (markers : Fin k → ℤ → Option Bool) :=
  fun i => Function.update (markers i) (source.workTapePos i)
    (some ((markers i (source.workTapePos i)).getD false))

private theorem step_ready (tm : MultiTapeTM k Bool State) (source : Cfg k Bool State input)
    (markers : Fin k → ℤ → Option Bool) (h : source.state ≠ none) :
    (machine tm).step (ready source markers) = pending (tm.step source) markers := by
  obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp h
  simp only [step, ready, cfg, pending, hs, Option.map_some, machine]
  simp only [Cfg.workTapeSymbols, Fin.addCases_left]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases <;>
    simp [Action.apply, -Fin.natAdd_eq_addNat] <;> rfl

private theorem step_pending (tm : MultiTapeTM k Bool State) (source : Cfg k Bool State input)
    (markers : Fin k → ℤ → Option Bool) :
    (machine tm).step (pending source markers) = ready source (mark source markers) := by
  simp only [step, ready, cfg, pending, machine]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply]) <;>
    funext i <;> induction i using Fin.addCases <;>
      simp [Action.apply, mark, Cfg.workTapeSymbols, -Fin.natAdd_eq_addNat]

private theorem runFrom_ready_live (tm : MultiTapeTM k Bool State) (source : Cfg k Bool State input)
    (markers : Fin k → ℤ → Option Bool) (h : source.state ≠ none) :
    (machine tm).runFrom (ready source markers) 2 =
      ready (tm.step source) (mark (tm.step source) markers) := by
  rw [show 2 = 1 + 1 from rfl, runFrom_add, runFrom_one, runFrom_one,
    step_ready _ _ _ h, step_pending]

private theorem step_init (tm : MultiTapeTM k Bool State) (input : List Bool) :
    (machine tm).step ((machine tm).initCfg input) =
      ready (tm.initCfg input) (fun _ => ClearWork.marks 0 0) := by
  simp only [step, initCfg, Cfg.init, machine, ready, cfg]
  refine Cfg.ext rfl (by simp [Action.apply]) ?_ ?_ (by simp [Action.apply])
  · funext i
    induction i using Fin.addCases with
    | left i => simp [Action.apply]
    | right i =>
      simp only [Action.apply, Fin.addCases_right]
      funext z
      by_cases hz : z = 0
      · simp [hz, ClearWork.marks]
      · have : ¬(0 ≤ z ∧ z ≤ 0) := by lia
        simp [Function.update_of_ne hz, this, ClearWork.marks]
  · funext i
    induction i using Fin.addCases <;> simp [Action.apply, -Fin.natAdd_eq_addNat]

private theorem mark_interval (lo hi position : ℤ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hpos : lo - 1 ≤ position ∧ position ≤ hi + 1) :
    Function.update (ClearWork.marks lo hi) position
      (some ((ClearWork.marks lo hi position).getD false)) =
        ClearWork.marks (min lo position) (max hi position) := by
  funext z
  by_cases hz : z = position
  · subst z
    simp only [Function.update_self, ClearWork.marks]
    have hnew : min lo position ≤ position ∧ position ≤ max hi position :=
      ⟨min_le_right _ _, le_max_right _ _⟩
    rw [ite_eq_left hnew]
    by_cases hp : position = 0
    · subst position; simp [hlo, hhi]
    · by_cases hb : lo ≤ position ∧ position ≤ hi <;> simp [hp, hb]
  · rw [Function.update_of_ne hz]
    simp only [ClearWork.marks]
    have hrange : (lo ≤ z ∧ z ≤ hi) ↔ (min lo position ≤ z ∧ z ≤ max hi position) := by
      constructor <;> intro h <;> simp only [min_le_iff, le_max_iff] at * <;> lia
    simp only [hrange]

private theorem mark_eq_self (source : Cfg k Bool State input) (markers : Fin k → ℤ → Option Bool)
    (h : ∀ i, markers i (source.workTapePos i) ≠ none) :
    mark source markers = markers := by
  funext i z
  obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists'.mp (h i)
  by_cases hz : z = source.workTapePos i
  · subst z; simp [mark, hbit]
  · simp [mark, hz]

private theorem runFrom_ready (tm : MultiTapeTM k Bool State) (source : Cfg k Bool State input)
    (markers : Fin k → ℤ → Option Bool)
    (h : ∀ i, markers i (source.workTapePos i) ≠ none) :
    (machine tm).runFrom (ready source markers) 2 =
      ready (tm.step source) (mark (tm.step source) markers) := by
  by_cases hs : source.state = none
  · rw [step_of_halt hs, mark_eq_self _ _ h]
    have hhalt : (ready source markers).state = none := by simp [ready, cfg, hs]
    rw [runFrom_eq_of_halt _ _ (Nat.zero_le 2) (by exact hhalt), runFrom_zero]
  · exact runFrom_ready_live tm source markers hs

/-- A marker interval covers the origin, the current head, and every nonblank data cell. -/
def Valid (source : Cfg k Bool State input) (lo hi : Fin k → ℤ) (time : ℕ) : Prop :=
  ∀ i, lo i ≤ 0 ∧ 0 ≤ hi i ∧ -(time : ℤ) ≤ lo i ∧ hi i ≤ time ∧
    lo i ≤ source.workTapePos i ∧ source.workTapePos i ≤ hi i ∧
      ∀ z, z < lo i ∨ hi i < z → source.workTapes i z = none

private theorem Valid.step (tm : MultiTapeTM k Bool State) (source : Cfg k Bool State input)
    (lo hi : Fin k → ℤ) (time : ℕ) (h : Valid source lo hi time) :
    Valid (tm.step source) (fun i => min (lo i) ((tm.step source).workTapePos i))
      (fun i => max (hi i) ((tm.step source).workTapePos i)) (time + 1) := by
  intro i
  obtain ⟨hlo, hhi, hlower, hupper, hleft, hright, hdata⟩ := h i
  have hmove := abs_le.mp (tm.workTapePos_step_le source i)
  refine ⟨by exact (min_le_left _ _).trans hlo, by exact hhi.trans (le_max_left _ _),
    ?_, ?_, min_le_right _ _, le_max_right _ _, ?_⟩
  · simp only [le_min_iff]; constructor <;> lia
  · simp only [max_le_iff]; constructor <;> lia
  · intro z hz
    have hne : z ≠ source.workTapePos i := by
      simp only [lt_min_iff, max_lt_iff] at hz
      lia
    rw [step_workTapes_eq_of_ne source i z hne]
    apply hdata z
    simp only [lt_min_iff, max_lt_iff] at hz
    lia

/-- Exact simulation with marker intervals sufficient for linear-time tape cleanup. -/
theorem runFrom_machine (tm : MultiTapeTM k Bool State) (input : List Bool) (time : ℕ) :
    ∃ lo hi, Valid (tm.runFrom (tm.initCfg input) time) lo hi time ∧
      (machine tm).runFrom ((machine tm).initCfg input) (2 * time + 1) =
        ready (tm.runFrom (tm.initCfg input) time) (fun i => ClearWork.marks (lo i) (hi i)) := by
  induction time with
  | zero =>
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
    · intro i
      simp [runFrom_zero]
    · simpa only [Nat.mul_zero, Nat.zero_add, runFrom_zero, runFrom_one] using step_init tm input
  | succ time ih =>
    obtain ⟨lo, hi, hvalid, hrun⟩ := ih
    let source := tm.runFrom (tm.initCfg input) time
    change Valid source lo hi time at hvalid
    have hstep : tm.runFrom (tm.initCfg input) (time + 1) = tm.step source := by
      rw [runFrom, Function.iterate_succ_apply']
      rfl
    refine ⟨fun i => min (lo i) ((tm.step source).workTapePos i),
      fun i => max (hi i) ((tm.step source).workTapePos i), ?_, ?_⟩
    · rw [hstep]
      exact hvalid.step tm source lo hi time
    · rw [show 2 * (time + 1) + 1 = (2 * time + 1) + 2 by lia, runFrom_add, hrun]
      have hmarked : ∀ i, ClearWork.marks (lo i) (hi i) (source.workTapePos i) ≠ none := by
        intro i
        have hv := hvalid i
        simp [ClearWork.marks, hv.2.2.2.2.1, hv.2.2.2.2.2.1]
      rw [runFrom_ready tm source _ hmarked, hstep]
      congr 1
      funext i
      apply mark_interval (lo i) (hi i) ((tm.step source).workTapePos i)
        (hvalid i).1 (hvalid i).2.1
      have hv := hvalid i
      have hmove := abs_le.mp (tm.workTapePos_step_le source i)
      lia


end Turing.MultiTapeTM.TrackWork
