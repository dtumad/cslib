/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Resumption
public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Resumption.Cost
public import Cslib.Foundations.Data.PFunctor.Resumption.State

/-!
# Expected polynomial time

A machine run without a budget (`runUnbounded`) is a resumption, whose runs that never halt are
infinite paths. A machine realizes a resumption (`RealizesUnbounded`) if, under every oracle
environment and from every state, the outputs of its halting runs and the final state are
distributed as the encoded outputs of the resumption and its final state; runs that never halt lose
mass on both sides.

The expected running time (`expectedTime`) counts transitions, each of which flips a coin, and a
family of resumptions is in expected polynomial time (`IsExpectedPolyTime`) if one finite-control
machine realizes it on every input within expected time `c * (n + 1) ^ d` on inputs of length `n`,
for every environment whose answers are at most probabilities. Programs in probabilistic polynomial
time are in expected polynomial time (`IsPPT.isExpectedPolyTime`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Turing.MultiTapePTM

open PFunctor MultiTapeMachine MultiTapeTM

variable {Oracle : Type}

namespace OracleEnv

variable (env : OracleEnv Oracle) {α : Type} [MeasurableSpace α]

/-- The joint distribution of the output of a resumption `r` and the final state, run from the
state `s`; runs that never return contribute no mass. -/
noncomputable def runR (r : Resumption (effects Oracle) α) (s : env.State) :
    Measure (α × env.State) :=
  (r.withState s).toMeasure env.sem

@[simp]
theorem runR_toResumption (x : (effects Oracle).FreeM α) (s : env.State) :
    env.runR x.toResumption s = env.run x s := by
  rw [runR, ← FreeM.toResumption_withState, FreeM.toMeasure_toResumption, run]

end OracleEnv

/-- Each coin costs one transition; sending a request takes the transition that flipped its coin. -/
def transitionCost : (effects Oracle).A → ℝ≥0∞
  | .inl () => 1
  | .inr _ => 0

variable {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
  {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle} {input : Word}

/-- `machine`, calling the oracle `dispatch p` through each port `p`, realizes the resumption `r` on
`input`: under every oracle environment and from every state, its halting outputs and the final
state are distributed as the encoded outputs of `r` and its final state. -/
def RealizesUnbounded (machine : MultiTapePTM k Bool State Ports) (dispatch : Ports → Oracle)
    (input : Word) (encode : α ↪ Word) (r : Resumption (effects Oracle) α) : Prop :=
  ∀ (env : OracleEnv Oracle) (s : env.State),
    (env.comap dispatch).runR
        ((fun cfg => cfg.tapes.output) <$> machine.runUnbounded (machine.initialConfig input)) s =
      env.runR (encode <$> r) s

/-- The expected number of transitions of `machine` on `input`, run from the state `s`. -/
noncomputable def expectedTime (machine : MultiTapePTM k Bool State Ports)
    (dispatch : Ports → Oracle) (env : OracleEnv Oracle) (input : Word) (s : env.State) : ℝ≥0∞ :=
  ((machine.runUnbounded (machine.initialConfig input)).withState s).expectedCost
    (env.comap dispatch).sem fun a => transitionCost a.1

/-- One finite-control machine with finitely many oracle ports realizes `r a` on `input a`, within
expected time `c * (n + 1) ^ d`, where `n` is its length, under every environment whose answers are
at most probabilities. -/
def IsExpectedPolyTime {β : Type} (input : α ↪ Word) (output : β ↪ Word)
    (r : α → Resumption (effects Oracle) β) : Prop :=
  Finite Oracle ∧ ∃ (k ports : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State (Fin ports)) (dispatch : Fin ports → Oracle) (c d : ℕ),
    ∀ a, machine.RealizesUnbounded dispatch (input a) output (r a) ∧
      ∀ env : OracleEnv Oracle, (∀ oracle word s, env.answer oracle word s Set.univ ≤ 1) →
        ∀ s, machine.expectedTime dispatch env (input a) s ≤ (c * ((input a).length + 1) ^ d : ℕ)

/-- Each path of a transition flips one coin. -/
theorem maxCost_step_le (machine : MultiTapePTM k Bool State Ports)
    (cfg : Config k Bool State Ports input) : (machine.step cfg).maxCost transitionCost ≤ 1 := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, hs, coin, bind_pure_comp, FreeM.maxCost_lift_bind', transitionCost]
    rw [ENNReal.iSup_eq_zero.mpr fun bit => ?_, add_zero]
    split <;> simp [query, transitionCost]

/-- Each path of a bounded run performs at most one transition per unit of budget. -/
theorem maxCost_runConfigFrom_le (machine : MultiTapePTM k Bool State Ports) (fuel : ℕ)
    (cfg : Config k Bool State Ports input) :
    (machine.runConfigFrom fuel cfg).maxCost transitionCost ≤ fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    refine (FreeM.maxCost_bind_le _ _ _).trans ?_
    rw [Nat.cast_succ, add_comm (fuel : ℝ≥0∞)]
    exact add_le_add (machine.maxCost_step_le cfg) (iSup_le ih)

/-- Under answers that are at most probabilities, a machine halting within a budget on every path
runs within that budget in expectation. -/
theorem HaltsWithin.expectedTime_le {fuel : ℕ}
    (h : machine.HaltsWithin fuel (machine.initialConfig input)) (env : OracleEnv Oracle)
    (henv : ∀ oracle word s, env.answer oracle word s Set.univ ≤ 1) (s : env.State) :
    machine.expectedTime dispatch env input s ≤ fuel := by
  rw [expectedTime, h.runUnbounded_eq, ← FreeM.toResumption_withState]
  refine (Resumption.expectedCost_toResumption_le _ _ (fun a => ?_) _).trans
    ((FreeM.maxCost_withState_le _ _ _).trans (machine.maxCost_runConfigFrom_le fuel _))
  rcases a with ⟨_ | ⟨port, word⟩, s⟩
  · rw [OracleEnv.sem, Measure.map_apply measurable_prodMk_right MeasurableSet.univ,
      Set.preimage_univ]
    exact prob_le_one
  · exact henv (dispatch port) word s

/-- A machine realizing a program within a budget on which it always halts realizes the program as a
resumption. -/
theorem Realizes.realizesUnbounded {fuel : ℕ} {encode : α ↪ Word}
    {program : (effects Oracle).FreeM α} (h : machine.Realizes dispatch fuel input encode program)
    (hhalt : machine.HaltsWithin fuel (machine.initialConfig input)) :
    machine.RealizesUnbounded dispatch input encode program.toResumption := by
  intro env s
  set run := machine.runConfigFrom fuel (machine.initialConfig input)
  have houtput : output? <$> run = some <$> (fun cfg => cfg.tapes.output) <$> run := by
    rw [← WeaklyLawfulMonadAttach.map_attach (x := run)]
    simp only [Functor.map_map]
    congr 1
    funext ⟨cfg, hcfg⟩
    simp [output?, hhalt cfg hcfg]
  have hsome : ∀ m m' : Measure (Word × env.State),
      m.map (Prod.map some id) = m'.map (Prod.map some id) → m = m' := fun m m' hm => by
    simpa [Measure.map_map Measurable.of_discrete Measurable.of_discrete, Function.comp_def]
      using congrArg (Measure.map fun p : Option Word × env.State => (p.1.getD [], p.2)) hm
  have hprogram : (fun a => some (encode a)) <$> program = some <$> encode <$> program := by
    simp [Functor.map_map]
  have := h env s
  rw [MultiTapePTM.run, runFrom, houtput, hprogram, OracleEnv.run_map (f := some),
    OracleEnv.run_map (f := some)] at this
  rw [hhalt.runUnbounded_eq, ← FreeM.toResumption_map', ← FreeM.toResumption_map',
    OracleEnv.runR_toResumption, OracleEnv.runR_toResumption]
  exact hsome _ _ this

/-- Probabilistic polynomial time programs are in expected polynomial time. -/
theorem IsPPT.isExpectedPolyTime {β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {program : α → (effects Oracle).FreeM β} (h : IsPPT input output program) :
    IsExpectedPolyTime input output fun a => (program a).toResumption := by
  obtain ⟨hf, k, ports, State, hs, machine, dispatch, c, d, hm⟩ := h
  exact ⟨hf, k, ports, State, hs, machine, dispatch, c, d, fun a =>
    ⟨(hm a).2.realizesUnbounded (hm a).1, fun env henv s => (hm a).1.expectedTime_le env henv s⟩⟩

end Turing.MultiTapePTM
