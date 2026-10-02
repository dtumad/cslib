/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Closed
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput

/-!
# Composing closed machines through a buffered word
The source has its own work tapes and writes its result to a fresh buffer. A deterministic
handoff rewinds the buffer and installs a boundary marker. The continuation then uses this word
as its input, with separate blank work tapes. Both machines' empty-answer oracles are handled
locally, so the continuation starts with clean communication tapes.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

namespace Composition

variable {k₀ k₁ : ℕ} {State₀ State₁ OracleState : Type} {input : List Bool}

/-- Reserve blank continuation tapes before the source's work tapes. -/
def reserve (k₁ : ℕ) (cfg : Config k₀ State₀ input) : Config (k₁ + k₀) State₀ input :=
  (Closed.config cfg).embed (Fin.natAddEmb k₁) (fun _ _ => none) (fun _ => 0)

/-- Buffer the source result and reserve a blank boundary-marker tape. -/
def buffer (k₁ : ℕ) (cfg : Config k₀ State₀ input) : Config (k₁ + k₀ + 2) State₀ input :=
  (OutputToTape.config (reserve k₁ cfg)).embed Fin.castSuccEmb (fun _ _ => none) (fun _ => 0)

/-- The source phase writes no real output and makes no external queries. -/
def source (machine : OracleTM k₀ State₀) (k₁ : ℕ) : OracleTM (k₁ + k₀ + 2) State₀ :=
  ((machine.closed.extendTapes (Fin.natAddEmb k₁)).outputToTape).extendTapes Fin.castSuccEmb

/-- Run the continuation with the buffer as its input and retain the source's scratch tapes. -/
def consumer (machine : OracleTM k₁ State₁) (k₀ : ℕ) : OracleTM (k₁ + k₀ + 2) State₁ :=
  (machine.closed.extendTapes (Fin.castAddEmb k₀)).inputFromTape

/-- The continuation's work tapes are separate from the source's preserved scratch tapes. -/
def consumerConfig (cfg₀ : Config k₀ State₀ input)
    (cfg₁ : Config k₁ State₁ cfg₀.tapes.output) : Config (k₁ + k₀ + 2) State₁ input :=
  InputFromTape.config
    ((Closed.config cfg₁).embed (Fin.castAddEmb k₀)
      (reserve k₁ cfg₀).tapes.workTapes (reserve k₁ cfg₀).tapes.workTapePos)
    input cfg₀.tapes.inputPos

/-- Deterministic handoff followed by the continuation. -/
def continuation (machine : OracleTM k₁ State₁) (k₀ : ℕ) :
    OracleTM (k₁ + k₀ + 2) (MultiTapeTM.PrepareInput.Control ⊕ State₁) :=
  (ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀))).seq (consumer machine k₀)

theorem runState_source (machine : OracleTM k₀ State₀) (k₁ : ℕ)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ)
    (input : List Bool) (s : OracleState) :
    OracleComp.runState oracle
      ((source machine k₁).runConfigFrom fuel ((source machine k₁).initialConfig input)) s =
      (OracleComp.eval (fun _ => PMF.pure [])
        (machine.runConfigFrom fuel (machine.initialConfig input))).map
        (fun final => (buffer k₁ final, s)) := by
  simp only [source, initialConfig_extendTapes, initialConfig_outputToTape,
    runConfigFrom_embed, runConfigFrom_outputToTape, OracleComp.runState_map]
  have h := runState_runConfigFrom_closed machine oracle fuel (machine.initialConfig input) s rfl
  change OracleComp.runState oracle
    (machine.closed.runConfigFrom fuel (machine.closed.initialConfig input)) s = _ at h
  rw [h]
  simp only [PMF.map_comp]
  rfl

theorem runState_consumer (machine : OracleTM k₁ State₁) (cfg₀ : Config k₀ State₀ input)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ) (s : OracleState) :
    OracleComp.runState oracle
      ((consumer machine k₀).runConfigFrom fuel
        (consumerConfig cfg₀ (machine.initialConfig cfg₀.tapes.output))) s =
      (OracleComp.eval (fun _ => PMF.pure [])
        (machine.runConfigFrom fuel (machine.initialConfig cfg₀.tapes.output))).map
        (fun final => (consumerConfig cfg₀ final, s)) := by
  simp only [consumer, consumerConfig, runConfigFrom_inputFromTape, runConfigFrom_embed,
    OracleComp.runState_map, runState_runConfigFrom_closed machine oracle fuel
      (machine.initialConfig cfg₀.tapes.output) s rfl,
    PMF.map_comp]
  rfl

private theorem partialInv_natAdd_castAdd (k₀ k₁ : ℕ) (i : Fin k₁) :
    MultiTapeTM.partialInv (Fin.natAddEmb k₁) (Fin.castAdd k₀ i) = none := by
  apply MultiTapeTM.partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := i.isLt
  simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at *
  omega

private theorem partialInv_castAdd_natAdd (k₀ k₁ : ℕ) (i : Fin k₀) :
    MultiTapeTM.partialInv (Fin.castAddEmb k₀) (Fin.natAdd k₁ i) = none := by
  apply MultiTapeTM.partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at *
  omega

/-- The deterministic handoff produces the continuation's initial virtual-input configuration. -/
theorem prepared (machine : OracleTM k₁ State₁) (cfg : Config k₀ State₀ input) :
    ({ tapes := MultiTapeTM.PrepareInput.after (reserve k₁ cfg).tapes (some machine.initial) } :
      Config (k₁ + k₀ + 2) State₁ input) =
      consumerConfig cfg (machine.initialConfig cfg.tapes.output) := by
  refine Config.ext ?_ rfl rfl rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    simp only [MultiTapeTM.PrepareInput.after_workTapes_castAdd,
      MultiTapeTM.PrepareInput.after_workTapePos_castAdd]
    induction i using Fin.addCases with
    | left i =>
      have hi := MultiTapeTM.partialInv_embed (Fin.castAddEmb k₀) i
      simp only [Fin.castAddEmb_apply] at hi
      simp [consumerConfig, InputFromTape.config,
        MultiTapeTM.inCfg, Config.embed, MultiTapeTM.embed, Closed.config, reserve,
        initialConfig, Cfg.init, hi, partialInv_natAdd_castAdd]
    | right i =>
      simp [consumerConfig, InputFromTape.config,
        MultiTapeTM.inCfg, Config.embed, MultiTapeTM.embed, Closed.config, reserve,
        partialInv_castAdd_natAdd]
  | right i =>
    fin_cases i <;>
      simp [consumerConfig, InputFromTape.config,
        MultiTapeTM.inCfg, Config.embed, MultiTapeTM.embed, Closed.config, reserve,
        initialConfig, Cfg.init, MultiTapeTM.PrepareInput.flag]

theorem consumer_halted (machine : OracleTM k₁ State₁) (cfg : Config k₀ State₀ input)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (fuel : ℕ) (s : OracleState)
    (hhalt : machine.HaltsWithin fuel cfg.tapes.output) :
    ∀ result ∈ (OracleComp.runState oracle
      ((consumer machine k₀).runConfigFrom fuel
        (consumerConfig cfg (machine.initialConfig cfg.tapes.output))) s).support,
      result.1.tapes.state = none := by
  intro result hresult
  rw [runState_consumer] at hresult
  obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
  exact hhalt.eval _ final hfinal

/-- Handoff and continuation have the expected distribution once both bounds have been paid. -/
theorem runState_continuation (machine : OracleTM k₁ State₁) (cfg : Config k₀ State₀ input)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (prepareTime runTime : ℕ) (s : OracleState)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime cfg.tapes.output) :
    OracleComp.runState oracle
      ((continuation machine k₀).runConfigFrom (prepareTime + runTime)
        (Sequential.start (continuation machine k₀) (buffer k₁ cfg))) s =
      (OracleComp.eval (fun _ => PMF.pure [])
        (machine.runConfigFrom runTime (machine.initialConfig cfg.tapes.output))).map
        (fun final => (Prepend.right (consumerConfig cfg final), s)) := by
  let preparation := MultiTapeTM.prepareInput (k₁ + k₀)
  let initial : Config (k₁ + k₀ + 2) MultiTapeTM.PrepareInput.Control input :=
    { tapes := (MultiTapeTM.PrepareInput.before (reserve k₁ cfg).tapes).withState
        (some preparation.q₀) }
  let ready : Config (k₁ + k₀ + 2) MultiTapeTM.PrepareInput.Control input :=
    { tapes := MultiTapeTM.PrepareInput.after (reserve k₁ cfg).tapes none }
  have hdet := MultiTapeTM.runFrom_prepareInput (reserve k₁ cfg).tapes
  change preparation.runFrom initial.tapes (cfg.tapes.output.length + 4) = ready.tapes at hdet
  have hprep : preparation.runFrom initial.tapes prepareTime = ready.tapes := by
    rw [preparation.runFrom_eq_of_halt initial.tapes hprepare (by rw [hdet]; rfl), hdet]
  have hstate : OracleComp.runState oracle
      ((ofDeterministic preparation).runConfigFrom prepareTime initial) s =
      PMF.pure (ready, s) := by
    rw [runState_runConfigFrom_ofDeterministic, hprep]
  have hready : Sequential.start (consumer machine k₀) ready =
      consumerConfig cfg (machine.initialConfig cfg.tapes.output) := prepared machine cfg
  change OracleComp.runState oracle
    (((ofDeterministic preparation).seq (consumer machine k₀)).runConfigFrom
      (prepareTime + runTime) (Sequential.left (consumer machine k₀) initial)) s = _
  rw [runState_runConfigFrom_seq _ _ oracle initial prepareTime runTime s
    (by
      intro result hresult
      rw [hstate, PMF.mem_support_pure_iff] at hresult
      subst result
      rfl)
    (by
      intro result hresult
      rw [hstate, PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [hready] using consumer_halted machine cfg oracle runTime s hrun),
    hstate, PMF.pure_bind]
  simp only [hready, runState_consumer, PMF.map_comp]
  rfl

theorem continuation_halted (machine : OracleTM k₁ State₁) (cfg : Config k₀ State₀ input)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (prepareTime runTime : ℕ) (s : OracleState)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime cfg.tapes.output) :
    ∀ result ∈ (OracleComp.runState oracle
      ((continuation machine k₀).runConfigFrom (prepareTime + runTime)
        (Sequential.start (continuation machine k₀) (buffer k₁ cfg))) s).support,
      result.1.tapes.state = none := by
  intro result hresult
  rw [runState_continuation machine cfg oracle prepareTime runTime s hprepare hrun] at hresult
  obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
  change final.tapes.state.map Sum.inr = none
  rw [hrun.eval _ final hfinal]
  rfl

/-- The two control-state embeddings of a completed composition. -/
def finalConfig (cfg₀ : Config k₀ State₀ input)
    (cfg₁ : Config k₁ State₁ cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) (State₀ ⊕ (MultiTapeTM.PrepareInput.Control ⊕ State₁)) input :=
  Prepend.right (Prepend.right (consumerConfig cfg₀ cfg₁))

@[simp] theorem finalConfig_output (cfg₀ : Config k₀ State₀ input)
    (cfg₁ : Config k₁ State₁ cfg₀.tapes.output) :
    (finalConfig cfg₀ cfg₁).tapes.output = cfg₁.tapes.output := rfl

theorem output_mem (machine : OracleTM k₀ State₀) (fuel : ℕ) (input : List Bool)
    (final : Config k₀ State₀ input)
    (hfinal : final ∈ (OracleComp.eval (fun _ => PMF.pure [])
      (machine.runConfigFrom fuel (machine.initialConfig input))).support) :
    final.tapes.output ∈
      (OracleComp.eval (fun _ => PMF.pure []) (machine.run fuel input)).support := by
  rw [run, runFrom_eq_map_runConfigFrom, OracleComp.eval_map]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

end Composition

/-- Feed one closed machine's output to another using disjoint work tapes and a buffered input. -/
def comp {k₀ k₁ : ℕ} {State₀ State₁ : Type}
    (first : OracleTM k₀ State₀) (second : OracleTM k₁ State₁) :
    OracleTM (k₁ + k₀ + 2) (State₀ ⊕ (MultiTapeTM.PrepareInput.Control ⊕ State₁)) :=
  (Composition.source first k₁).seq (Composition.continuation second k₀)

variable {k₀ k₁ : ℕ} {State₀ State₁ OracleState : Type}

/-- Closed machine composition realizes monadic sequencing. The source takes at most `firstTime`
steps; preparing its output takes at most `firstTime + 4`; the continuation takes `secondTime`.
The full final configurations are retained, and the external oracle state is untouched. -/
theorem runState_runConfigFrom_comp (first : OracleTM k₀ State₀) (second : OracleTM k₁ State₁)
    (input : List Bool) (firstTime secondTime : ℕ)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (s : OracleState)
    (hfirst : first.HaltsWithin firstTime input)
    (hsecond :
      ∀ word ∈ (OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).support,
      second.HaltsWithin secondTime word) :
    OracleComp.runState oracle
      ((first.comp second).runConfigFrom (firstTime + (firstTime + 4 + secondTime))
        ((first.comp second).initialConfig input)) s =
      (OracleComp.eval (fun _ => PMF.pure [])
        (first.runConfigFrom firstTime (first.initialConfig input))).bind
        (fun sourceFinal => (OracleComp.eval (fun _ => PMF.pure [])
          (second.runConfigFrom secondTime (second.initialConfig sourceFinal.tapes.output))).map
          (fun final => (Composition.finalConfig sourceFinal final, s))) := by
  have hlength (final : Config k₀ State₀ input)
      (hfinal : final ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (first.runConfigFrom firstTime (first.initialConfig input))).support) :
      final.tapes.output.length ≤ firstTime := by
    have h := length_output_eval_runFrom_le first _ firstTime (first.initialConfig input)
      final.tapes.output (Composition.output_mem first firstTime input final hfinal)
    simpa [initialConfig] using h
  change OracleComp.runState oracle
    (((Composition.source first k₁).seq (Composition.continuation second k₀)).runConfigFrom _
      (Sequential.left (Composition.continuation second k₀)
        ((Composition.source first k₁).initialConfig input))) s = _
  rw [runState_runConfigFrom_seq _ _ oracle _ firstTime (firstTime + 4 + secondTime) s
    (by
      intro result hresult
      rw [Composition.runState_source] at hresult
      obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact hfirst.eval _ final hfinal)
    (by
      intro result hresult
      rw [Composition.runState_source] at hresult
      obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact Composition.continuation_halted second final oracle (firstTime + 4) secondTime s
        (by have := hlength final hfinal; omega)
        (hsecond _ (Composition.output_mem first firstTime input final hfinal))),
    Composition.runState_source, PMF.bind_map]
  apply Probability.PMF.bind_congr_on_support
  intro final hfinal
  dsimp only [Function.comp_def]
  rw [Composition.runState_continuation second final oracle (firstTime + 4) secondTime s
    (by have := hlength final hfinal; omega)
    (hsecond _ (Composition.output_mem first firstTime input final hfinal)), PMF.map_comp]
  rfl

/-- At the output level, the compiled machine samples the first result and runs the second on it. -/
theorem runState_comp (first : OracleTM k₀ State₀) (second : OracleTM k₁ State₁)
    (input : List Bool) (firstTime secondTime : ℕ)
    (oracle : List Bool → StateT OracleState PMF (List Bool)) (s : OracleState)
    (hfirst : first.HaltsWithin firstTime input)
    (hsecond :
      ∀ word ∈ (OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).support,
      second.HaltsWithin secondTime word) :
    OracleComp.runState oracle
      ((first.comp second).run (firstTime + (firstTime + 4 + secondTime)) input) s =
      ((OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).bind
        (fun word => OracleComp.eval (fun _ => PMF.pure []) (second.run secondTime word))).map
        (fun output => (output, s)) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_comp first second input firstTime secondTime oracle s hfirst hsecond)
  simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.runState_map, OracleComp.eval_map,
    PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def] using h

/-- Closed evaluation of the compiled machine is the bind of the original output distributions. -/
theorem eval_comp (first : OracleTM k₀ State₀) (second : OracleTM k₁ State₁)
    (input : List Bool) (firstTime secondTime : ℕ)
    (hfirst : first.HaltsWithin firstTime input)
    (hsecond :
      ∀ word ∈ (OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).support,
      second.HaltsWithin secondTime word) :
    OracleComp.eval (fun _ => PMF.pure [])
      ((first.comp second).run (firstTime + (firstTime + 4 + secondTime)) input) =
      (OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).bind
        (fun word => OracleComp.eval (fun _ => PMF.pure []) (second.run secondTime word)) := by
  have h := congrArg (PMF.map Prod.fst) (runState_comp first second input firstTime secondTime
    (fun _ (s : Unit) => (PMF.pure []).map (fun answer => (answer, s))) () hfirst hsecond)
  rw [OracleComp.runState_stateless] at h
  simpa [PMF.map, Function.comp_def] using h

/-- The composed machine really halts within the combined bound. -/
theorem HaltsWithin.comp {first : OracleTM k₀ State₀} {second : OracleTM k₁ State₁}
    {input : List Bool} {firstTime secondTime : ℕ}
    (hfirst : first.HaltsWithin firstTime input)
    (hsecond :
      ∀ word ∈ (OracleComp.eval (fun _ => PMF.pure []) (first.run firstTime input)).support,
      second.HaltsWithin secondTime word) :
    (first.comp second).HaltsWithin (firstTime + (firstTime + 4 + secondTime)) input := by
  intro OracleState oracle s final s' hfinal
  rw [runState_runConfigFrom_comp first second input firstTime secondTime oracle s hfirst hsecond]
    at hfinal
  obtain ⟨sourceFinal, hsource, htarget⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
  obtain ⟨targetFinal, htarget, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp htarget
  have hhalt := (hsecond _ (Composition.output_mem first firstTime input sourceFinal hsource)).eval
    _ targetFinal htarget
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  simpa [Composition.finalConfig, Prepend.right_state, Composition.consumerConfig,
    InputFromTape.config_state, Config.embed_state, Closed.config_state, hhalt] using hstate.symm

end Turing.OracleTM
