/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendChannels
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
import Mathlib.Tactic.FinCases

/-!
# Composing machines through a buffered result

The source writes its result to a fresh work tape. A deterministic handoff marks the input
boundary and rewinds that buffer. The continuation then reads the buffer using separate work
tapes and communication ports. Both sets of ports may be bound to the same stateful oracle.
Preparing the intermediate input costs its length plus four transitions.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

namespace Composition

variable {k₀ k₁ ports₀ ports₁ : ℕ} {State₀ State₁ : Type} {input : List Bool}

/-- Reserve the continuation's blank work tapes and communication ports. -/
def reserve (k₁ ports₁ : ℕ) (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    Config (k₁ + k₀) Bool State₀ (Fin (ports₀ + ports₁)) input :=
  ExtendTapes.config (ExtendChannels.config cfg (Fin.castAddEmb ports₁) (fun _ => {}))
    (Fin.natAddEmb k₁) (fun _ _ => none) (fun _ => 0)

/-- Buffer the source output and leave the boundary-marker tape blank. -/
def buffer (k₁ ports₁ : ℕ) (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    Config (k₁ + k₀ + 2) Bool State₀ (Fin (ports₀ + ports₁)) input :=
  ExtendTapes.config (OutputToTape.config (reserve k₁ ports₁ cfg))
    Fin.castSuccEmb (fun _ _ => none) (fun _ => 0)

/-- The source phase writes its output to the buffer and uses the left communication ports. -/
def source (machine : MultiTapePTM k₀ Bool State₀ (Fin ports₀)) (k₁ ports₁ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₀ (Fin (ports₀ + ports₁)) :=
  let named := machine.extendChannels (Fin.castAddEmb ports₁)
  ((named.extendTapes (Fin.natAddEmb k₁)).outputToTape).extendTapes Fin.castSuccEmb

/-- The continuation reads the buffered input, with its own work tapes and right-hand ports. -/
def consumer (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁)) (k₀ ports₀ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₁ (Fin (ports₀ + ports₁)) :=
  ((machine.extendChannels (Fin.natAddEmb ports₀)).extendTapes (Fin.castAddEmb k₀)).inputFromTape

/-- Preserve the source's data while embedding a continuation configuration. -/
def consumerConfig (cfg₀ : Config k₀ Bool State₀ (Fin ports₀) input)
    (cfg₁ : Config k₁ Bool State₁ (Fin ports₁) cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) Bool State₁ (Fin (ports₀ + ports₁)) input :=
  InputFromTape.config
    (ExtendTapes.config
      (ExtendChannels.config cfg₁ (Fin.natAddEmb ports₀) (reserve k₁ ports₁ cfg₀).channels)
      (Fin.castAddEmb k₀) (reserve k₁ ports₁ cfg₀).tapes.workTapes
      (reserve k₁ ports₁ cfg₀).tapes.workTapePos) input cfg₀.tapes.inputPos

/-- Rewind and mark the intermediate input before starting the continuation. -/
def continuation (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁)) (k₀ ports₀ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool (MultiTapeTM.PrepareInput.Control ⊕ State₁)
      (Fin (ports₀ + ports₁)) :=
  (ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀))).seq (consumer machine k₀ ports₀)

theorem runConfigFrom_source (machine : MultiTapePTM k₀ Bool State₀ (Fin ports₀))
    (k₁ ports₁ fuel : ℕ) (input : List Bool) :
    (source machine k₁ ports₁).runConfigFrom fuel
        ((source machine k₁ ports₁).initialConfig input) =
      buffer k₁ ports₁ <$>
        (machine.runConfigFrom fuel (machine.initialConfig input)).liftM
          (rename (Fin.castAddEmb ports₁)) := by
  simp only [source, initialConfig_extendTapes, initialConfig_outputToTape,
    initialConfig_extendChannels, runConfigFrom_embed, runConfigFrom_outputToTape,
    runConfigFrom_extendChannels, ← comp_map]
  rfl

theorem runConfigFrom_consumer (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg₀ : Config k₀ Bool State₀ (Fin ports₀) input)
    (cfg₁ : Config k₁ Bool State₁ (Fin ports₁) cfg₀.tapes.output) (fuel : ℕ) :
    (consumer machine k₀ ports₀).runConfigFrom fuel (consumerConfig cfg₀ cfg₁) =
      consumerConfig cfg₀ <$>
        (machine.runConfigFrom fuel cfg₁).liftM (rename (Fin.natAddEmb ports₀)) := by
  simp only [consumer, consumerConfig, runConfigFrom_inputFromTape, runConfigFrom_embed,
    runConfigFrom_extendChannels, ← comp_map]
  rfl

theorem partialInv_natAdd_castAdd (left right : ℕ) (i : Fin left) :
    MultiTapeTM.partialInv (Fin.natAddEmb left) (Fin.castAdd right i) = none := by
  apply MultiTapeTM.partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := i.isLt
  simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at *
  omega

theorem partialInv_castAdd_natAdd (left right : ℕ) (i : Fin right) :
    MultiTapeTM.partialInv (Fin.castAddEmb right) (Fin.natAdd left i) = none := by
  apply MultiTapeTM.partialInv_eq_none
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at *
  omega

/-- The physical handoff produces the continuation's initial virtual input and blank ports. -/
theorem prepared (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    ({ tapes := MultiTapeTM.PrepareInput.after (reserve k₁ ports₁ cfg).tapes (some machine.initial)
       channels := (reserve k₁ ports₁ cfg).channels } :
      Config (k₁ + k₀ + 2) Bool State₁ (Fin (ports₀ + ports₁)) input) =
      consumerConfig cfg (machine.initialConfig cfg.tapes.output) := by
  apply Config.ext
  · refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
    | left i =>
      simp only [MultiTapeTM.PrepareInput.after_workTapes_castAdd,
        MultiTapeTM.PrepareInput.after_workTapePos_castAdd]
      induction i using Fin.addCases with
      | left i =>
        have hi := MultiTapeTM.partialInv_embed (Fin.castAddEmb k₀) i
        simp only [Fin.castAddEmb_apply] at hi
        simp [consumerConfig, InputFromTape.config, MultiTapeTM.inCfg,
          ExtendTapes.config, MultiTapeTM.embed, ExtendChannels.config, reserve,
          initialConfig, Cfg.init, hi, partialInv_natAdd_castAdd]
      | right i =>
        simp [consumerConfig, InputFromTape.config, MultiTapeTM.inCfg,
          ExtendTapes.config, MultiTapeTM.embed, ExtendChannels.config, reserve,
          partialInv_castAdd_natAdd]
    | right i =>
      fin_cases i <;> simp [consumerConfig, InputFromTape.config, MultiTapeTM.inCfg,
        ExtendTapes.config, MultiTapeTM.embed, ExtendChannels.config, reserve,
        initialConfig, Cfg.init, MultiTapeTM.PrepareInput.flag]
  · funext port
    induction port using Fin.addCases with
    | left port =>
      simp [consumerConfig, InputFromTape.config, ExtendTapes.config, ExtendChannels.config,
        partialInv_natAdd_castAdd]
    | right port =>
      have hi := MultiTapeTM.partialInv_embed (Fin.natAddEmb ports₀) port
      simp only [Fin.natAddEmb_apply] at hi
      simp [consumerConfig, InputFromTape.config, ExtendTapes.config, ExtendChannels.config,
        reserve, partialInv_castAdd_natAdd, initialConfig, hi]

def prepareInitial (k₁ ports₁ : ℕ) (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    Config (k₁ + k₀ + 2) Bool MultiTapeTM.PrepareInput.Control (Fin (ports₀ + ports₁)) input where
  tapes := (MultiTapeTM.PrepareInput.before (reserve k₁ ports₁ cfg).tapes).withState
    (some (MultiTapeTM.prepareInput (k₁ + k₀)).q₀)
  channels := (reserve k₁ ports₁ cfg).channels

def prepareFinal (k₁ ports₁ : ℕ) (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    Config (k₁ + k₀ + 2) Bool MultiTapeTM.PrepareInput.Control (Fin (ports₀ + ports₁)) input where
  tapes := MultiTapeTM.PrepareInput.after (reserve k₁ ports₁ cfg).tapes none
  channels := (reserve k₁ ports₁ cfg).channels

theorem run_preparation (k₁ ports₁ : ℕ) (cfg : Config k₀ Bool State₀ (Fin ports₀) input)
    (time : ℕ) (htime : cfg.tapes.output.length + 4 ≤ time) :
    (MultiTapeTM.prepareInput (k₁ + k₀)).runFrom (prepareInitial k₁ ports₁ cfg).tapes time =
      (prepareFinal k₁ ports₁ cfg).tapes := by
  have h := MultiTapeTM.runFrom_prepareInput (reserve k₁ ports₁ cfg).tapes
  change (MultiTapeTM.prepareInput (k₁ + k₀)).runFrom (prepareInitial k₁ ports₁ cfg).tapes
    (cfg.tapes.output.length + 4) = (prepareFinal k₁ ports₁ cfg).tapes at h
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ htime (by rw [h]; rfl), h]

theorem prepare_start (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) :
    Sequential.start (consumer machine k₀ ports₀) (prepareFinal k₁ ports₁ cfg) =
      consumerConfig cfg (machine.initialConfig cfg.tapes.output) := prepared machine cfg

/-- The continuation inherits its pathwise halting bound on its private work tapes and ports. -/
theorem consumer_halts (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) (fuel : ℕ)
    (hhalt : machine.HaltsWithin fuel (machine.initialConfig cfg.tapes.output)) :
    (consumer machine k₀ ports₀).HaltsWithin fuel
      (consumerConfig cfg (machine.initialConfig cfg.tapes.output)) := by
  intro final hfinal
  rw [runConfigFrom_consumer] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  exact hhalt original ((canReturn_liftM_rename _ _ _).mp horiginal)

theorem prepare_canReturn (k₁ ports₁ : ℕ)
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) (time : ℕ)
    (htime : cfg.tapes.output.length + 4 ≤ time)
    (final : Config (k₁ + k₀ + 2) Bool MultiTapeTM.PrepareInput.Control
      (Fin (ports₀ + ports₁)) input)
    (hfinal : MonadAttach.CanReturn
      ((ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀))).runConfigFrom time
        (prepareInitial k₁ ports₁ cfg)) final) : final = prepareFinal k₁ ports₁ cfg := by
  rw [canReturn_ofDeterministic _ _ _ _ hfinal, run_preparation _ _ cfg time htime]
  rfl

/-- Preparation and the continuation halt within the sum of their transition budgets. -/
theorem continuation_halts (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime (machine.initialConfig cfg.tapes.output)) :
    (continuation machine k₀ ports₀).HaltsWithin (prepareTime + runTime)
      (Sequential.start (continuation machine k₀ ports₀) (buffer k₁ ports₁ cfg)) := by
  change ((ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀))).seq
    (consumer machine k₀ ports₀)).HaltsWithin (prepareTime + runTime)
      (Sequential.left (consumer machine k₀ ports₀) (prepareInitial k₁ ports₁ cfg))
  apply HaltsWithin.seq
  · intro final hfinal
    rw [prepare_canReturn _ _ cfg prepareTime hprepare final hfinal]
    rfl
  · intro final hfinal
    rw [prepare_canReturn _ _ cfg prepareTime hprepare final hfinal, prepare_start]
    exact consumer_halts machine cfg runTime hrun

end Composition

/-- Feed a machine's buffered output to another, using disjoint work tapes and oracle ports. -/
def comp {k₀ k₁ ports₀ ports₁ : ℕ} {State₀ State₁ : Type}
    (first : MultiTapePTM k₀ Bool State₀ (Fin ports₀))
    (second : MultiTapePTM k₁ Bool State₁ (Fin ports₁)) :
    MultiTapePTM (k₁ + k₀ + 2) Bool (State₀ ⊕ (MultiTapeTM.PrepareInput.Control ⊕ State₁))
      (Fin (ports₀ + ports₁)) :=
  (Composition.source first k₁ ports₁).seq (Composition.continuation second k₀ ports₀)

variable {k₀ k₁ ports₀ ports₁ : ℕ} {State₀ State₁ : Type}

theorem composition_output_bound (first : MultiTapePTM k₀ Bool State₀ (Fin ports₀))
    (input : List Bool) (fuel : ℕ) (final : Config k₀ Bool State₀ (Fin ports₀) input)
    (hfinal : MonadAttach.CanReturn (first.runConfigFrom fuel (first.initialConfig input)) final) :
    final.tapes.output.length ≤ fuel := by
  simpa [initialConfig, Cfg.init] using
    length_output_runConfigFrom_le first fuel (first.initialConfig input) final hfinal

/-- The buffered source is followed by the charged handoff, retaining all effects. -/
theorem runConfigFrom_comp (first : MultiTapePTM k₀ Bool State₀ (Fin ports₀))
    (second : MultiTapePTM k₁ Bool State₁ (Fin ports₁)) (input : List Bool)
    (firstTime secondTime : ℕ)
    (hfirst : first.HaltsWithin firstTime (first.initialConfig input))
    (hsecond : ∀ final,
      MonadAttach.CanReturn (first.runConfigFrom firstTime (first.initialConfig input)) final →
      second.HaltsWithin secondTime (second.initialConfig final.tapes.output)) :
    (first.comp second).runConfigFrom (firstTime + (firstTime + 4 + secondTime))
        ((first.comp second).initialConfig input) = (do
      let final ← (first.runConfigFrom firstTime (first.initialConfig input)).liftM
        (rename (Fin.castAddEmb ports₁))
      Sequential.right <$>
        (Composition.continuation second k₀ ports₀).runConfigFrom (firstTime + 4 + secondTime)
          (Sequential.start (Composition.continuation second k₀ ports₀)
            (Composition.buffer k₁ ports₁ final))) := by
  change ((Composition.source first k₁ ports₁).seq
    (Composition.continuation second k₀ ports₀)).runConfigFrom _
      (Sequential.left (Composition.continuation second k₀ ports₀)
        ((Composition.source first k₁ ports₁).initialConfig input)) = _
  rw [runConfigFrom_seq _ _ firstTime (firstTime + 4 + secondTime) _
    (by
      intro final hfinal
      rw [Composition.runConfigFrom_source] at hfinal
      obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
      exact hfirst original ((canReturn_liftM_rename _ _ _).mp horiginal))
    (by
      intro final hfinal
      rw [Composition.runConfigFrom_source] at hfinal
      obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
      have hsource := (canReturn_liftM_rename _ _ _).mp horiginal
      exact Composition.continuation_halts second original (firstTime + 4) secondTime
        (Nat.add_le_add_right (composition_output_bound first input firstTime original hsource) 4)
        (hsecond original hsource)), Composition.runConfigFrom_source, bind_map_left]

/-- The compiled composition halts on every response path within the combined transition bound. -/
theorem HaltsWithin.comp {first : MultiTapePTM k₀ Bool State₀ (Fin ports₀)}
    {second : MultiTapePTM k₁ Bool State₁ (Fin ports₁)} {input : List Bool}
    {firstTime secondTime : ℕ} (hfirst : first.HaltsWithin firstTime (first.initialConfig input))
    (hsecond : ∀ final,
      MonadAttach.CanReturn (first.runConfigFrom firstTime (first.initialConfig input)) final →
      second.HaltsWithin secondTime (second.initialConfig final.tapes.output)) :
    (first.comp second).HaltsWithin (firstTime + (firstTime + 4 + secondTime))
      ((first.comp second).initialConfig input) := by
  intro final hfinal
  rw [runConfigFrom_comp first second input firstTime secondTime hfirst hsecond] at hfinal
  obtain ⟨mid, hmid, hfinal⟩ := (FreeM.canReturn_bind _ _ _).mp hfinal
  obtain ⟨last, hlast, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  have hsource := (canReturn_liftM_rename _ _ _).mp hmid
  have hhalt := Composition.continuation_halts second mid (firstTime + 4) secondTime
    (Nat.add_le_add_right (composition_output_bound first input firstTime mid hsource) 4)
    (hsecond mid hsource)
  simp [hhalt last hlast]

end Turing.MultiTapePTM
