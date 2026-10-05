/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Rename
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# Separate communication ports for subroutines

Embedding ports reserves independent communication buffers without splitting the oracle's hidden
state. The semantic renaming may bind several ports to one shared operation. This lets sequential
subroutines start with blank buffers while retaining the state left by earlier oracle calls.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k ports ports' : ℕ} {State : Type} {input : List Bool}

/-- Reindex communication buffers, leaving all unused ports untouched. -/
@[simps! initial] def extendChannels (machine : MultiTapePTM k Bool State (Fin ports))
    (e : Fin ports ↪ Fin ports') : MultiTapePTM k Bool State (Fin ports') where
  initial := machine.initial
  tr state symbol work answer bit :=
    match machine.tr state symbol work (fun port => answer (e port)) bit with
    | .step action symbol move => .step action
      (fun port => (MultiTapeTM.partialInv e port).bind symbol)
      (fun port => ((MultiTapeTM.partialInv e port).map move).getD 0)
    | .query port next => .query (e port) next

namespace ExtendChannels

/-- The unused ports retain the supplied buffers and answer heads. -/
def config (cfg : Config k Bool State (Fin ports) input) (e : Fin ports ↪ Fin ports')
    (extra : Fin ports' → Channel Bool) : Config k Bool State (Fin ports') input where
  tapes := cfg.tapes
  channels port := match MultiTapeTM.partialInv e port with
    | some source => cfg.channels source
    | none => extra port

@[simp] theorem config_state (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) :
    (config cfg e extra).tapes.state = cfg.tapes.state := rfl

@[simp] theorem config_inputSymbol (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) :
    (config cfg e extra).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) :
    (config cfg e extra).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem config_channels (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) (port : Fin ports) :
    (config cfg e extra).channels (e port) = cfg.channels port := by simp [config]

@[simp] theorem config_answerSymbols (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) (port : Fin ports) :
    (config cfg e extra).answerSymbols (e port) = cfg.answerSymbols port := by
  simp [Config.answerSymbols]

theorem step_config (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool)
    (action : Turing.Action k Bool State) (symbol : Fin ports → Option Bool)
    (move : Fin ports → SignType) :
    (config cfg e extra).step action
        (fun port => (MultiTapeTM.partialInv e port).bind symbol)
        (fun port => ((MultiTapeTM.partialInv e port).map move).getD 0) =
      config (cfg.step action symbol move) e extra := by
  refine Config.ext rfl ?_
  funext port
  cases hp : MultiTapeTM.partialInv e port <;> simp [Config.step, config, hp]

theorem receive_config (cfg : Config k Bool State (Fin ports) input)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool)
    (port : Fin ports) (next : State) (answer : List Bool) :
    (config cfg e extra).receive (e port) next answer =
      config (cfg.receive port next answer) e extra := by
  refine Config.ext rfl ?_
  funext target
  by_cases ht : target ∈ Set.range e
  · obtain ⟨source, rfl⟩ := ht
    simp [Config.receive, config, Function.update_apply, e.injective.eq_iff]
  · have hne : e port ≠ target := fun h => ht ⟨port, h⟩
    simp [Config.receive, config, Function.update_apply, MultiTapeTM.partialInv_eq_none e ht,
      Ne.symm hne]

end ExtendChannels

/-- One step uses only the selected buffers and renames precisely the submitted request. -/
theorem step_extendChannels (machine : MultiTapePTM k Bool State (Fin ports))
    (e : Fin ports ↪ Fin ports') (cfg : Config k Bool State (Fin ports) input)
    (extra : Fin ports' → Channel Bool) :
    (machine.extendChannels e).step (ExtendChannels.config cfg e extra) =
      (fun final => ExtendChannels.config final e extra) <$>
        (machine.step cfg).liftM (rename e) := by
  cases hs : cfg.tapes.state with
  | none => simp [step, hs]
  | some state =>
    simp only [step, ExtendChannels.config_state, hs, ExtendChannels.config_inputSymbol,
      ExtendChannels.config_workTapeSymbols, ExtendChannels.config_answerSymbols,
      extendChannels, FreeM.liftM_bind, liftM_rename_coin, map_bind]
    apply bind_congr
    intro bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
      <;> simp [ExtendChannels.step_config, ExtendChannels.receive_config]

/-- Port reservation preserves responses and continuations, changing only the request name. -/
theorem runConfigFrom_extendChannels (machine : MultiTapePTM k Bool State (Fin ports))
    (e : Fin ports ↪ Fin ports') (cfg : Config k Bool State (Fin ports) input)
    (extra : Fin ports' → Channel Bool) (fuel : ℕ) :
    (machine.extendChannels e).runConfigFrom fuel (ExtendChannels.config cfg e extra) =
      (fun final => ExtendChannels.config final e extra) <$>
        (machine.runConfigFrom fuel cfg).liftM (rename e) := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    simp only [runConfigFrom_succ, step_extendChannels, FreeM.liftM_bind, bind_map_left, map_bind]
    exact bind_congr ih

/-- Reserving ports starts all original and additional buffers empty. -/
theorem initialConfig_extendChannels (machine : MultiTapePTM k Bool State (Fin ports))
    (e : Fin ports ↪ Fin ports') (input : List Bool) :
    (machine.extendChannels e).initialConfig input =
      ExtendChannels.config (machine.initialConfig input) e (fun _ => {}) := by
  refine Config.ext rfl ?_
  funext port
  cases hp : MultiTapeTM.partialInv e port <;> simp [initialConfig, ExtendChannels.config, hp]

/-- Output and timeout are unchanged by the port embedding. -/
theorem runFrom_extendChannels (machine : MultiTapePTM k Bool State (Fin ports))
    (e : Fin ports ↪ Fin ports') (cfg : Config k Bool State (Fin ports) input)
    (extra : Fin ports' → Channel Bool) (fuel : ℕ) :
    (machine.extendChannels e).runFrom fuel (ExtendChannels.config cfg e extra) =
      (machine.runFrom fuel cfg).liftM (rename e) := by
  simp only [runFrom, runConfigFrom_extendChannels, FreeM.liftM_map, ← comp_map]
  rfl

/-- Every source response path corresponds to a path using the renamed ports. -/
theorem HaltsWithin.extendChannels {machine : MultiTapePTM k Bool State (Fin ports)} {fuel : ℕ}
    {cfg : Config k Bool State (Fin ports) input} (h : machine.HaltsWithin fuel cfg)
    (e : Fin ports ↪ Fin ports') (extra : Fin ports' → Channel Bool) :
    (machine.extendChannels e).HaltsWithin fuel (ExtendChannels.config cfg e extra) := by
  intro final hfinal
  rw [runConfigFrom_extendChannels] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := (FreeM.canReturn_map _ _ _).mp hfinal
  exact h original ((canReturn_liftM_rename e _ _).mp horiginal)

end Turing.MultiTapePTM
