/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Unbounded machine execution

Every live transition exposes a private coin, even when the table ignores its value. This
visible operation records progress through local machine work. A query transition additionally
exposes the submitted oracle request. Thus transition fuel counts private-coin operations,
whereas ordinary resumption truncation counts both coins and oracle requests.

When every path halts within a transition bound, the unbounded execution is exactly the
resumption embedding of the corresponding bounded configuration program.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine PFunctor

variable {k : ℕ} {State Oracle : Type} [DecidableEq Oracle] {input : List Bool}

/-- A machine configuration or a query awaiting its answer after the transition's coin. -/
abbrev ExecutionState (k : ℕ) (State Oracle : Type) (input : List Bool) :=
  Config k Bool State Oracle input ⊕ (Config k Bool State Oracle input × Oracle × State)

/-- The return-or-effect coalgebra for unbounded execution. -/
def executionStep (machine : MultiTapePTM k Bool State Oracle) :
    ExecutionState k State Oracle input → Config k Bool State Oracle input ⊕
      (effects Oracle).Obj (ExecutionState k State Oracle input)
  | .inl cfg => match cfg.tapes.state with
    | none => .inl cfg
    | some state => .inr ⟨.inl (), fun bit =>
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | .step action symbol move => .inl (cfg.step action symbol move)
      | .query oracle next => .inr (cfg, oracle, next)⟩
  | .inr (cfg, oracle, next) =>
    .inr ⟨.inr (oracle, (cfg.channels oracle).queryBuffer),
      fun answer => .inl (cfg.receive oracle next answer)⟩

/-- Execute without a fuel bound. Infinite paths remain observable through machine coins. -/
def runUnbounded (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) :
    Resumption (effects Oracle) (Config k Bool State Oracle input) :=
  Resumption.corec (executionStep machine) (.inl cfg)

private theorem corec_query (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) (oracle : Oracle) (next : State) :
    Resumption.corec (executionStep machine) (.inr (cfg, oracle, next)) =
      Resumption.query (p := effects Oracle) (.inr (oracle, (cfg.channels oracle).queryBuffer))
        (fun answer => machine.runUnbounded (cfg.receive oracle next answer)) := by
  apply Resumption.dest_injective
  rw [Resumption.dest_corec, Resumption.dest_query]
  rfl

/-- A halted machine returns immediately, without consuming an extra coin. -/
theorem runUnbounded_halted (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) (h : cfg.tapes.state = none) :
    machine.runUnbounded cfg = Resumption.pure cfg := by
  apply Resumption.dest_injective
  simp [runUnbounded, Resumption.dest_corec, executionStep, h]

/-- One live machine transition, including a possible named request. -/
theorem runUnbounded_live (machine : MultiTapePTM k Bool State Oracle)
    (cfg : Config k Bool State Oracle input) (state : State) (h : cfg.tapes.state = some state) :
    machine.runUnbounded cfg = Resumption.query (p := effects Oracle) (.inl ()) (fun bit =>
      match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | .step action symbol move => machine.runUnbounded (cfg.step action symbol move)
      | .query oracle next =>
        Resumption.query (p := effects Oracle) (.inr (oracle, (cfg.channels oracle).queryBuffer))
          (fun answer => machine.runUnbounded (cfg.receive oracle next answer))) := by
  apply Resumption.dest_injective
  simp only [runUnbounded, Resumption.dest_corec, executionStep, h, Sum.map_inr,
    Resumption.dest_query, PFunctor.map]
  congr 2
  funext bit
  dsimp only [PFunctor.Obj.snd, Function.comp_apply]
  cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit with
  | step action symbol move => rfl
  | query oracle next => exact corec_query machine cfg oracle next

/-- A pathwise clock connects bounded and unbounded execution as an equality of programs. -/
theorem HaltsWithin.runUnbounded_eq {machine : MultiTapePTM k Bool State Oracle} {fuel : ℕ}
    {cfg : Config k Bool State Oracle input} (h : machine.HaltsWithin fuel cfg) :
    machine.runUnbounded cfg = (machine.runConfigFrom fuel cfg).toResumption := by
  induction fuel generalizing cfg with
  | zero => exact runUnbounded_halted machine cfg (h cfg rfl)
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runUnbounded_halted machine cfg hs, runConfigFrom_halted machine _ cfg hs]
    | some state =>
      rw [runUnbounded_live machine cfg state hs]
      simp only [runConfigFrom, step, hs, bind_assoc]
      change Resumption.query _ _ = Resumption.query _ _
      congr 1
      funext bit
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
      | step action symbol move =>
        simp only [FreeM.pure_bind, ha, pure_bind]
        apply ih
        intro final hfinal
        apply h final
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨cfg.step action symbol move, ?_, hfinal⟩
        simp only [step, hs]
        exact (FreeM.canReturn_bind _ _ _).mpr ⟨bit, by simp [coin], by simp [ha]⟩
      | query oracle next =>
        simp only [FreeM.pure_bind, ha, bind_assoc]
        change Resumption.query _ _ = Resumption.query _ _
        congr 1
        funext answer
        apply ih
        intro final hfinal
        apply h final
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨cfg.receive oracle next answer, ?_, hfinal⟩
        simp only [step, hs]
        apply (FreeM.canReturn_bind _ _ _).mpr
        refine ⟨bit, by simp [coin], ?_⟩
        rw [ha]
        exact (FreeM.canReturn_bind _ _ _).mpr ⟨answer, by simp [query], rfl⟩

end Turing.MultiTapePTM
