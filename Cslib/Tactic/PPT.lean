/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Tactic.PolyTime
public import Cslib.Computability.PolynomialTime.Sampling

/-!
# Synthesizing machine certificates for native probabilistic programs

`ppt` composes the uniform machine certificates for ordinary `PFunctor.FreeM` programs.
It combines sampling, monadic sequencing, and deterministic `polytime` rules. A continuation
may retain the original input; the certificate charges for that copying. Unknown subprograms
require local certificates. Every resulting proof preserves the joint output and shared oracle
state through the native measure semantics.

This adapts Samuel Schlesinger's `ppt` tactic to `MultiTapePTM.IsPPT`, without a separate
probabilistic-program representation.
-/

public section

namespace Cslib.Tactic.PPT

open Turing.MultiTapeTM Turing.MultiTapePTM

open Lean Meta Elab Tactic in
/-- Dispatch a native program's certificate before unification unfolds its implementation. -/
meta def applyHead (rules : Array (Name × Name)) : TacticM Unit :=
  Cslib.Tactic.applyProgramHead ``IsPPT rules

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptPrimitive : Lean.Elab.Tactic.TacticM Unit :=
  applyHead #[(``Pure.pure, ``IsPolyTime.isPPT),
    (``List.mapM, ``isPPT_sampleBits_of_isPolyTime)]

open Lean Meta Elab Tactic PolyTime in
@[aesop unsafe 50% tactic (rule_sets := [PPT])]
private meta def pptCall : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``IsPPT do throwError "expected a probabilistic polynomial-time goal"
  let domain := (← whnf (← inferType target.getAppArgs.back!)).bindingDomain!
  for decl in ← getLCtx do
    if decl.isImplementationDetail || !decl.type.isAppOf ``IsPPT then continue
    let saved ← saveState
    try
      let source := (← whnf (← inferType decl.type.getAppArgs.back!)).bindingDomain!
      let argument ← prepareArgument domain source
      applyWithArguments ``IsPPT.comp #[(`f, argument), (`hprogram, decl.toExpr)]
      if ← (← getGoals).anyM (fun goal => do isDefEq (← goal.getType) target) then
        throwError "composition made no progress"
      return
    catch _ => saved.restore
  throwError "no applicable local program certificate"

-- Resolve the first program's result encoding before certifying its captured continuation.
open Lean Meta Elab Tactic in
@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPPT do throwError "expected a probabilistic polynomial-time goal"
  let isBind ← lambdaTelescope target.getAppArgs.back! fun _ body => do
    if body.isAppOf ``Bind.bind then return true
    if body.isAppOf ``Functor.map then return false
    throwError "expected probabilistic sequencing"
  if isBind then
    liftMetaTactic fun goal => goal.applyConst ``IsPPT.bind_with
    evalTactic (← `(tactic| case hfirst => solve | aesop (rule_sets := [PPT, PolyTime])))
  else
    liftMetaTactic fun goal => goal.applyConst ``IsPPT.map_with
    evalTactic (← `(tactic| case hprogram => solve | aesop (rule_sets := [PPT, PolyTime])))

/-- Prove a native program uniformly polynomial time using certified sampling and composition. -/
macro "ppt" : tactic => `(tactic| solve | aesop (rule_sets := [PPT, PolyTime]))

end Cslib.Tactic.PPT
