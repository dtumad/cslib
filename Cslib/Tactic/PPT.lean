/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Tactic.PolyTime
public import Cslib.Computability.Probabilistic.Composition
public import Cslib.Computability.Probabilistic.Sampling
public import Cslib.Computability.Probabilistic.OracleEncoding

/-!
# Synthesizing certificates for probabilistic polynomial-time programs

`ppt` combines proved PPT sequencing and sampling rules with deterministic `polytime` rules.
It handles supported `do` programs without exposing a machine witness. A call to an unknown
algorithm still needs a local certificate. Typed continuations retain captured inputs using
their encodings. Sampling lengths may depend on
runtime data. For stateful oracle programs, the tactic supports certified machine runs and
Boolean postprocessing of certified subprograms. General oracle sequencing is not yet automated.
-/

public section

open Lean Meta Elab Tactic Cslib.Probability in
/-- Apply the certificate associated with a program's syntactic head before unification.
This keeps similarly implemented samplers and tests from unfolding into each other's rules. -/
meta def Cslib.Tactic.PPT.applyHead (rules : Array (Name × Name)) : TacticM Unit :=
  Cslib.Tactic.applyProgramHead ``IsPPTOn rules

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PPT])]
  Cslib.Probability.isPPT_sampleBits
  Cslib.Probability.IsPolyTime.isPPT_word
  Cslib.Probability.IsPolyTime.isPPT
  Cslib.Probability.IsOraclePPTOn.map_bool
  Cslib.Probability.OracleEncoding.IsPPTOn.map_bool

-- Matching a primitive by unification can evaluate a whole random program while its output
-- encoding is still unknown. Inspect the program head before applying primitive rules.
@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptPrimitive : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[
    (``Pure.pure, ``Cslib.Probability.IsPolyTime.isPPTOn),
    (``Cslib.OracleComp.sampleBits, ``Cslib.Probability.IsPolyTime.sampleBits),
    (``Cslib.OracleComp.sample, ``Cslib.Probability.IsPolyTime.uniformBits),
    (``Cslib.OracleComp.uniform, ``Cslib.Probability.isPPTOn_uniformBool)]

attribute [aesop safe apply (rule_sets := [PPT])]
  Cslib.Probability.IsPPT.map_word
  Cslib.Probability.IsPPT.map_bool
  Cslib.Probability.IsPPTOn.isPPT
  Cslib.Probability.IsOraclePPTOn.of_machine

attribute [aesop unsafe 50% apply (rule_sets := [PPT])]
  Cslib.Probability.IsPPT.bind
  Cslib.Probability.IsPPT.bind_parameter
  Cslib.Probability.IsPPT.preprocess_word
  Cslib.Probability.IsPPT.on
  Cslib.Probability.IsPPTOn.bind_with
  Cslib.Probability.IsPPTOn.map_with
  Cslib.Probability.IsPPTOn.bind
  Cslib.Probability.IsPPTOn.map
  Cslib.Probability.IsPPTOn.preprocess

open Lean Meta Elab Tactic Cslib.Probability Cslib.Tactic.PolyTime in
@[aesop unsafe 50% tactic (rule_sets := [PPT])]
private meta def pptCall : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for tuple in [true, false] do
      let saved ← saveState
      try
        if decl.type.isAppOf ``IsPPT then
          applyWithArguments ``IsPPT.preprocess #[(`hprogram, decl.toExpr)]
        else if decl.type.isAppOf ``IsPPTOn then
          if tuple then
            let argument ← prepareArgument target.getAppArgs[0]! decl.type.getAppArgs[0]!
            applyWithArguments ``IsPPTOn.preprocess
              #[(`prepare, argument), (`hprogram, decl.toExpr)]
          else
            applyWithArguments ``IsPPTOn.preprocess_pair #[(`hprogram, decl.toExpr)]
        else throwError "expected a probabilistic certificate"
        if ← (← getGoals).anyM (fun goal => do isDefEq (← goal.getType) target) then
          throwError "composition made no progress"
        return
      catch _ => saved.restore
  throwError "no applicable local program certificate"

open Lean Meta Elab Tactic Cslib.Probability in
@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptIte : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
  let isIte ← lambdaTelescope target.getAppArgs.back! fun _ body => pure (body.isAppOf ``ite)
  unless isIte do throwError "expected a conditional"
  evalTactic (← `(tactic| first | apply IsPPTOn.cond | apply IsPPTOn.ite))

open Lean Meta Elab Tactic Cslib.Probability in
@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
  let isBind ← lambdaTelescope target.getAppArgs.back! fun _ body => do
    if body.isAppOf ``Bind.bind then return true
    if body.isAppOf ``Functor.map then return false
    throwError "expected probabilistic sequencing"
  if isBind then
    liftMetaTactic fun goal => goal.applyConst ``IsPPTOn.bind_with
    evalTactic (← `(tactic| case hfirst => solve | aesop (rule_sets := [PPT, PolyTime])))
  else
    liftMetaTactic fun goal => goal.applyConst ``IsPPTOn.map_with
    evalTactic (← `(tactic| case hprogram => solve | aesop (rule_sets := [PPT, PolyTime])))

/-- Synthesize a PPT certificate using sampling, composition, and deterministic efficiency rules. -/
macro "ppt" : tactic => `(tactic| solve | aesop (rule_sets := [PPT, PolyTime]))
