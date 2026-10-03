/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Aesop

/-! # Rule sets for deterministic and probabilistic polynomial-time programs -/

public section

declare_aesop_rule_sets [PolyTime, PPT]

open Lean Meta Elab Tactic in
/-- Apply a certificate by the program's syntactic head before unification. The last argument
of the supplied efficiency predicate is the program. This prevents similarly implemented
algorithms from unfolding into each other's rules during proof search. -/
meta def Cslib.Tactic.applyProgramHead (predicate : Name) (rules : Array (Name × Name)) :
    TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
  let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
  let rule ← lambdaTelescope program fun _ body => do
    let some (_, rule) := rules.find? (fun (head, _) => body.isAppOf head)
      | throwError "no certificate registered for this program head"
    pure rule
  liftMetaTactic fun goal => goal.applyConst rule
