/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.List
public import Cslib.Computability.PolynomialTime.Parameter
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

`polytime` composes proved efficiency rules for ordinary word programs: pairing, concatenation,
maps, `zipWith`, reversal, filtering, head/tail, unary length, and bounded iteration. Higher-order
folds reuse local step certificates and fixed-growth contracts; simple constructor growth is
inferred automatically. Boolean parameters may be computed at runtime.
Encoded collections support `map`, `flatMap`, filtering, and reversal, including callbacks that
capture runtime data and call supplied algorithms. Calls may assemble nested tuple arguments.
Unary arithmetic supports fixed powers, subtraction, comparison, and base-two logarithms;
word operations include runtime indexing, slicing, equality, and conditionals.

All rules construct proofs of the machine-based `IsPolyTime` predicate. An unknown operation
requires a certificate; arbitrary Lean computation is not assigned unit cost. Loops that grow
their state can use `IsPolyTime.iterate_spec` or `IsPolyTime.foldl_spec` with a size invariant.
-/

public section

namespace Cslib.Tactic.PolyTime

open Turing.MultiTapeTM

open Lean Elab Tactic in
/-- Apply a deterministic certificate by its program head, without unfolding unrelated programs. -/
meta def applyHead (rules : Array (Name × Name)) : TacticM Unit :=
  Cslib.Tactic.applyProgramHead ``IsPolyTime rules

open Lean Meta Elab Tactic in
/-- Dispatch a unary arithmetic certificate by the encoded natural-number expression.
Recognize both the named embedding and its simplified list representation. -/
meta def applyUnaryHead (rules : Array (Name × Name)) : TacticM Unit :=
  Cslib.Tactic.applyProgramHead ``IsPolyTime rules fun body => do
    if body.isAppOf ``DFunLike.coe && body.getAppArgs[4]!.isAppOf ``unaryEncoding then
      return body.getAppArgs.back!
    if body.isAppOf ``List.replicate && body.getAppArgs.back!.isAppOf ``Bool.true then
      return body.getAppArgs[1]!
    throwError "expected a unary natural-number result"

open Lean Meta Elab Tactic in
@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeEncoded : TacticM Unit :=
  Cslib.Tactic.applyProgramHead ``IsPolyTime #[
    (``List.cons, ``IsPolyTime.list_cons),
    (``Option.some, ``IsPolyTime.option_some),
    (``Option.getD, ``IsPolyTime.option_getD),
    (``Sigma.mk, ``IsPolyTime.sigma),
    (``List.lookup, ``IsPolyTime.list_lookup)] fun body => do
      unless body.isAppOf ``DFunLike.coe do throwError "expected an encoded result"
      return body.getAppArgs.back!

open Lean Meta Elab Tactic in
/-- Apply a rule with selected named arguments, keeping proof obligations in the metavariable
context so that subsequent tactics must discharge them. -/
meta def applyWithArguments (rule : Name)
    (arguments : Array (Name × Expr)) : TacticM Unit := do
  let mut proof ← mkConstWithFreshMVarLevels rule
  let mut type ← inferType proof
  while let .forallE name domain body _ := type do
    let arg ← match arguments.find? (fun argument => argument.1 == name) with
      | some (_, value) => pure value
      | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType arg) domain do throwError "argument type mismatch"
    proof := mkApp proof arg
    type := body.instantiate1 arg
    if name == arguments.back!.1 then
      replaceMainGoal (← (← getMainGoal).apply proof)
      return
  throwError "argument not found"

/-- Fix the accumulator encoding and expose the Boolean growth cases before proof search. -/
theorem foldl_rule {α : Type} {encode : α → Word}
    {input initial : α → Word} {step : Word → Bool → Word} {growth : ℕ}
    (hinput : IsPolyTime encode input) (hinitial : IsPolyTime encode initial)
    (hstep : IsPolyTime (pairEncoding wordEncoding boolEncoding)
      (fun pair => step pair.1 pair.2))
    (hgrowth : ∀ word, (step word false).length ≤ word.length + growth ∧
      (step word true).length ≤ word.length + growth) :
    IsPolyTime encode (fun a => (input a).foldl step (initial a)) :=
  hinput.foldl_of_bounded_growth (stateEncoding := wordEncoding) (step := step) hinitial hstep
    (by simpa [wordEncoding] using hgrowth)

/-- Recognize the form of `headD` produced by simplification. -/
theorem headD_rule {α : Type} {encode : α → Word}
    {f : α → Word} (hf : IsPolyTime encode f) (fallback : Bool) :
    IsPolyTime encode (fun a => [(f a).head?.getD fallback]) := by
  simpa using hf.headD fallback

/-- Treat a string of false bits as a change of symbols in an efficient unary counter. -/
theorem replicate_false_rule {α : Type} {encode : α → Word} {count : α → ℕ}
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true)) :
    IsPolyTime encode (fun a => List.replicate (count a) false) := hcount.replicate false

/-- Fix the Boolean operation before solving its argument certificate. -/
theorem bool₁_rule {α : Type} {encode : α → Word} (op : Bool → Bool)
    {f : α → Bool} (hf : IsPolyTime encode (fun a => [f a])) :
    IsPolyTime encode (fun a => [op (f a)]) := hf.bool₁ op

/-- Fix the Boolean operation before solving its two argument certificates. -/
theorem bool₂_rule {α : Type} {encode : α → Word} (op : Bool → Bool → Bool)
    {f g : α → Bool} (hf : IsPolyTime encode (fun a => [f a]))
    (hg : IsPolyTime encode (fun a => [g a])) :
    IsPolyTime encode (fun a => [op (f a) (g a)]) := hf.bool₂ hg op

-- Recognize tuple construction and bitwise combinations before generic rules unfold encodings.
-- Callbacks with several captured inputs can have deeply nested tuple encodings.
open Lean Meta Elab Tactic in
@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstruct : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let rule ← lambdaTelescope target.getAppArgs.back! fun _ body => do
    if body.isAppOf ``DFunLike.coe && body.getAppArgs[4]!.isAppOf ``pairEncoding &&
        body.getAppArgs.back!.isAppOf ``Prod.mk then
      return ``IsPolyTime.pair
    if body.isAppOf ``DFunLike.coe && body.getAppArgs[4]!.isAppOf ``parameterEncoding &&
        body.getAppArgs.back!.isAppOf ``Prod.mk then
      return ``IsPolyTime.parameterInput
    if body.isAppOf ``HAppend.hAppend || body.isAppOf ``List.append then
      return ``IsPolyTime.append
    if body.isAppOf ``List.zipWith then return ``IsPolyTime.zipWith
    if body.isAppOf ``List.cons && body.getAppArgs[1]!.isAppOf ``List.foldl &&
        body.getAppArgs.back!.isAppOf ``List.nil then return ``IsPolyTime.foldl_bool
    throwError "expected tuple construction or a bitwise combination"
  if rule == ``IsPolyTime.pair then
    -- The field types and encodings may depend on the input. Assemble their encoded words.
    evalTactic (← `(tactic| apply IsPolyTime.pair (left := wordEncoding) (right := wordEncoding)))
  else
    liftMetaTactic fun goal => goal.applyConst rule

open Lean Meta Elab Tactic in
@[aesop safe -5 tactic (rule_sets := [PolyTime])]
private meta def polytimeBool : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let (rule, op) ← lambdaTelescope target.getAppArgs.back! fun inputs body => do
    unless body.isAppOf ``List.cons && body.getAppArgs.back!.isAppOf ``List.nil do
      throwError "expected a Boolean result"
    let bit := body.getAppArgs[1]!.consumeMData
    let args := bit.getAppArgs
    let bool := mkConst ``Bool
    for (arity, rule) in [(1, ``bool₁_rule), (2, ``bool₂_rule)] do
      if args.size < arity then continue
      let op := mkAppN bit.getAppFn (args.extract 0 (args.size - arity))
      if op.hasExprMVar then continue
      if inputs.any (fun input => op.containsFVar input.fvarId!) then continue
      let opType ← if arity == 1 then mkArrow bool bool
        else mkArrow bool (← mkArrow bool bool)
      if ← isDefEq (← inferType op) opType then return (rule, op)
    throwError "expected a fixed unary or binary Boolean operation"
  applyWithArguments rule #[(`op, op)]

-- Rules invoked by name must be exported for clients using `module` and `public import`.
/-- Rule for running a certified function on the first input field. -/
theorem on_fst_rule {α β : Type} {left : α ↪ Word} {right : β ↪ Word}
    {f : α → Word} (hf : IsPolyTime left f) :
    IsPolyTime (pairEncoding left right) (fun pair => f pair.1) :=
  hf.comp_encoded (isPolyTime_fst left right)

/-- Rule for running a certified function on the second input field. -/
theorem on_snd_rule {α β : Type} {left : α ↪ Word} {right : β ↪ Word}
    {f : β → Word} (hf : IsPolyTime right f) :
    IsPolyTime (pairEncoding left right) (fun pair => f pair.2) :=
  hf.comp_encoded (isPolyTime_snd left right)

/-- A certified function of the security parameter may ignore the auxiliary input. -/
theorem on_security_rule {f : ℕ → Word} (hf : IsPolyTime unaryEncoding f) :
    IsPolyTime parameterEncoding (fun input => f input.1) :=
  hf.comp_encoded isPolyTime_security

/-- A certified function of the auxiliary input may ignore the security parameter. -/
theorem on_auxiliaryInput_rule {f : Word → Word} (hf : IsPolyTime wordEncoding f) :
    IsPolyTime parameterEncoding (fun input => f input.2) :=
  hf.comp_encoded isPolyTime_auxiliaryInput

-- Abstract the selected field explicitly: higher-order unification does not infer an arbitrary
-- chain of projections, and guessing a fresh pair would introduce an unknown encoding.
open Lean Meta Elab Tactic in
@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeProjection : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  for (index, projection, rule) in
      [(0, ``Prod.fst, ``on_security_rule), (1, ``Prod.snd, ``on_auxiliaryInput_rule),
        (0, ``Prod.fst, ``on_fst_rule), (1, ``Prod.snd, ``on_snd_rule)] do
    let saved ← saveState
    try
      let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
      let fn ← lambdaTelescope program fun args body => do
        unless args.size == 1 do throwError "expected one input"
        let input := args[0]!
        let field ← mkAppM projection #[input]
        withLocalDeclD `field (← inferType field) fun value => do
          let body := body.replace fun e =>
            if e == field || e == mkProj ``Prod index input then some value else none
          if body.containsFVar input.fvarId! then throwError "uses both fields"
          mkLambdaFVars #[value] body
      applyWithArguments rule #[(`f, fn)]
      return
    catch _ => saved.restore
  throwError "not a projection of the input"

/-- Capture the current input before certifying a mapped callback. -/
theorem list_map_with_rule {α Item Output : Type} {encode : α ↪ Word}
    {element : Item ↪ Word} {output : Output ↪ Word}
    {values : α → List Item} {f : α → Item → Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime (pairEncoding encode element) (fun pair => output (f pair.1 pair.2))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).map (f a))) :=
  hvalues.list_map_with (environment := encode) (env := id) (isPolyTime_input encode) hf

/-- Capture the current input before certifying a list-producing callback. -/
theorem list_flatMap_with_rule {α Item Output : Type} {encode : α ↪ Word}
    {element : Item ↪ Word} {output : Output ↪ Word}
    {values : α → List Item} {f : α → Item → List Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime (pairEncoding encode element)
      (fun pair => listEncoding output (f pair.1 pair.2))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).flatMap (f a))) :=
  hvalues.list_flatMap_with (environment := encode) (env := id) (isPolyTime_input encode) hf

/-- Capture the current input before certifying a collection predicate. -/
theorem list_filter_with_rule {α Item : Type} {encode : α ↪ Word}
    {element : Item ↪ Word} {values : α → List Item} {predicate : α → Item → Bool}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hpredicate : IsPolyTime (pairEncoding encode element)
      (fun pair => [predicate pair.1 pair.2])) :
    IsPolyTime encode (fun a => listEncoding element ((values a).filter (predicate a))) :=
  hvalues.list_filter_with (environment := encode) (env := id) (isPolyTime_input encode) hpredicate

/-- Collect a Boolean callback's answers into an ordinary word. -/
theorem list_map_bool_rule {α Item : Type} {encode : α ↪ Word}
    {element : Item ↪ Word} {values : α → List Item} {f : α → Item → Bool}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime (pairEncoding encode element) (fun pair => [f pair.1 pair.2])) :
    IsPolyTime encode (fun a => (values a).map (f a)) :=
  (hvalues.list_map_with (environment := encode) (env := id) (output := boolEncoding)
    (isPolyTime_input encode) hf).decode_list_bool

/-- Concatenate a word-producing callback's answers. -/
theorem list_flatMap_word_rule {α Item : Type} {encode : α ↪ Word}
    {element : Item ↪ Word} {values : α → List Item} {f : α → Item → Word}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime (pairEncoding encode element) (fun pair => f pair.1 pair.2)) :
    IsPolyTime encode (fun a => (values a).flatMap (f a)) :=
  (hvalues.list_flatMap_with (environment := encode) (env := id) (output := boolEncoding)
    (isPolyTime_input encode) hf.encode_list_bool).decode_list_bool

/-- Mapping over raw bits fixes the element encoding before certifying the captured callback. -/
theorem word_map_with_rule {α : Type} {encode : α ↪ Word}
    {values : α → Word} {f : α → Bool → Bool}
    (hvalues : IsPolyTime encode values)
    (hf : IsPolyTime (pairEncoding encode boolEncoding) (fun pair => [f pair.1 pair.2])) :
    IsPolyTime encode (fun a => (values a).map (f a)) :=
  list_map_bool_rule hvalues.encode_list_bool hf

/-- A captured callback may produce a word for each raw input bit. -/
theorem word_flatMap_with_rule {α : Type} {encode : α ↪ Word}
    {values : α → Word} {f : α → Bool → Word}
    (hvalues : IsPolyTime encode values)
    (hf : IsPolyTime (pairEncoding encode boolEncoding) (fun pair => f pair.1 pair.2)) :
    IsPolyTime encode (fun a => (values a).flatMap (f a)) :=
  list_flatMap_word_rule hvalues.encode_list_bool hf

open Lean Meta in
/-- Prepare tuple-valued functions using function metavariables. Abstract the input before
creating each metavariable, so matching a call can infer its component functions. -/
private meta partial def prepareFunction (type : Expr) : MetaM Expr := do
  let constructor ← forallBoundedTelescope type (some 1) fun _ body => do
    let body ← whnf body
    if body.isAppOf ``Prod then return some ``Prod.mk
    if body.isAppOf ``Sigma then return some ``Sigma.mk
    return none
  match constructor with
  | none => mkFreshExprMVar type
  | some constructor =>
    let leftType ← forallBoundedTelescope type (some 1) fun inputs body => do
      mkForallFVars inputs (← whnf body).getAppArgs[0]!
    let left ← prepareFunction leftType
    let rightType ← forallBoundedTelescope type (some 1) fun inputs body => do
      let right := (← whnf body).getAppArgs[1]!
      mkForallFVars inputs (if constructor == ``Prod.mk then right
        else mkApp right (mkAppN left inputs))
    let right ← prepareFunction rightType
    forallBoundedTelescope type (some 1) fun inputs body => do
      let args := (← whnf body).getAppArgs
      mkLambdaFVars inputs (← mkAppOptM constructor
        #[some args[0]!, some args[1]!, some (mkAppN left inputs), some (mkAppN right inputs)])

open Lean Meta in
/-- Prepare ordinary and dependent tuple arguments before matching a certified call. -/
meta def prepareArgument (domain type : Expr) : MetaM Expr := do
  prepareFunction (← mkArrow domain type)

/-- Reading a pair field also works when its type depends on the input. -/
theorem pair_fst_rule {α : Type} {encode : α → Word} {left right : α → Word}
    (h : IsPolyTime encode (fun a => List.BitPair.encode (left a) (right a))) :
    IsPolyTime encode left := by
  simpa only [List.BitPair.fst_encode] using h.bitPair_fst

/-- Read the second field without requiring its type or encoding to be constant. -/
theorem pair_snd_rule {α : Type} {encode : α → Word} {left right : α → Word}
    (h : IsPolyTime encode (fun a => List.BitPair.encode (left a) (right a))) :
    IsPolyTime encode right := by
  simpa only [List.BitPair.snd_encode] using h.bitPair_snd

open Lean Meta in
/-- Reuse a certified tuple-valued algorithm when a client reads one of its fields. Only
explicit pair encodings are projected, so proof search never guesses an output encoding. -/
meta partial def withProjections (certificate : Expr) : MetaM (Array Expr) := do
  let type ← instantiateMVars (← inferType certificate)
  let program ← Core.betaReduce (← etaExpand type.getAppArgs.back!)
  let projections ← lambdaTelescope program fun _ body => do
    unless body.isAppOf ``DFunLike.coe do return #[]
    let encoding := body.getAppArgs[4]!
    if encoding.isAppOf ``pairEncoding || encoding.isAppOf ``sigmaEncoding then
      return #[``pair_fst_rule, ``pair_snd_rule]
    return #[]
  let mut certificates := #[certificate]
  for projection in projections do
    certificates := certificates ++ (← withProjections (← mkAppM projection #[certificate]))
  return certificates

open Lean Meta Elab Tactic in
@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeInputProjection : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let input ← mkAppM ``isPolyTime_input #[target.getAppArgs[1]!]
  for certificate in ← withProjections input do
    let saved ← saveState
    try
      unless ← isDefEq (← inferType certificate) target do throwError "different input field"
      closeMainGoal `polytime certificate
      return
    catch _ => saved.restore
  throwError "not an encoded input field"

-- Instantiate the called algorithm from a known certificate before searching its arguments.
-- Unrestricted composition rules leave both the algorithm and its encoding undetermined.
open Lean Meta Elab Tactic in
@[aesop unsafe 50% tactic (rule_sets := [PolyTime])]
private meta def polytimeCall : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``IsPolyTime do
      throwError "expected a polynomial-time goal"
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.type.isAppOf ``IsPolyTime then continue
      for certificate in ← withProjections decl.toExpr do
        let type ← inferType certificate
        for tuple in [true, false] do
          let saved ← saveState
          try
            if tuple then
              let argument ← prepareArgument target.getAppArgs[0]! type.getAppArgs[0]!
              -- Reduce constructed arguments before matching through an abstract output encoding.
              let composed ← withLocalDeclD `input target.getAppArgs[0]! fun input =>
                mkLambdaFVars #[input] (mkApp type.getAppArgs.back! (mkApp argument input))
              unless ← isDefEq (← withReducible (reduce composed)) target.getAppArgs.back! do
                throwError "the certified algorithm does not match this call"
              applyWithArguments ``IsPolyTime.comp_encoded #[(`f, argument), (`hg, certificate)]
            else
              applyWithArguments ``IsPolyTime.comp_pair #[(`hf, certificate)]
            let goals ← getGoals
            if ← goals.anyM (fun subgoal => do isDefEq (← subgoal.getType) target) then
              throwError "composition made no progress"
            return
          catch _ => saved.restore
    throwError "no applicable local algorithm certificate"

attribute [aesop norm simp (rule_sets := [PolyTime])]
  forall_and

-- Preserve typed input embeddings in PPT goals: probabilistic composition needs their
-- injectivity proofs. Only deterministic goals normalize these encodings to plain functions.
open Lean Meta Elab Tactic Turing.MultiTapeTM in
@[aesop norm -50 tactic (rule_sets := [PolyTime])]
private meta def polytimeEncoding : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  evalTactic (← `(tactic| simp only [boolEncoding, wordEncoding, Function.Embedding.coeFn_mk]))

-- Certify fully specified constant outputs before simplification expands large unary words.
-- Normalization must not instantiate metavariables shared with other proof-search goals.
open Lean Meta Elab Tactic in
@[aesop norm -100 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstant : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``IsPolyTime && !target.hasExprMVar do
    throwError "expected a fully specified polynomial-time goal"
  let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
  lambdaTelescope program fun inputs body => do
    if inputs.any (fun input => body.containsFVar input.fvarId!) then
      throwError "the output depends on the input"
  liftMetaTactic fun goal => goal.applyConst ``isPolyTime_const

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PolyTime])]
  foldl_rule
  Turing.MultiTapeTM.isPolyTime_const
  Turing.MultiTapeTM.isPolyTime_input
  Turing.MultiTapeTM.isPolyTime_decode_list_bool
  Turing.MultiTapeTM.isPolyTime_flatMap
  Turing.MultiTapeTM.isPolyTime_map
  Turing.MultiTapeTM.isPolyTime_filter
  Turing.MultiTapeTM.isPolyTime_unaryLength
  Turing.MultiTapeTM.isPolyTime_tail
  Turing.MultiTapeTM.isPolyTime_head
  Turing.MultiTapeTM.isPolyTime_foldl_bool
  Turing.MultiTapeTM.isPolyTime_takeWhile
  Turing.MultiTapeTM.isPolyTime_dropWhile
  Turing.MultiTapeTM.isPolyTime_security
  Turing.MultiTapeTM.isPolyTime_auxiliaryInput
  Turing.MultiTapeTM.isPolyTime_fst
  Turing.MultiTapeTM.isPolyTime_snd
  Turing.MultiTapeTM.IsPolyTime.reverse
  Turing.MultiTapeTM.IsPolyTime.zipWith
  Turing.MultiTapeTM.IsPolyTime.list_flatten
  Turing.MultiTapeTM.IsPolyTime.flatten

attribute [aesop safe apply (rule_sets := [PolyTime])]
  headD_rule
  replicate_false_rule
  Nat.le_refl
  Turing.MultiTapeTM.IsPolyTime.append
  Turing.MultiTapeTM.IsPolyTime.flatMap
  Turing.MultiTapeTM.IsPolyTime.map
  Turing.MultiTapeTM.IsPolyTime.filter
  Turing.MultiTapeTM.IsPolyTime.count
  Turing.MultiTapeTM.IsPolyTime.any
  Turing.MultiTapeTM.IsPolyTime.unaryLength
  Turing.MultiTapeTM.IsPolyTime.tail
  Turing.MultiTapeTM.IsPolyTime.head
  Turing.MultiTapeTM.IsPolyTime.foldl_bool
  Turing.MultiTapeTM.IsPolyTime.iterate_of_length_le
  Turing.MultiTapeTM.IsPolyTime.takeWhile
  Turing.MultiTapeTM.IsPolyTime.dropWhile
  Turing.MultiTapeTM.IsPolyTime.parameterInput
  Turing.MultiTapeTM.IsPolyTime.list_tail
  Turing.MultiTapeTM.IsPolyTime.bitPair_fst
  Turing.MultiTapeTM.IsPolyTime.bitPair_snd
  Turing.MultiTapeTM.IsPolyTime.getD
  Turing.MultiTapeTM.IsPolyTime.list_getD
  Turing.MultiTapeTM.IsPolyTime.range
  Turing.MultiTapeTM.isPolyTime_list_headD
  Turing.MultiTapeTM.isPolyTime_list_tail
  Turing.MultiTapeTM.isPolyTime_list_unaryLength
  Turing.MultiTapeTM.IsPolyTime.list_reverse
  Turing.MultiTapeTM.IsPolyTime.list_map
  Turing.MultiTapeTM.IsPolyTime.list_flatMap
  Turing.MultiTapeTM.IsPolyTime.list_filter
  Turing.MultiTapeTM.IsPolyTime.unary_add
  Turing.MultiTapeTM.IsPolyTime.unary_mul
  Turing.MultiTapeTM.IsPolyTime.unary_pow
  Turing.MultiTapeTM.IsPolyTime.unary_sub
  Turing.MultiTapeTM.IsPolyTime.unary_min
  Turing.MultiTapeTM.IsPolyTime.unary_lt
  Turing.MultiTapeTM.IsPolyTime.unary_le
  Turing.MultiTapeTM.IsPolyTime.unary_eq
  Turing.MultiTapeTM.IsPolyTime.unary_div_two
  Turing.MultiTapeTM.IsPolyTime.unary_min_one
  Turing.MultiTapeTM.IsPolyTime.unary_log2

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PolyTime])]
  Turing.MultiTapeTM.isPolyTime_bitPair_fst
  Turing.MultiTapeTM.isPolyTime_bitPair_snd

attribute [aesop unsafe 50% apply (rule_sets := [PolyTime])]
  Turing.MultiTapeTM.IsPolyTime.drop
  Turing.MultiTapeTM.IsPolyTime.take
  Turing.MultiTapeTM.IsPolyTime.list_drop
  Turing.MultiTapeTM.IsPolyTime.list_take
  Turing.MultiTapeTM.IsPolyTime.fst
  Turing.MultiTapeTM.IsPolyTime.snd
  Turing.MultiTapeTM.IsPolyTime.list_unaryLength
  Turing.MultiTapeTM.IsPolyTime.map_with_bit

attribute [aesop unsafe 50% apply (index := [unindexed]) (rule_sets := [PolyTime])]
  Turing.MultiTapeTM.IsPolyTime.beq

-- A singleton's bit premise would repeat the conclusion; leave it to the Boolean rules.
open Lean Meta Elab Tactic in
@[aesop safe 100 tactic (rule_sets := [PolyTime])]
private meta def polytimeCons : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let isCons ← lambdaTelescope target.getAppArgs.back! fun _ body =>
    pure (body.isAppOf ``List.cons && !body.getAppArgs.back!.isAppOf ``List.nil)
  unless isCons do throwError "expected a nonsingleton list constructor"
  evalTactic (← `(tactic| apply IsPolyTime.cons))

-- Apply branching only to an actual conditional, without inventing an unknown condition.
open Lean Meta Elab Tactic in
@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def polytimeIte : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let (isIte, isBitIte, isAppliedIte) ←
      lambdaTelescope target.getAppArgs.back! fun _ body => do
    let body ← whnf body
    return (body.isAppOf ``ite, body.isAppOf ``List.cons &&
      body.getAppArgs.back!.isAppOf ``List.nil && body.getAppArgs[1]!.consumeMData.isAppOf ``ite,
      body.isApp && body.appArg!.consumeMData.isAppOf ``ite)
  unless isIte || isBitIte || isAppliedIte do throwError "expected a conditional"
  if isBitIte then
    evalTactic (← `(tactic| simp only [apply_ite (fun bit : Bool => [bit])]))
  else if isAppliedIte then
    evalTactic (← `(tactic| simp only [apply_ite]))
  evalTactic (← `(tactic| first | apply IsPolyTime.cond | apply IsPolyTime.ite))

-- Resolve the collection's encoding before searching the callback. Otherwise Aesop may search
-- the callback with an undetermined element encoding, even when the input is a simple projection.
open Lean Meta Elab Tactic in
@[aesop safe 50 tactic (rule_sets := [PolyTime])]
private meta def polytimeCollection : TacticM Unit := withMainContext do
  let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let rule ← lambdaTelescope target.getAppArgs.back! fun _ body => do
    if body.isAppOf ``List.map then
      return if body.getAppArgs[0]!.isConstOf ``Bool then
        ``word_map_with_rule else ``list_map_bool_rule
    if body.isAppOf ``List.flatMap then
      return if body.getAppArgs[0]!.isConstOf ``Bool then
        ``word_flatMap_with_rule else ``list_flatMap_word_rule
    if let some values := body.getAppArgs.back? then
      if values.isAppOf ``List.map then return ``list_map_with_rule
      if values.isAppOf ``List.flatMap then return ``list_flatMap_with_rule
      if values.isAppOf ``List.filter then return ``list_filter_with_rule
    throwError "expected a collection combinator"
  liftMetaTactic fun goal => goal.applyConst rule
  evalTactic (← `(tactic| case hvalues => solve | aesop (rule_sets := [PolyTime])))

/-- Synthesize a polynomial-time word-program certificate from registered rules. -/
macro "polytime" : tactic => `(tactic| solve | aesop (rule_sets := [PolyTime]))

end Cslib.Tactic.PolyTime
