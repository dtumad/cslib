/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Decision
public import Cslib.Computability.Probabilistic.Adaptive

/-!
# A clocked hard-core boosting program

The state stores a threshold, a list of predictor descriptions, and a stopping flag.
A fixed certified evaluator interprets each description on an observation. Each active round
tests the majority guard, optionally raises the threshold, and requests one new predictor.

The supplied learner is an explicit program with its own efficiency and correctness obligations.
We truncate its output to the declared description bound on every execution, including failures.
The analysis must therefore certify the truncated predictor. This gives a polynomial bound on
the complete state throughout the clocked loop without a probabilistic runtime exception.

## References

* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
  Figure 2 and Lemma 2.14. [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  We replace the worst-dense-set stopping test by its proved polynomial clock. The majority
  stopping test remains explicit, and all rational tests use finite fair-bit sampling.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Cslib.Probability

/-- The executable state of the boosting loop. Predictor descriptions are ordinary binary words. -/
structure State where
  /-- Once true, all remaining clock ticks preserve this state. -/
  stopped : Bool
  /-- The number of shifts subtracted from the raw vote margin. -/
  threshold : ℕ
  /-- Predictor descriptions, newest first. -/
  predictors : List Word
  deriving DecidableEq

namespace State

/-- Reuse the standard Boolean, unary, and list encodings. -/
def encoding : State ↪ Word :=
  ⟨fun state => pairEncoding boolEncoding (pairEncoding unaryEncoding (listEncoding wordEncoding))
    (state.stopped, state.threshold, state.predictors), by
    intro left right h
    have hfields := (pairEncoding boolEncoding
      (pairEncoding unaryEncoding (listEncoding wordEncoding))).injective h
    cases left
    cases right
    simpa using hfields⟩

/-- Start before any learned predictors or threshold shifts. -/
def initial : State := ⟨false, 0, []⟩

/-- Evaluate the current collection on an observation. The truth label is not an input. -/
def votes (evaluate : Word → Word → Bool) (state : State) (observation : Word) : Word :=
  state.predictors.map (fun code => evaluate code observation)

/-- Move the threshold according to the sampled shift decision. -/
def shift (state : State) (yes : Bool) : State :=
  { state with threshold := state.threshold + if yes then 1 else 0 }

/-- Add a bounded predictor description. -/
def add (state : State) (bound : ℕ) (code : Word) : State :=
  { state with predictors := code.take bound :: state.predictors }

@[simp] theorem votes_initial (evaluate : Word → Word → Bool) (observation : Word) :
    initial.votes evaluate observation = [] := rfl

@[simp] theorem votes_shift (evaluate : Word → Word → Bool) (state : State)
    (yes : Bool) (observation : Word) :
    (state.shift yes).votes evaluate observation = state.votes evaluate observation := rfl

@[simp] theorem votes_add (evaluate : Word → Word → Bool) (state : State)
    (bound : ℕ) (code observation : Word) :
    (state.add bound code).votes evaluate observation =
      evaluate (code.take bound) observation :: state.votes evaluate observation := rfl

@[simp] theorem length_encoding (state : State) :
    (encoding state).length = 2 * state.threshold +
      (listEncoding wordEncoding state.predictors).length + 4 := by
  simp [encoding, boolEncoding, length_pairEncoding]
  lia

/-- After `rounds` rounds there are at most that many shifts and bounded descriptions. -/
def Bounded (rounds codeBound : ℕ) (state : State) : Prop :=
  state.threshold ≤ rounds ∧ state.predictors.length ≤ rounds ∧
    ∀ code ∈ state.predictors, code.length ≤ codeBound

@[simp] theorem bounded_initial (codeBound : ℕ) : Bounded 0 codeBound initial := by
  simp [Bounded, initial]

/-- A bound remains valid when more rounds are allowed. -/
theorem Bounded.mono {rounds more codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) (hmore : rounds ≤ more) :
    Bounded more codeBound state :=
  ⟨h.1.trans hmore, h.2.1.trans hmore, h.2.2⟩

/-- An optional shift and a truncated description preserve the resource invariant. -/
theorem Bounded.shift_add {rounds codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) (yes : Bool) (code : Word) :
    Bounded (rounds + 1) codeBound ((state.shift yes).add codeBound code) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [add, shift]
    split <;> lia [h.1]
  · simpa only [add, shift, List.length_cons] using Nat.add_le_add_right h.2.1 1
  · intro candidate hcandidate
    rcases List.mem_cons.mp hcandidate with rfl | hcandidate
    · simp only [List.length_take]; exact min_le_left _ _
    · exact h.2.2 candidate hcandidate

/-- The semantic resource invariant bounds the complete encoded state. -/
theorem Bounded.length_encoding_le {rounds codeBound : ℕ} {state : State}
    (h : Bounded rounds codeBound state) :
    (encoding state).length ≤ rounds * (2 * codeBound + 3) + 4 := by
  have hsum := List.sum_le_length_nsmul
    (state.predictors.map (fun code => 2 * code.length + 1)) (2 * codeBound + 1) (by
      intro value hvalue
      obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hvalue
      have := h.2.2 code hcode
      lia)
  simp only [List.length_map, smul_eq_mul] at hsum
  simp only [length_encoding, length_listEncoding, wordEncoding, Function.Embedding.refl_apply]
  have := Nat.mul_le_mul_right (2 * codeBound + 1) h.2.1
  nlinarith [h.1]

section Efficiency

variable {α : Type} {input : α → Word} {state : α → State}

private theorem fields_isPolyTime (hstate : IsPolyTime input (fun a => encoding (state a))) :
    IsPolyTime input (fun a =>
      pairEncoding boolEncoding (pairEncoding unaryEncoding (listEncoding wordEncoding))
        ((state a).stopped, (state a).threshold, (state a).predictors)) := hstate

/-- Efficient field values construct an efficient state. -/
theorem mk_isPolyTime {stopped : α → Bool} {threshold : α → ℕ} {predictors : α → List Word}
    (hstopped : IsPolyTime input (fun a => [stopped a]))
    (hthreshold : IsPolyTime input (fun a => unaryEncoding (threshold a)))
    (hpredictors : IsPolyTime input (fun a => listEncoding wordEncoding (predictors a))) :
    IsPolyTime input (fun a => encoding ⟨stopped a, threshold a, predictors a⟩) :=
  hstopped.pair (hthreshold.pair hpredictors)

/-- Project the stopping flag through the shared pair implementation. -/
theorem stopped_isPolyTime (hstate : IsPolyTime input (fun a => encoding (state a))) :
    IsPolyTime input (fun a => [(state a).stopped]) :=
  (fields_isPolyTime hstate).fst

/-- Project the threshold through the shared pair implementation. -/
theorem threshold_isPolyTime (hstate : IsPolyTime input (fun a => encoding (state a))) :
    IsPolyTime input (fun a => unaryEncoding (state a).threshold) :=
  (fields_isPolyTime hstate).snd.fst

/-- Project the predictor collection through the shared pair implementation. -/
theorem predictors_isPolyTime (hstate : IsPolyTime input (fun a => encoding (state a))) :
    IsPolyTime input (fun a => listEncoding wordEncoding (state a).predictors) :=
  (fields_isPolyTime hstate).snd.snd

/-- Evaluating a list of descriptions is an ordinary captured map. -/
theorem votes_isPolyTime {evaluate : Word → Word → Bool} {observation : α → Word}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hstate : IsPolyTime input (fun a => encoding (state a)))
    (hobservation : IsPolyTime input observation) :
    IsPolyTime input (fun a => (state a).votes evaluate (observation a)) := by
  have hcallback : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.2 pair.1]) := by
    polytime
  exact ((predictors_isPolyTime hstate).list_map_with
    (environment := wordEncoding) (output := boolEncoding)
    (f := fun obs code => evaluate code obs) hobservation hcallback).decode_list_bool

/-- Updating the threshold uses its field certificate and the efficient Boolean decision. -/
theorem shift_isPolyTime {yes : α → Bool}
    (hstate : IsPolyTime input (fun a => encoding (state a)))
    (hyes : IsPolyTime input (fun a => [yes a])) :
    IsPolyTime input (fun a => encoding ((state a).shift (yes a))) := by
  have hincrement : IsPolyTime input (fun a => unaryEncoding (if yes a then 1 else 0)) := by
    simpa only [apply_ite] using hyes.cond
      (isPolyTime_const input (unaryEncoding 1)) (isPolyTime_const input (unaryEncoding 0))
  exact mk_isPolyTime (stopped_isPolyTime hstate)
    ((threshold_isPolyTime hstate).unary_add hincrement) (predictors_isPolyTime hstate)

/-- Truncation and list insertion charge for the complete stored predictor description. -/
theorem add_isPolyTime {bound : α → ℕ} {code : α → Word}
    (hstate : IsPolyTime input (fun a => encoding (state a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hcode : IsPolyTime input code) :
    IsPolyTime input (fun a => encoding ((state a).add (bound a) (code a))) := by
  exact mk_isPolyTime (stopped_isPolyTime hstate) (threshold_isPolyTime hstate)
    ((hcode.take hbound).list_cons (predictors_isPolyTime hstate))

end Efficiency

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem stopped_rule : IsPolyTime encoding (fun state => [state.stopped]) :=
  stopped_isPolyTime (isPolyTime_input encoding)

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem threshold_rule :
    IsPolyTime encoding (fun state => unaryEncoding state.threshold) :=
  threshold_isPolyTime (isPolyTime_input encoding)

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem predictors_rule :
    IsPolyTime encoding (fun state => listEncoding wordEncoding state.predictors) :=
  predictors_isPolyTime (isPolyTime_input encoding)

open Lean Meta Elab Tactic in
@[aesop safe -10 tactic (rule_sets := [PolyTime])]
private meta def stateConstructor : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``IsPolyTime do throwError "expected a polynomial-time goal"
  let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
  lambdaTelescope program fun _ body => do
    unless body.isAppOf ``DFunLike.coe && body.getAppArgs[4]!.isAppOf ``encoding do
      throwError "expected a boosting state encoding"
    let value := body.getAppArgs.back!
    let rule ← if value.isAppOf ``State.mk then pure ``mk_isPolyTime
      else if value.isAppOf ``State.shift then pure ``shift_isPolyTime
      else if value.isAppOf ``State.add then pure ``add_isPolyTime
      else throwError "expected a boosting state constructor or update"
    liftMetaTactic fun goal => goal.applyConst rule

end State

/-- Natural parameters for exact dyadic weights and polynomial sampling budgets. -/
structure Parameters where
  /-- Each sampled guard has failure probability at most `2⁻confidence`. -/
  confidence : ℕ
  /-- The numerator of the target density. -/
  densityNumerator : ℕ
  /-- The parameter whose `dyadicSize` is the density denominator. -/
  densityBound : ℕ
  /-- The parameter whose `dyadicSize` is the reciprocal weight rate. -/
  rateBound : ℕ
  /-- Maximum length of each stored predictor description. -/
  codeBound : ℕ

namespace Parameters

/-- The density denominator is a positive power of two. -/
def denominator (params : Parameters) : ℕ := dyadicSize params.densityBound

/-- The reciprocal weight rate is a positive power of two. -/
def inverseRate (params : Parameters) : ℕ := dyadicSize params.rateBound

/-- A sufficient majority-test precision for every positive density numerator. -/
def majorityPrecision (params : Parameters) : ℕ := 32 * params.denominator

/-- A sufficient density-test precision at weight rate `1 / inverseRate`. -/
def shiftPrecision (params : Parameters) : ℕ := 32 * params.denominator * params.inverseRate

/-- A polynomial clock whenever `0 < densityNumerator ≤ denominator`. -/
def clock (params : Parameters) : ℕ := 4 * params.inverseRate ^ 2 * params.denominator ^ 3

end Parameters

/-- Draw a fresh labeled observation and evaluate the current predictor collection on it. -/
def withVotes (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (state : State) : ProbComp (Word × Bool) :=
  (fun sample => (state.votes evaluate sample.1, sample.2)) <$> source

/-- Training samples compose with the certified evaluator without exposing a machine. -/
theorem withVotes_isPPT {α : Type} {input : α ↪ Word} {evaluate : Word → Word → Bool}
    {source : α → ProbComp (Word × Bool)} {state : α → State}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hstate : IsPolyTime input (fun a => State.encoding (state a))) :
    IsPPTOn input (pairEncoding wordEncoding boolEncoding)
      (fun a => withVotes evaluate (source a) (state a)) := by
  have hsample := isPolyTime_snd input (pairEncoding wordEncoding boolEncoding)
  have hcaller := isPolyTime_fst input (pairEncoding wordEncoding boolEncoding)
  have hvotes := State.votes_isPolyTime hevaluate (hstate.comp_encoded hcaller) hsample.fst
  exact hsource.map_with (hvotes.pair hsample.snd)

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptWithVotes : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``withVotes, ``withVotes_isPPT)]

/-- One round of boosting. A previously stopped state is returned unchanged. -/
noncomputable def round (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (params : Parameters) (state : State) : ProbComp State := do
  if state.stopped then return state
  let training := withVotes evaluate source state
  let stop ← testMajority params.confidence params.majorityPrecision
    params.densityNumerator params.denominator
    ((fun sample => nonpositiveMargin sample.1 sample.2) <$> training)
  if stop then return { state with stopped := true }
  let shift ← testShift params.confidence params.shiftPrecision params.densityNumerator
    params.denominator 1 params.inverseRate do
      let (votes, truth) ← training
      sampleWeight params.rateBound 1 state.threshold votes truth
  let shifted := state.shift shift
  let code ← learn shifted
  return shifted.add params.codeBound code

/-- Run the sampled boosting body for the proved polynomial clock. -/
noncomputable def run (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (params : Parameters) : ProbComp State :=
  OracleComp.iterate params.clock (round evaluate source learn params) State.initial

/-- Resource bounds hold on every outcome, including erroneous tests and learner failures. -/
theorem round_bounded (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (params : Parameters) {rounds : ℕ} {state : State}
    (hstate : State.Bounded rounds params.codeBound state) :
    ∀ next ∈ (ProbComp.eval (round evaluate source learn params state)).support,
      State.Bounded (rounds + 1) params.codeBound next := by
  intro next hnext
  unfold round at hnext
  split at hnext
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
    subst next
    exact hstate.mono (by lia)
  · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
    obtain ⟨stop, _, hnext⟩ := hnext
    split at hnext
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
      subst next
      exact hstate.mono (by lia)
    · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff,
        ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
      obtain ⟨shift, _, code, _, rfl⟩ := hnext
      exact hstate.shift_add shift code

/-- The clocked loop stores at most one bounded predictor per round. -/
theorem run_bounded (evaluate : Word → Word → Bool) (source : ProbComp (Word × Bool))
    (learn : State → ProbComp Word) (params : Parameters) :
    ∀ state ∈ (ProbComp.eval (run evaluate source learn params)).support,
      State.Bounded params.clock params.codeBound state :=
  ProbComp.iterate_invariant params.clock (round evaluate source learn params) State.initial
    (fun rounds => State.Bounded rounds params.codeBound) (State.bounded_initial _)
    (fun _ _ _ hstate => round_bounded evaluate source learn params hstate)

/-- The complete sampled round composes the evaluator, source, learner, and unary parameters.
No machine implementation is part of the client's proof. -/
theorem round_isPPT {α : Type} {input : α ↪ Word} {evaluate : Word → Word → Bool}
    {source : α → ProbComp (Word × Bool)} {learn : α → State → ProbComp Word}
    {params : α → Parameters}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hlearn : IsPPTOn (pairEncoding input State.encoding) wordEncoding
      (fun pair => learn pair.1 pair.2))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (hdensityNum : IsPolyTime input (fun a => unaryEncoding (params a).densityNumerator))
    (hdensityBound : IsPolyTime input (fun a => unaryEncoding (params a).densityBound))
    (hrateBound : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hcodeBound : IsPolyTime input (fun a => unaryEncoding (params a).codeBound)) :
    IsPPTOn (pairEncoding input State.encoding) State.encoding
      (fun pair => round evaluate (source pair.1) (learn pair.1) (params pair.1) pair.2) := by
  have htraining : IsPPTOn (pairEncoding input State.encoding)
      (pairEncoding wordEncoding boolEncoding)
      (fun pair => withVotes evaluate (source pair.1) pair.2) := withVotes_isPPT hevaluate
    (hsource.preprocess (isPolyTime_fst input State.encoding))
    (isPolyTime_snd input State.encoding)
  unfold round Parameters.majorityPrecision Parameters.shiftPrecision
    Parameters.denominator Parameters.inverseRate
  apply IsPPTOn.cond
  · polytime
  · ppt
  · dsimp only
    apply IsPPTOn.bind_with (middle := boolEncoding)
    · apply testMajority_isPPT <;> ppt
    · apply IsPPTOn.cond
      · polytime
      · ppt
      · apply IsPPTOn.bind_with (middle := boolEncoding)
        · apply testShift_isPPT <;> ppt
        · ppt

/-- Polynomially bounded parameters and a certified learner give a strict PPT boosting loop.
The single resource invariant also proves `run_bounded`, independently of correctness. -/
theorem run_isPPT {α : Type} {input : α ↪ Word} {evaluate : Word → Word → Bool}
    {source : α → ProbComp (Word × Bool)} {learn : α → State → ProbComp Word}
    {params : α → Parameters}
    (hevaluate : IsPolyTime coinInputEncoding (fun pair => [evaluate pair.1 pair.2]))
    (hsource : IsPPTOn input (pairEncoding wordEncoding boolEncoding) source)
    (hlearn : IsPPTOn (pairEncoding input State.encoding) wordEncoding
      (fun pair => learn pair.1 pair.2))
    (hconfidence : IsPolyTime input (fun a => unaryEncoding (params a).confidence))
    (hdensityNum : IsPolyTime input (fun a => unaryEncoding (params a).densityNumerator))
    (hdensityBound : IsPolyTime input (fun a => unaryEncoding (params a).densityBound))
    (hrateBound : IsPolyTime input (fun a => unaryEncoding (params a).rateBound))
    (hcodeBound : IsPolyTime input (fun a => unaryEncoding (params a).codeBound)) :
    IsPPTOn input State.encoding (fun a => run evaluate (source a) (learn a) (params a)) := by
  have hclock : IsPolyTime input (fun a => unaryEncoding (params a).clock) := by
    unfold Parameters.clock Parameters.inverseRate Parameters.denominator
    polytime
  obtain ⟨cc, dc, hc⟩ := hclock.length_le
  obtain ⟨cb, db, hb⟩ := hcodeBound.length_le
  simp only [unaryEncoding, Function.Embedding.coeFn_mk, List.length_replicate] at hc hb
  refine (IsPPTOn.iterate_with_spec (stateEncoding := State.encoding)
    (initial := fun _ => State.initial)
    (step := fun a => round evaluate (source a) (learn a) (params a))
    (isPolyTime_const input (State.encoding State.initial))
    hclock (round_isPPT hevaluate hsource hlearn hconfidence hdensityNum hdensityBound
      hrateBound hcodeBound)
    (fun a rounds => State.Bounded rounds (params a).codeBound)
    (fun _ => State.bounded_initial _)
    (fun a _ _ _ hstate => round_bounded evaluate (source a) (learn a) (params a) hstate)
    (size := fun n => cc * (n + 1) ^ dc * (2 * (cb * (n + 1) ^ db) + 3) + 4)
    (by fun_prop) ?_).1
  intro a rounds state hrounds hstate
  exact hstate.length_encoding_le.trans (Nat.add_le_add_right
    (Nat.mul_le_mul (hrounds.trans (hc a)) (by have := hb a; lia)) 4)

end Cslib.Crypto.Pseudoentropy.Boosting
