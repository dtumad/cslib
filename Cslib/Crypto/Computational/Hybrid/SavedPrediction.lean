/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Hybrid.Sequence
public import Cslib.Crypto.Computational.Prediction

/-!
# Saving the randomness of a coordinate predictor

A predictor description stores the sampled surrounding examples, a trial bit, and the test's
coins. It contains no program for generating those examples, so its size does not recursively
include earlier predictors used during training. The evaluator accepts arbitrary word codes;
the decoder is total even when a boosting loop truncates a description.

The saved test input is split into two encoded fragments around the missing labeled example.
This avoids requiring an efficient inverse for an arbitrary observation or parameter encoding.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We save the sampled context explicitly to bound descriptions in the constructive learner.
-/

@[expose] public section

namespace Cslib.Crypto.SavedPrediction

open Probability

/-- Finite data needed to reuse one coordinate predictor on arbitrary observations. -/
structure Description where
  /-- Padding coordinates reject the test. -/
  active : Bool
  /-- The trial label inserted with the new observation. -/
  trial : Bool
  /-- Encoded test input before the inserted example. -/
  front : Word
  /-- Encoded test input after the inserted example. -/
  back : Word
  /-- The test's saved random tape. -/
  coins : Word
  deriving DecidableEq

namespace Description

/-- Encode a description using the shared pair representation. -/
def encoding : Description ↪ Word :=
  ⟨fun desc => pairEncoding boolEncoding
    (pairEncoding boolEncoding (pairEncoding wordEncoding coinInputEncoding))
      (desc.active, desc.trial, desc.front, desc.back, desc.coins), by
    intro left right h
    have hfields := (pairEncoding boolEncoding
      (pairEncoding boolEncoding (pairEncoding wordEncoding coinInputEncoding))).injective h
    cases left
    cases right
    simpa using hfields⟩

/-- Decode any word. Missing or malformed fields use the total pair projections. -/
def decode (code : Word) : Description where
  active := (List.BitPair.fst code).headD false
  trial := (List.BitPair.fst (List.BitPair.snd code)).headD false
  front := List.BitPair.fst (List.BitPair.snd (List.BitPair.snd code))
  back := List.BitPair.fst (List.BitPair.snd (List.BitPair.snd (List.BitPair.snd code)))
  coins := List.BitPair.snd (List.BitPair.snd (List.BitPair.snd (List.BitPair.snd code)))

@[simp] theorem decode_encoding (desc : Description) : decode (encoding desc) = desc := by
  cases desc
  simp [decode, encoding, pairEncoding, boolEncoding, wordEncoding]

@[simp] theorem length_encoding (desc : Description) :
    (encoding desc).length =
      2 * (desc.front.length + desc.back.length) + desc.coins.length + 8 := by
  simp [encoding, boolEncoding, wordEncoding]
  lia

/-- Insert a labeled example directly into the saved encoded input. -/
def input (desc : Description) (observation : Word) : Word :=
  desc.front ++ pairEncoding wordEncoding wordEncoding
    (pairEncoding wordEncoding boolEncoding (observation, desc.trial), desc.back)

@[simp] theorem length_input (desc : Description) (observation : Word) :
    (desc.input observation).length =
      desc.front.length + desc.back.length + 4 * observation.length + 5 := by
  simp [input, boolEncoding, wordEncoding]
  lia

end Description

/-- Evaluate a saved predictor with a fixed total word evaluator for the original test. -/
def evaluate (test : Word → Word → Word) (code observation : Word) : Bool :=
  let desc := Description.decode code
  if desc.active && (test desc.coins (desc.input observation)).headD false then
    desc.trial else !desc.trial

/-- Evaluation is deterministic polynomial time on every code, including truncated codes. -/
theorem evaluate_isPolyTime {test : Word → Word → Word}
    (htest : IsPolyTime coinInputEncoding (fun pair => test pair.1 pair.2)) :
    IsPolyTime coinInputEncoding (fun pair => [evaluate test pair.1 pair.2]) := by
  unfold evaluate Description.decode Description.input
  polytime

/-- A tape long enough for every observation up to the supplied width. -/
def coinBudget (c d width : ℕ) (front back : Word) : ℕ :=
  c * (front.length + back.length + 4 * width + 6) ^ d

/-- Attach one random tape to an already sampled context. -/
noncomputable def save (c d width : ℕ) (trial : Bool) (front back : Word) : ProbComp Word := do
  let coins ← OracleComp.sampleBits (coinBudget c d width front back)
  return Description.encoding ⟨true, trial, front, back, coins⟩

/-- Drawing and saving the common tape has a strict PPT certificate. -/
theorem save_isPPT {Param : Type} {input : Param ↪ Word}
    {front back : Param → Word} {width : Param → ℕ} {trial : Param → Bool} (c d : ℕ)
    (hfront : IsPolyTime input front) (hback : IsPolyTime input back)
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (htrial : IsPolyTime input (fun a => [trial a])) :
    IsPPTOn input wordEncoding (fun a => save c d (width a) (trial a) (front a) (back a)) := by
  simp only [save, coinBudget, Description.encoding, Function.Embedding.coeFn_mk]
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSave : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``save, ``save_isPPT)]

variable {α : Type}

/-- Sample and save the surrounding examples before any target observation is supplied. -/
noncomputable def splice (sample : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (before after : ℕ)
    (c d width : ℕ) (trial : Bool) : ProbComp Word := do
  let front ← OracleComp.replicate before replacement
  let back ← OracleComp.replicate after original
  let front := pairEncoding wordEncoding (listEncoding (pairEncoding sample boolEncoding))
    (base, front)
  let back := listEncoding (pairEncoding sample boolEncoding) back
  save c d width trial front back

/-- Sample a reusable predictor description, including the fair trial and rejected padding. -/
noncomputable def sample (encoding : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ) : ProbComp Word := do
  let trial ← OracleComp.uniform Bool
  let split ← sampleDyadicIndex count
  if split < count then
    splice encoding base replacement original split (count - split - 1) c d width trial
  else return Description.encoding ⟨false, trial, [], [], []⟩

private theorem input_splice (encoding : α ↪ Word) (base : Word)
    (front back : List (α × Bool)) (trial : Bool) (coins : Word) (observation : α) :
    (Description.mk true trial
      (pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding)) (base, front))
      (listEncoding (pairEncoding encoding boolEncoding) back) coins).input (encoding observation) =
      pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
        (base, front ++ (observation, trial) :: back) := by
  simp [Description.input, pairEncoding, List.BitPair.encode, List.append_assoc, wordEncoding,
    listEncoding_append, listEncoding_cons]

private theorem coinBudget_ge (desc : Description) (observation : Word) (c d width : ℕ)
    (hwidth : observation.length ≤ width) :
    c * ((desc.input observation).length + 1) ^ d ≤
      coinBudget c d width desc.front desc.back := by
  rw [Description.length_input]
  unfold coinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  lia

/-- Replaying a saved splice has exactly the original trial predictor's distribution. Only the
target observation needs a size bound; the surrounding samples choose their own coin budget. -/
theorem eval_splice (encoding : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (before after c d width : ℕ) (trial : Bool)
    (test : List (α × Bool) → ProbComp Bool) (raw : Word → Word → Word)
    (hrealize : ∀ values budget,
      c * ((pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
        (base, values)).length + 1) ^ d ≤ budget →
      ProbComp.eval (test values) = (uniformBits budget).map (fun coins =>
        (raw coins (pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
          (base, values))).headD false))
    (observation : α) (hwidth : (encoding observation).length ≤ width) :
    ProbComp.eval ((fun code => evaluate raw code (encoding observation)) <$>
      splice encoding base replacement original before after c d width trial) =
      ProbComp.eval (trialPredictor
        (fun trial => spliceTest replacement original before after test (observation, trial))
        trial) := by
  simp only [splice, save, trialPredictor, spliceTest, map_bind, map_pure, ProbComp.eval_bind]
  congr 1
  funext front
  congr 1
  funext back
  let desc : Description := ⟨true, trial,
    pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding)) (base, front),
    listEncoding (pairEncoding encoding boolEncoding) back, []⟩
  have hbudget := coinBudget_ge desc (encoding observation) c d width hwidth
  rw [input_splice] at hbudget
  rw [ProbComp.eval_map, hrealize _ _ hbudget]
  simp [ProbComp.eval, OracleComp.eval_sampleBits, evaluate, Function.comp_def,
    desc, input_splice, PMF.map]

/-- Sampling all predictor randomness once preserves every bounded observation's prediction
law, including rejected padding coordinates. -/
theorem eval_sample (encoding : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ)
    (test : List (α × Bool) → ProbComp Bool) (raw : Word → Word → Word)
    (hrealize : ∀ values budget,
      c * ((pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
        (base, values)).length + 1) ^ d ≤ budget →
      ProbComp.eval (test values) = (uniformBits budget).map (fun coins =>
        (raw coins (pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
          (base, values))).headD false))
    (observation : α) (hwidth : (encoding observation).length ≤ width) :
    ProbComp.eval ((fun code => evaluate raw code (encoding observation)) <$>
      sample encoding base replacement original count c d width) =
      ProbComp.eval (bitPredictor
        (fun trial => sequenceTest replacement original count test (observation, trial))) := by
  simp only [sample, bitPredictor, sequenceTest, trialPredictor, map_bind, ProbComp.eval_bind]
  congr 1
  funext trial
  congr 1
  funext split
  by_cases hsplit : split < count
  · simpa only [hsplit, ite_true, trialPredictor] using
      eval_splice encoding base replacement original split (count - split - 1) c d width trial
        test raw hrealize observation hwidth
  · simp [hsplit, evaluate]

/-- Encoded surrounding examples and the public test parameter occupy this many bits. -/
def contextBound (baseSize count width : ℕ) : ℕ :=
  2 * baseSize + count * (4 * width + 5) + 1

/-- The complete description bound depends on sample sizes and the fixed test clock, not on
the program or stored state used to generate the surrounding examples. -/
def codeBound (baseSize count c d width : ℕ) : ℕ :=
  let context := contextBound baseSize count width
  2 * context + c * (context + 4 * width + 6) ^ d + 8

private theorem length_save {c d width : ℕ} {trial : Bool} {front back code : Word}
    (hcode : code ∈ (ProbComp.eval (save c d width trial front back)).support) :
    code.length = 2 * (front.length + back.length) + coinBudget c d width front back + 8 := by
  rw [save, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨coins, hcoins, hcode⟩ := hcode
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hcode
  subst code
  have hlength := length_of_mem_support_uniformBits (by
    simpa [ProbComp.eval] using hcoins)
  simpa only [Description.length_encoding] using congrArg
    (fun length => 2 * (front.length + back.length) + length + 8) hlength

private theorem length_labeledList_le (encoding : α ↪ Word) {values : List (α × Bool)}
    {width : ℕ} (hwidth : ∀ value ∈ values, (encoding value.1).length ≤ width) :
    (listEncoding (pairEncoding encoding boolEncoding) values).length ≤
      values.length * (4 * width + 5) := by
  have h := length_listEncoding_le (pairEncoding encoding boolEncoding)
    (bound := 2 * width + 2) (values := values) (by
      intro value hmem
      have := hwidth value hmem
      simp only [length_pairEncoding, boolEncoding, Function.Embedding.coeFn_mk,
        List.length_singleton]
      lia)
  convert h using 1
  congr 1
  lia

/-- Saving a fixed coordinate has a uniform description bound on every execution. -/
theorem length_splice_le (encoding : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (before after c d width : ℕ) (trial : Bool)
    (hreplacement : ∀ value ∈ (ProbComp.eval replacement).support,
      (encoding value.1).length ≤ width)
    (horiginal : ∀ value ∈ (ProbComp.eval original).support,
      (encoding value.1).length ≤ width)
    {code : Word}
    (hcode : code ∈ (ProbComp.eval
      (splice encoding base replacement original before after c d width trial)).support) :
    code.length ≤ codeBound base.length (before + after) c d width := by
  simp only [splice, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨front, hfront, back, hback, hcode⟩ := hcode
  obtain ⟨hfrontLength, hfrontSupport⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hfront
  obtain ⟨hbackLength, hbackSupport⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hback
  have hfrontSize := length_labeledList_le encoding
    (fun value hmem => hreplacement value (hfrontSupport value hmem))
  have hbackSize := length_labeledList_le encoding
    (fun value hmem => horiginal value (hbackSupport value hmem))
  have hcontext :
      (pairEncoding wordEncoding (listEncoding (pairEncoding encoding boolEncoding))
        (base, front)).length + (listEncoding (pairEncoding encoding boolEncoding) back).length ≤
      contextBound base.length (before + after) width := by
    simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply]
    unfold contextBound
    rw [hfrontLength] at hfrontSize
    rw [hbackLength] at hbackSize
    nlinarith
  rw [length_save hcode]
  dsimp only [codeBound, coinBudget]
  gcongr

/-- Every generated description fits a bound independent of the source algorithms' internal
state. Padding descriptions satisfy the same bound, including when `count = 0`. -/
theorem length_sample_le (encoding : α ↪ Word) (base : Word)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ)
    (hreplacement : ∀ value ∈ (ProbComp.eval replacement).support,
      (encoding value.1).length ≤ width)
    (horiginal : ∀ value ∈ (ProbComp.eval original).support,
      (encoding value.1).length ≤ width)
    {code : Word}
    (hcode : code ∈ (ProbComp.eval
      (sample encoding base replacement original count c d width)).support) :
    code.length ≤ codeBound base.length count c d width := by
  simp only [sample, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨trial, _, split, _, hcode⟩ := hcode
  split_ifs at hcode with hsplit
  · have hsize := length_splice_le encoding base replacement original split
      (count - split - 1) c d width trial hreplacement horiginal hcode
    apply hsize.trans
    dsimp only [codeBound, contextBound]
    gcongr <;> lia
  · rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hcode
    subst code
    simp [codeBound]

/-- A PPT test supplies one fixed efficient evaluator for all saved descriptions. No decoder
for either the public parameter or observation representation is required. -/
theorem exists_evaluator {Param : Type} {input : Param ↪ Word} {output : α ↪ Word}
    {test : Param → List (α × Bool) → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding input (listEncoding (pairEncoding output boolEncoding)))
      boolEncoding (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (predict : Word → Word → Bool),
      IsPolyTime coinInputEncoding (fun pair => [predict pair.1 pair.2]) ∧
      ∀ a replacement original count width observation, (output observation).length ≤ width →
        ProbComp.eval ((fun code => predict code (output observation)) <$>
          sample output (input a) replacement original count c d width) =
          ProbComp.eval (bitPredictor (fun trial =>
            sequenceTest replacement original count (test a) (observation, trial))) := by
  obtain ⟨c, d, raw, hefficient, hrealize⟩ := htest.exists_padded_bool_coin_evaluator
  refine ⟨c, d, evaluate raw, evaluate_isPolyTime hefficient, ?_⟩
  intro a replacement original count width observation hwidth
  apply eval_sample output (input a) replacement original count c d width (test a) raw
    (fun values budget hbudget => hrealize (a, values) budget hbudget) observation hwidth

/-- Saving context and coins is strict PPT whenever the sources and numerical bounds are. -/
theorem splice_isPPT {Param : Type} {input : Param ↪ Word} {output : α ↪ Word}
    {base : Param → Word} {replacement original : Param → ProbComp (α × Bool)}
    {before after width : Param → ℕ} {trial : Param → Bool} (c d : ℕ)
    (hbase : IsPolyTime input base)
    (hreplacement : IsPPTOn input (pairEncoding output boolEncoding) replacement)
    (horiginal : IsPPTOn input (pairEncoding output boolEncoding) original)
    (hbefore : IsPolyTime input (fun a => unaryEncoding (before a)))
    (hafter : IsPolyTime input (fun a => unaryEncoding (after a)))
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (htrial : IsPolyTime input (fun a => [trial a])) :
    IsPPTOn input wordEncoding (fun a =>
      splice output (base a) (replacement a) (original a) (before a) (after a) c d (width a)
        (trial a)) := by
  unfold splice
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSplice : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``splice, ``splice_isPPT)]

/-- The random-coordinate description sampler is a uniform strict PPT program. -/
theorem sample_isPPT {Param : Type} {input : Param ↪ Word} {output : α ↪ Word}
    {base : Param → Word} {replacement original : Param → ProbComp (α × Bool)}
    {count width : Param → ℕ} (c d : ℕ)
    (hbase : IsPolyTime input base)
    (hreplacement : IsPPTOn input (pairEncoding output boolEncoding) replacement)
    (horiginal : IsPPTOn input (pairEncoding output boolEncoding) original)
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a))) :
    IsPPTOn input wordEncoding (fun a =>
      sample output (base a) (replacement a) (original a) (count a) c d (width a)) := by
  unfold sample Description.encoding
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSample : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``sample, ``sample_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hreplacement => solve | aesop (rule_sets := [PPT, PolyTime])))

end Cslib.Crypto.SavedPrediction
