/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Entropy
public import Cslib.Crypto.Computational.Prediction
public import Cslib.Crypto.Computational.Hybrid.Sequence
public import Cslib.Crypto.Computational.Pseudoentropy.Boosting.Sampling

/-!
# Fresh masks for a pseudoentropy pair

A mask coin chooses whether to replace a label by a fresh fair bit. Conditional on any
deterministic observation, the resulting label has at least as much entropy as the average
replacement probability. This remains true when the mask probability depends on the original
input and label.

Every occurrence draws a fresh mask, including repeated inputs. The executable boosting weights
provide such coins exactly, so their density is a lower bound on the masked label's conditional
entropy. The sampler and its strict PPT certificate use the usual programming combinators.

The distinguishing-to-prediction reduction then samples a random coordinate and supplies a trial
bit at that coordinate. Its weighted prediction bias is exactly the complete sequence gap divided
by the dyadic coordinate range. The target observation is its only target-dependent input; labels
and masks are computed only on fresh surrounding samples.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We replace the set indicator in that experiment by a fresh soft-mask coin.
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.1.1,
  observes that hard-core statements can be formulated using measures.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  The entropy and prediction facts here are ingredients for that route; completing the weak
  learner still requires the extraction bound and a bounded description selected with high
  probability, including both signs of distinguishing advantage.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Cslib.Probability Cslib.Probability.PMF

/-- Replace a label by a fresh fair bit when the supplied mask accepts. -/
noncomputable def maskBit (mask : ProbComp Bool) (truth : Bool) : ProbComp Bool := do
  let replace ← mask
  if replace then OracleComp.uniform Bool else pure truth

/-- Sample an observation and a label with a fresh input-dependent randomization mask. -/
noncomputable def maskedSample {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) : ProbComp (β × Bool) := do
  let x ← source
  (observe x, ·) <$> maskBit (mask x) (truth x)

/-- The mask's law is an ordinary mixture of a fair bit and the original label. -/
theorem eval_maskBit (mask : ProbComp Bool) (truth : Bool) :
    ProbComp.eval (maskBit mask truth) = (ProbComp.eval mask).bind
      (fun replace => if replace then PMF.uniformOfFintype Bool else PMF.pure truth) := by
  unfold maskBit
  rw [ProbComp.eval_bind]
  congr 1
  funext replace
  cases replace <;> simp [OracleComp.uniform]

/-- The original label remains with probability `1 - maskProbability / 2`. -/
theorem eval_maskBit_apply (mask : ProbComp Bool) (truth bit : Bool) :
    (ProbComp.eval (maskBit mask truth) bit).toReal =
      if bit = truth then 1 - (ProbComp.eval mask true).toReal / 2
      else (ProbComp.eval mask true).toReal / 2 := by
  have hmass := sum_toReal (ProbComp.eval mask)
  simp only [Fintype.sum_bool] at hmass
  rw [eval_maskBit, bind_apply_toReal]
  cases truth <;> cases bit <;>
    norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply] <;> linarith

/-- A fresh replacement contributes one bit of conditional randomness whenever the mask accepts. -/
theorem entropy_maskBit_ge (mask : ProbComp Bool) (truth : Bool) :
    (ProbComp.eval mask true).toReal ≤ entropy (ProbComp.eval (maskBit mask truth)) := by
  rw [eval_maskBit]
  have h := sum_mul_entropy_le_entropy_bind (ProbComp.eval mask)
    (fun replace => if replace then PMF.uniformOfFintype Bool else PMF.pure truth)
  simpa using h

/-- The masked pair reveals the original observation and averages the pointwise masked laws. -/
theorem eval_maskedSample {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) :
    ProbComp.eval (maskedSample source observe truth mask) =
      (ProbComp.eval source).bind
        (fun x => (ProbComp.eval (maskBit (mask x) (truth x))).map (observe x, ·)) := by
  simp only [maskedSample, ProbComp.eval_bind, ProbComp.eval_map]

/-- Hiding all but a deterministic observation leaves at least the average mask probability
in conditional label entropy. In particular, mask probabilities may depend on hidden labels. -/
theorem maskedSample_entropy_ge {α β : Type} [Fintype α] [Finite β] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) :
    (∑ x, (ProbComp.eval source x).toReal * (ProbComp.eval (mask x) true).toReal) ≤
      conditionalEntropy (ProbComp.eval (maskedSample source observe truth mask)) := by
  rw [eval_maskedSample]
  exact (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (entropy_maskBit_ge (mask x) (truth x)) ENNReal.toReal_nonneg)).trans
      (conditionalEntropy_observe_ge (ProbComp.eval source)
        (fun x => ProbComp.eval (maskBit (mask x) (truth x))) observe)

/-- The entropy available from executable boosting masks is at least their exact soft density. -/
theorem maskedSample_weight_entropy_ge {α β : Type} [Fintype α] [Finite β]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool) (votes : α → Word)
    (bound numerator threshold : ℕ) :
    Boosting.density (ProbComp.eval source) (numerator / dyadicSize bound)
      (fun x => Boosting.voteMargin (votes x) (truth x) - threshold) ≤
        conditionalEntropy (ProbComp.eval (maskedSample source observe truth (fun x =>
          Boosting.sampleWeight bound numerator threshold (votes x) (truth x)))) := by
  simpa only [Boosting.eval_sampleWeight_true, Boosting.density] using
    maskedSample_entropy_ge source observe truth
      (fun x => Boosting.sampleWeight bound numerator threshold (votes x) (truth x))

/-- Distinguishing a real label from its masked version gives prediction bias weighted by the
mask probability. The predictor itself receives only the test, not the mask or hidden label. -/
theorem maskBit_prediction_gap (test : Bool → ProbComp Bool) (mask : ProbComp Bool)
    (truth : Bool) :
    winProbability (test truth) - winProbability (maskBit mask truth >>= test) =
      (ProbComp.eval mask true).toReal *
        (winProbability ((fun guess => guess == truth) <$> bitPredictor test) - 1 / 2) := by
  rw [winProbability_bind, bitPredictor_bias]
  simp only [Fintype.sum_bool, eval_maskBit_apply]
  cases truth <;> norm_num <;> ring

/-- The exact masked distinguishing gap is the source-averaged weighted prediction bias.
Only the observation is passed to the predictor; the mask may depend on the entire source. -/
theorem maskedSample_prediction_gap {α β : Type} [Fintype α] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool)
    (test : β → Bool → ProbComp Bool) :
    winProbability (source >>= fun x => test (observe x) (truth x)) -
        winProbability (maskedSample source observe truth mask >>= fun pair => test pair.1 pair.2) =
      ∑ x, (ProbComp.eval source x).toReal * (ProbComp.eval (mask x) true).toReal *
        (winProbability ((fun guess => guess == truth x) <$> bitPredictor (test (observe x))) -
          1 / 2) := by
  simp only [maskedSample, bind_assoc, bind_map_left]
  rw [winProbability_bind, winProbability_bind, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, maskBit_prediction_gap, mul_assoc]

/-- A certified mask and an efficiently supplied label give a strict PPT randomized label. -/
theorem maskBit_isPPT {α : Type} {input : α ↪ Word} {mask : α → ProbComp Bool}
    {truth : α → Bool} (hmask : IsPPTOn input boolEncoding mask)
    (htruth : IsPolyTime input (fun a => [truth a])) :
    IsPPTOn input boolEncoding (fun a => maskBit (mask a) (truth a)) := by
  unfold maskBit
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptMaskBit : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``maskBit, ``maskBit_isPPT)]

/-- Masked sampling composes a certified source, observation, label, and mask. All callbacks may
capture the original input, and all intermediate encodings are charged. -/
theorem maskedSample_isPPT {α β γ : Type} {input : α ↪ Word}
    {sample : β ↪ Word} {output : γ ↪ Word} {source : α → ProbComp β}
    {observe : α → β → γ} {truth : α → β → Bool} {mask : α → β → ProbComp Bool}
    (hsource : IsPPTOn input sample source)
    (hobserve : IsPolyTime (pairEncoding input sample) (fun pair => output (observe pair.1 pair.2)))
    (htruth : IsPolyTime (pairEncoding input sample) (fun pair => [truth pair.1 pair.2]))
    (hmask : IsPPTOn (pairEncoding input sample) boolEncoding (fun pair => mask pair.1 pair.2)) :
    IsPPTOn input (pairEncoding output boolEncoding)
      (fun a => maskedSample (source a) (observe a) (truth a) (mask a)) := by
  unfold maskedSample
  apply hsource.bind_with
  ppt

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptMaskedSample : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``maskedSample, ``maskedSample_isPPT)]

/-- Predict from one public observation by simulating a random-coordinate masked hybrid.
Hidden labels and masks are computed only on independently generated surrounding samples. -/
noncomputable def maskedSequencePredictor {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) (count : ℕ)
    (test : List (β × Bool) → ProbComp Bool) (observation : β) : ProbComp Bool :=
  bitPredictor (fun trial => sequenceTest (maskedSample source observe truth mask)
    ((fun x => (observe x, truth x)) <$> source) count test (observation, trial))

/-- A sequence distinguisher gives one predictor whose mask-weighted bias equals the complete
distinguishing gap divided by the dyadic coordinate range. This allows arbitrary finite sources,
arbitrary observations, hidden-label-dependent masks, and zero repetitions. -/
theorem maskedSequence_prediction_gap {α β : Type} [Fintype α] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) (count : ℕ)
    (test : List (β × Bool) → ProbComp Bool) :
    winProbability (OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
        >>= test) -
      winProbability (OracleComp.replicate count (maskedSample source observe truth mask)
        >>= test) =
      (dyadicSize count : ℝ) * ∑ x,
        (ProbComp.eval source x).toReal * (ProbComp.eval (mask x) true).toReal *
          (winProbability ((fun guess => guess == truth x) <$>
            maskedSequencePredictor source observe truth mask count test (observe x)) - 1 / 2) := by
  rw [sequenceTest_gap]
  unfold maskedSequencePredictor
  congr 1
  simpa only [bind_map_left] using maskedSample_prediction_gap source observe truth mask
    (fun observation trial => sequenceTest (maskedSample source observe truth mask)
      ((fun x => (observe x, truth x)) <$> source) count test (observation, trial))

/-- The complete masked-coordinate prediction reduction is strict PPT whenever its source,
observation, labels, masks, test, and repetition count have certificates. -/
theorem maskedSequencePredictor_isPPT {Param α β : Type} {input : Param ↪ Word}
    {sample : α ↪ Word} {output : β ↪ Word} {source : Param → ProbComp α}
    {observe : Param → α → β} {truth : Param → α → Bool} {mask : Param → α → ProbComp Bool}
    {count : Param → ℕ} {test : Param → List (β × Bool) → ProbComp Bool}
    {observation : Param → β}
    (hsource : IsPPTOn input sample source)
    (hobserve : IsPolyTime (pairEncoding input sample) (fun pair => output (observe pair.1 pair.2)))
    (htruth : IsPolyTime (pairEncoding input sample) (fun pair => [truth pair.1 pair.2]))
    (hmask : IsPPTOn (pairEncoding input sample) boolEncoding (fun pair => mask pair.1 pair.2))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (htest : IsPPTOn (pairEncoding input (listEncoding (pairEncoding output boolEncoding)))
      boolEncoding (fun pair => test pair.1 pair.2))
    (hobservation : IsPolyTime input (fun a => output (observation a))) :
    IsPPTOn input boolEncoding (fun a => maskedSequencePredictor (source a) (observe a)
      (truth a) (mask a) (count a) (test a) (observation a)) := by
  have hmasked := maskedSample_isPPT hsource hobserve htruth hmask
  have horiginal : IsPPTOn input (pairEncoding output boolEncoding)
      (fun a => (fun x => (observe a x, truth a x)) <$> source a) :=
    hsource.map_with (by polytime)
  unfold maskedSequencePredictor
  apply bitPredictor_isPPT
  apply sequenceTest_isPPT (sample := pairEncoding output boolEncoding)
  · exact hmasked.preprocess (prepare := Prod.fst) (isPolyTime_fst input boolEncoding)
  · exact horiginal.preprocess (prepare := Prod.fst) (isPolyTime_fst input boolEncoding)
  · polytime
  · exact htest.preprocess
      (prepare := fun pair : (Param × Bool) × List (β × Bool) => (pair.1.1, pair.2)) (by polytime)
  · polytime

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptMaskedSequencePredictor : Lean.Elab.Tactic.TacticM Unit := do
  Cslib.Tactic.PPT.applyHead #[(``maskedSequencePredictor, ``maskedSequencePredictor_isPPT)]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    case hsource => solve | aesop (rule_sets := [PPT, PolyTime])))

end Cslib.Crypto.Pseudoentropy
