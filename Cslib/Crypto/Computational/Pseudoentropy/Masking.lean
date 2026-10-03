/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Entropy
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

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Game 3.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  We replace the set indicator in that experiment by a fresh soft-mask coin.
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.1.1,
  observes that hard-core statements can be formulated using measures.
  [Write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf).
  The entropy and sampling facts here are ingredients for that route; the weak learner still
  requires the extraction and hybrid argument.
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

end Cslib.Crypto.Pseudoentropy
