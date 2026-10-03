/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Selection
public import Cslib.Computability.Probabilistic.Adaptive
public import Cslib.Computability.Probabilistic.Repeat

/-!
# Strict PPT empirical selection

Candidate selection composes an efficient indexed trial with polynomial candidate and repetition
counts. The common adaptive-loop certificate charges for both indices and the running success
count. Their bounds hold on every execution, independently of the statistical accuracy theorem.
-/

@[expose] public section

namespace Cslib.Probability

/-- Selecting among polynomially many efficient tests using polynomially many trials is strict
PPT. The test may capture the complete original input. -/
theorem IsPPTOn.selectBest {α : Type} {input : α ↪ Word}
    {count trials : α → ℕ} {test : α → ℕ → ProbComp Bool}
    (htest : IsPPTOn (pairEncoding input unaryEncoding) boolEncoding
      (fun pair => test pair.1 pair.2))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (htrials : IsPolyTime input (fun a => unaryEncoding (trials a))) :
    IsPPTOn input unaryEncoding (fun a => OracleComp.selectBest (count a) (trials a) (test a)) := by
  let stateEncoding := pairEncoding unaryEncoding (pairEncoding unaryEncoding unaryEncoding)
  have htest' : IsPPTOn (pairEncoding input stateEncoding) boolEncoding
      (fun pair => test pair.1 pair.2.1) :=
    htest.preprocess (prepare := fun pair : α × (ℕ × ℕ × ℕ) => (pair.1, pair.2.1))
      (by dsimp only [stateEncoding]; polytime)
  have htrials' : IsPolyTime (pairEncoding input stateEncoding)
      (fun pair => unaryEncoding (trials pair.1)) :=
    htrials.comp_encoded (isPolyTime_fst input stateEncoding)
  have hstep : IsPPTOn (pairEncoding input stateEncoding) stateEncoding
      (fun pair => OracleComp.selectStep (trials pair.1) (test pair.1) pair.2) := by
    unfold OracleComp.selectStep
    apply (htest'.countTrue htrials').map_with
    simp only [OracleComp.selectUpdate, stateEncoding, apply_ite]
    polytime
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  obtain ⟨ct, dt, ht⟩ := htrials.length_le
  simp only [unaryEncoding, Function.Embedding.coeFn_mk, List.length_replicate] at hc ht
  have hloop := (IsPPTOn.iterate_with_spec (stateEncoding := stateEncoding)
    (initial := fun _ => (0, 0, 0))
    (step := fun a => OracleComp.selectStep (trials a) (test a))
    (isPolyTime_const input (stateEncoding (0, 0, 0))) hcount hstep
    (fun a i state => state.1 = i ∧ state.2.1 ≤ i ∧ state.2.2 ≤ trials a)
    (by simp) (fun a i _ state hstate next hnext =>
      ProbComp.selectStep_bounded (trials a) (test a) i state hstate next hnext)
    (size := fun n => 4 * (cc * (n + 1) ^ dc) + ct * (n + 1) ^ dt + 2)
    (by fun_prop) (by
      intro a i state hi hstate
      dsimp only [stateEncoding]
      simp only [length_pairEncoding, unaryEncoding, Function.Embedding.coeFn_mk,
        List.length_replicate]
      have := hc a
      have := ht a
      lia)).1
  exact hloop.map (by dsimp only [stateEncoding]; polytime)

@[aesop safe -10 tactic (rule_sets := [PPT])]
private meta def pptSelection : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.PPT.applyHead #[(``OracleComp.selectBest, ``IsPPTOn.selectBest)]

end Cslib.Probability
