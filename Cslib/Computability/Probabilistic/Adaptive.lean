/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Iteration
public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Computability.Probabilistic.CoinTape
public import Cslib.Tactic.PPT

/-!
# Strict PPT adaptive iteration

A bounded probabilistic loop is strict PPT when its step is strict PPT and one invariant
bounds the size of every reachable state. The rule also returns the final invariant.
`iterate_with_spec` allows the body to capture the original input. The bounded-growth and
length-nonincreasing variants derive their size invariants automatically.

These resource invariants hold on every possible execution. The semantic iteration module
separately supplies approximate correctness rules that add per-round failure probabilities.

Internally, the shared saved-coin evaluator turns the loop into a deterministic list fold.
One polynomial coin budget works for every reachable state, and independently sampled blocks
give the exact adaptive distribution. The client supplies no machine, replay code, or decoder.
-/

@[expose] public section

namespace Cslib.Probability

/-- A Hoare-style rule for a bounded adaptive probabilistic loop. The invariant proves both
the final postcondition and the polynomial bound on all intermediate states. -/
theorem IsPPTOn.iterate_spec {α State : Type} {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : State → ProbComp State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → State → Prop) (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i, i < count a → ∀ state, invariant a i state →
      ∀ next ∈ (ProbComp.eval (step state)).support, invariant a (i + 1) next)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size (input a).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a, ∀ state ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support,
        invariant a (count a) state := by
  obtain ⟨c, d, evaluate, hevaluate, hsupport, hlaw⟩ := hstep.exists_total_seeded_evaluator
  obtain ⟨cs, ds, hs⟩ := hsize
  let bound (a : α) := cs * ((input a).length + 1) ^ ds
  let budget (a : α) := c * (bound a + 1) ^ d
  have hbudget (a : α) (i : ℕ) (state : State) (hi : i ≤ count a)
      (hinvariant : invariant a i state) :
      c * ((stateEncoding state).length + 1) ^ d ≤ budget a :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left
      (Nat.add_le_add_right ((hbound a i state hi hinvariant).trans (hs _)) 1) d)
  have hfold : IsPolyTime (pairEncoding input wordEncoding) (fun pair => stateEncoding
      ((maskRows (count pair.1) (budget pair.1) pair.2).foldl evaluate (initial pair.1))) := by
    have hrows : IsPolyTime (pairEncoding input wordEncoding) (fun pair =>
        listEncoding wordEncoding (maskRows (count pair.1) (budget pair.1) pair.2)) := by
      unfold budget bound
      polytime
    have hstart : IsPolyTime (pairEncoding input wordEncoding)
        (fun pair => stateEncoding (initial pair.1)) := by polytime
    refine (hrows.list_foldl_spec hstart hevaluate
      (fun pair consumed state => invariant pair.1 consumed.length state)
      (fun pair => hinit pair.1) ?_
      (size := fun n => cs * (n + 1) ^ ds) (by fun_prop) ?_).1
    · intro pair consumed state coins hprefix hinvariant
      have hlength := hprefix.length_le
      simp only [List.length_append, List.length_singleton, maskRows,
        List.length_map, List.length_range] at hlength
      simpa only [List.length_append, List.length_singleton] using
        hpreserve pair.1 consumed.length (by lia) state hinvariant _ (hsupport state coins)
    · intro pair consumed state hprefix hinvariant
      have hlength := hprefix.length_le
      simp only [maskRows, List.length_map, List.length_range] at hlength
      have hstate := (hbound pair.1 consumed.length state hlength hinvariant).trans (hs _)
      exact hstate.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
        (by simp only [length_pairEncoding]; lia) ds))
  let replayed (a : α) : ProbComp State := do
    let coins ← OracleComp.sampleBits (count a * budget a)
    return (maskRows (count a) (budget a) coins).foldl evaluate (initial a)
  have hefficient : IsPPTOn input stateEncoding replayed := by
    have hbits : IsPolyTime input (fun a => unaryEncoding (count a * budget a)) := by
      unfold budget bound
      polytime
    unfold replayed
    ppt
  refine ⟨hefficient.congr ?_, fun a =>
    ProbComp.iterate_invariant (count a) step (initial a) (invariant a) (hinit a) (hpreserve a)⟩
  intro a
  have hjoint := ProbComp.eval_iterate_of_uniform (Seed := BitString (budget a))
    (count a) step (initial a) (fun state bits => evaluate state (List.ofFn bits))
    (invariant a) (hinit a) (hpreserve a) (fun i hi state hinvariant => by
      simpa only [uniformBits, PMF.map_comp, Function.comp_def] using
        hlaw state (budget a) (hbudget a i state hi.le hinvariant))
  rw [hjoint]
  have hrows := congrArg (PMF.map (fun rows : Fin (count a) → BitString (budget a) =>
    (List.ofFn rows).foldl (fun state bits => evaluate state (List.ofFn bits)) (initial a)))
    (uniformBits_masksFromWord (count a) (budget a))
  rw [PMF.map_comp] at hrows
  simpa only [replayed, ProbComp.eval, OracleComp.eval_bind, OracleComp.eval_sampleBits,
    OracleComp.eval_pure, Function.comp_def, maskRows_eq_ofFn, ← List.foldl_map,
    List.map_ofFn, PMF.map] using hrows

/-- The loop body may capture the original input. Its certificate charges for that input and
the current state; the invariant describes only the client's state. -/
theorem IsPPTOn.iterate_with_spec {α State : Type}
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : α → State → ProbComp State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPPTOn (pairEncoding input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → State → Prop) (hinit : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i, i < count a → ∀ state, invariant a i state →
      ∀ next ∈ (ProbComp.eval (step a state)).support, invariant a (i + 1) next)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size (input a).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a, ∀ state ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support,
        invariant a (count a) state := by
  let packedStep (pair : α × State) : ProbComp (α × State) :=
    (fun next => (pair.1, next)) <$> step pair.1 pair.2
  have hpackedStep : IsPPTOn (pairEncoding input stateEncoding)
      (pairEncoding input stateEncoding) packedStep :=
    hstep.pair (isPolyTime_fst input stateEncoding)
  have hstart : IsPolyTime input (fun a => pairEncoding input stateEncoding (a, initial a)) :=
    (isPolyTime_input input).pair hinitial
  have hpacked := (IsPPTOn.iterate_spec hstart hcount hpackedStep
    (fun a i pair => pair.1 = a ∧ invariant a i pair.2)
    (fun a => And.intro rfl (hinit a))
    (by
      rintro a i hi ⟨captured, state⟩ ⟨rfl, hstate⟩ next hnext
      simp only [packedStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
      obtain ⟨value, hvalue, rfl⟩ := hnext
      exact ⟨rfl, hpreserve captured i hi state hstate value hvalue⟩)
    (size := fun n => 2 * n + size n + 1) (by fun_prop)
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩
      simp only [length_pairEncoding]
      have := hbound captured i state hi hstate
      lia)).1
  refine ⟨(hpacked.map (isPolyTime_snd input stateEncoding)).congr ?_, fun a =>
    ProbComp.iterate_invariant (count a) (step a) (initial a)
      (invariant a) (hinit a) (hpreserve a)⟩
  intro a
  rw [OracleComp.iterate_map (count a) (step a) packedStep (fun state => (a, state))
    (fun _ => rfl) (initial a)]
  simp only [ProbComp.eval_map, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- A strict PPT step with bounded growth can be repeated polynomially many times. The
initializer and unary count supply the overall size bound automatically. -/
theorem IsPPTOn.iterate_of_bounded_growth {α State : Type}
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : State → ProbComp State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    {growth : ℕ} (hgrowth : ∀ state, ∀ next ∈ (ProbComp.eval (step state)).support,
      (stateEncoding next).length ≤ (stateEncoding state).length + growth) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) := by
  obtain ⟨ci, di, hi⟩ := hinitial.length_le
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  simp only [unaryEncoding, Function.Embedding.coeFn_mk, List.length_replicate] at hc
  exact (IsPPTOn.iterate_spec hinitial hcount hstep
    (fun a i state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + i * growth)
    (by simp)
    (by
      intro a i _ state hinvariant next hnext
      have := hgrowth state next hnext
      nlinarith)
    (size := fun n => ci * (n + 1) ^ di + cc * (n + 1) ^ dc * growth) (by fun_prop)
    (fun a i state hiCount hinvariant => hinvariant.trans
      (Nat.add_le_add (hi a) (Nat.mul_le_mul_right growth (hiCount.trans (hc a)))))).1

/-- Iteration of a step that never increases its encoded state size needs no extra size proof. -/
theorem IsPPTOn.iterate_of_length_le {α State : Type}
    {input : α ↪ Word} {stateEncoding : State ↪ Word}
    {initial : α → State} {count : α → ℕ} {step : State → ProbComp State}
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (hshrink : ∀ state, ∀ next ∈ (ProbComp.eval (step state)).support,
      (stateEncoding next).length ≤ (stateEncoding state).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  IsPPTOn.iterate_of_bounded_growth hinitial hcount hstep (growth := 0)
    (by simpa using hshrink)

end Cslib.Probability
