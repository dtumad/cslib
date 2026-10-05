/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Realizer

/-!
# Source query bounds from uniform machine clocks

An oracle that counts selected requests makes their number observable in the joint semantics.
Full-support answers reflect every structural source path into a machine execution. The
machine's transition bound therefore bounds external requests in the source program itself.
Private coins remain unobserved and need not have the same placement in the two programs.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

private noncomputable def queryCounter (select : (effects Oracle).A → Bool) :
    Oracle → Word → Kernel ℕ (Word × ℕ) := fun op word =>
  ⟨fun state => Measure.count.map (fun answer : Word =>
    (answer, state + (select (.inr (op, word))).toNat)), Measurable.of_discrete⟩

private theorem queryCounter_positive (select : (effects Oracle).A → Bool)
    (hcoin : select (.inl ()) = false) (op : (effects Oracle).A)
    (answer : (effects Oracle).B op) (state : ℕ) :
    effectKernel (queryCounter select) op state
      {(answer, state + (select op).toNat)} ≠ 0 := by
  cases op with
  | inl token =>
    cases token
    change ((uniformOn (Set.univ : Set Bool)).bind (fun bit => Measure.dirac (bit, state)))
      {(answer, state + (select (.inl ())).toNat)} ≠ 0
    rw [hcoin]
    simp only [Bool.toNat_false, Nat.add_zero,
      Measure.bind_dirac_eq_map _ Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
    have hpre : (fun bit : Bool => (bit, state)) ⁻¹' {(answer, state)} = {answer} := by
      ext bit
      simp
    rw [hpre, uniformOn_univ]
    simp
  | inr request =>
    change (Measure.count.map (fun value : Word =>
      (value, state + (select (.inr request)).toNat)))
        {(answer, state + (select (.inr request)).toNat)} ≠ 0
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
    have hpre : (fun value : Word => (value, state + (select (.inr request)).toNat)) ⁻¹'
        {(answer, state + (select (.inr request)).toNat)} = {answer} := by
      ext value
      simp
    simp [hpre]

private theorem queryCounter_ae (select : (effects Oracle).A → Bool)
    (hcoin : select (.inl ()) = false) (op : (effects Oracle).A) (state : ℕ) :
    ∀ᵐ out ∂effectKernel (queryCounter select) op state,
      out.2 = state + (select op).toNat := by
  cases op with
  | inl token =>
    cases token
    change ∀ᵐ out ∂((uniformOn (Set.univ : Set Bool)).bind
      (fun bit => Measure.dirac (bit, state))), out.2 = state + (select (.inl ())).toNat
    rw [hcoin, Measure.bind_dirac_eq_map _ Measurable.of_discrete]
    exact (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      (Filter.Eventually.of_forall fun _ => by simp)
  | inr request =>
    change ∀ᵐ out ∂(Measure.count.map (fun answer : Word =>
      (answer, state + (select (.inr request)).toNat))),
        out.2 = state + (select (.inr request)).toNat
    exact (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      (Filter.Eventually.of_forall fun _ => rfl)

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
private theorem foldl_count {P : PFunctor} (select : P.A → Bool)
    (events : List (Sigma P.B)) (state : ℕ) :
    events.foldl (fun count event => count + (select event.1).toNat) state =
      state + events.countP (fun event => select event.1) := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    cases hs : select event.1 <;> simp [List.foldl_cons, ih, hs, Nat.add_assoc, Nat.add_comm]

/-- Every source path makes at most as many selected external requests as the realizing
machine has transitions. No separate source query-bound hypothesis is required. -/
theorem Realizer.queryBoundP_le {input : α ↪ Word} {output : β ↪ Word}
    {program : α → (effects Oracle).FreeM β}
    (implementation : Realizer input output program) (a : α)
    (select : (effects Oracle).A → Bool) (hcoin : select (.inl ()) = false) :
    FreeM.queryBoundP select (program a) ≤ implementation.clock (input a).length := by
  let : ∀ op : (effects Oracle).A, Nonempty ((effects Oracle).B op) := by
    rintro (token | request)
    · exact inferInstanceAs (Nonempty Bool)
    · exact inferInstanceAs (Nonempty Word)
  let update := fun (op : (effects Oracle).A) (_ : (effects Oracle).B op) (state : ℕ) =>
    state + (select op).toNat
  apply FreeM.queryBoundP_le_of_countP_trace_le
  rintro ⟨value, events⟩ htrace
  have hencoded : MonadAttach.CanReturn
      (FreeM.trace ((fun value => some (output value)) <$> program a))
        (some (output value), events) := by
    rw [FreeM.trace_map]
    exact (FreeM.canReturn_map _ _ _).mpr ⟨(value, events), htrace, rfl⟩
  have hpositive := FreeM.runKernel_singleton_ne_zero_of_trace
    (effectKernel (queryCounter select)) update (queryCounter_positive select hcoin)
    _ hencoded 0
  rw [← implementation.runKernel_run a (queryCounter select) 0] at hpositive
  have hsupport := FreeM.runKernel_ae_exists_trace (effectKernel (queryCounter select)) update
    (queryCounter_ae select hcoin) (implementation.run a) 0
  obtain ⟨machineEvents, hmachine, hcount⟩ :=
    (ae_iff_of_countable.mp hsupport) _ hpositive
  simp only [update, foldl_count, Nat.zero_add] at hcount
  have hle := (FreeM.countP_trace_le_queryBoundP select (implementation.run a) hmachine).trans
    (implementation.queryBoundP_run_le a select hcoin)
  rw [hcount] at hle
  exact_mod_cast hle

/-- Uniform polynomial time supplies a polynomial budget for all source oracle requests. -/
theorem IsPPT.queryBoundP_le {input : α ↪ Word} {output : β ↪ Word}
    {program : α → (effects Oracle).FreeM β} (h : IsPPT input output program) :
    ∃ c d : ℕ, ∀ a (select : (effects Oracle).A → Bool), select (.inl ()) = false →
      FreeM.queryBoundP select (program a) ≤ (c * ((input a).length + 1) ^ d : ℕ) := by
  obtain ⟨implementation⟩ := isPPT_iff_nonempty_realizer.mp h
  exact ⟨implementation.coefficient, implementation.degree, implementation.queryBoundP_le⟩

end Turing.MultiTapePTM
