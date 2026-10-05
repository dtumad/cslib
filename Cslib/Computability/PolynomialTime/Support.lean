/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Free.Kernel

/-!
# Reachable outputs of a machine realization

Correctness against every kernel ensures that every terminating machine path produces a valid
encoded program result. The proof uses counting measure as a full-support test interpretation;
it does not add a probabilistic oracle or a decoder to the executable machine.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

variable {Oracle : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

private noncomputable def countingOracle (Oracle : Type) :
    Oracle → Word → Kernel Unit (Word × Unit) := fun _ _ => Kernel.const _ Measure.count

private theorem countingOracle_positive (op : (effects Oracle).A) (answer : (effects Oracle).B op) :
    effectKernel (countingOracle Oracle) op () {(answer, ())} ≠ 0 := by
  cases op with
  | inl token =>
    change ((uniformOn (Set.univ : Set Bool)).bind (fun bit => Measure.dirac (bit, ())))
      {(answer, ())} ≠ 0
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
    have hpreimage : (fun bit : Bool => (bit, ())) ⁻¹' {(answer, ())} = {answer} := by
      ext bit
      simp
    rw [hpreimage, uniformOn_univ]
    simp
  | inr request => simp [effectKernel, countingOracle]

/-- Every reached encoded machine result comes from a structurally reachable program value. -/
theorem Realizes.canReturn {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
    {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle}
    {fuel : ℕ} {input word : Word} {encode : α ↪ Word} {program : (effects Oracle).FreeM α}
    (h : machine.Realizes dispatch fuel input encode program)
    (hword : MonadAttach.CanReturn (machine.run fuel input) (some word)) :
    ∃ value, MonadAttach.CanReturn program value ∧ encode value = word := by
  have hpositive := FreeM.runKernel_singleton_ne_zero_of_canReturn
    (effectKernel (fun port => countingOracle Oracle (dispatch port))) ()
    (fun op answer => countingOracle_positive op answer) _ _ hword
  rw [h Unit (countingOracle Oracle) ()] at hpositive
  have hreach := (ae_iff_of_countable.mp
    (FreeM.runKernel_ae_canReturn (effectKernel (countingOracle Oracle))
      ((fun value => some (encode value)) <$> program) ())) (some word, ()) hpositive
  obtain ⟨value, hvalue, hencode⟩ := (FreeM.canReturn_map _ _ _).mp hreach
  exact ⟨value, hvalue, Option.some.inj hencode⟩

/-- Uniform kernel correctness identifies exactly the possible encoded output words. -/
theorem Realizes.canReturn_iff {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
    {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle}
    {fuel : ℕ} {input word : Word} {encode : α ↪ Word} {program : (effects Oracle).FreeM α}
    (h : machine.Realizes dispatch fuel input encode program) :
    MonadAttach.CanReturn (machine.run fuel input) (some word) ↔
      ∃ value, MonadAttach.CanReturn program value ∧ encode value = word := by
  refine ⟨h.canReturn, ?_⟩
  rintro ⟨value, hvalue, rfl⟩
  have hencoded : MonadAttach.CanReturn
      ((fun value => some (encode value)) <$> program) (some (encode value)) :=
    (FreeM.canReturn_map _ _ _).mpr ⟨value, hvalue, rfl⟩
  have hpositive := FreeM.runKernel_singleton_ne_zero_of_canReturn
    (effectKernel (countingOracle Oracle)) () countingOracle_positive _ _ hencoded
  rw [← h Unit (countingOracle Oracle) ()] at hpositive
  exact (ae_iff_of_countable.mp
    (FreeM.runKernel_ae_canReturn (effectKernel (fun port => countingOracle Oracle (dispatch port)))
      (machine.run fuel input) ())) (some (encode value), ()) hpositive

end Turing.MultiTapePTM
