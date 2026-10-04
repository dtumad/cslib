/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Free.Kernel
public import Cslib.Foundations.MeasureTheory.Uniform
public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measure semantics for fair-coin machines

Private coins are independent uniform bits. Named oracle operations share one kernel state;
the interpretation records the joint output and final state. In particular, an oracle's state
is neither reset between calls nor split between operation names.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory

variable {Oracle : Type}
  [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]

instance (op : (effects Oracle).A) : MeasurableSpace ((effects Oracle).B op) :=
  match op with
  | .inl _ => inferInstanceAs (MeasurableSpace Bool)
  | .inr _ => inferInstanceAs (MeasurableSpace (List Bool))

instance (op : (effects Oracle).A) : DiscreteMeasurableSpace ((effects Oracle).B op) := by
  cases op with
  | inl _ => exact inferInstanceAs (DiscreteMeasurableSpace Bool)
  | inr _ => exact inferInstanceAs (DiscreteMeasurableSpace (List Bool))

instance (op : (effects Oracle).A) : Countable ((effects Oracle).B op) := by
  cases op with
  | inl _ => exact inferInstanceAs (Countable Bool)
  | inr _ => exact inferInstanceAs (Countable (List Bool))

variable {S α : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Fair private coins together with named operations on shared state. -/
noncomputable def effectKernel (oracle : Oracle → List Bool → Kernel S (List Bool × S)) :
    (op : (effects Oracle).A) → Kernel S ((effects Oracle).B op × S)
  | .inl _ =>
    { toFun := fun state => (uniformOn (Set.univ : Set Bool)).bind
        (fun bit => Measure.dirac (bit, state))
      measurable' := Measurable.of_discrete }
  | .inr (op, word) => oracle op word

instance (oracle : Oracle → List Bool → Kernel S (List Bool × S))
    [∀ op word, IsMarkovKernel (oracle op word)] (op : (effects Oracle).A) :
    IsMarkovKernel (effectKernel oracle op) := by
  cases op with
  | inl token =>
    refine ⟨fun state => ?_⟩
    exact isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  | inr request => exact inferInstanceAs (IsMarkovKernel (oracle request.1 request.2))

variable [Countable S] [MeasurableSpace α]
  (oracle : Oracle → List Bool → Kernel S (List Bool × S))

/-- A private coin leaves the shared oracle state untouched. -/
theorem runKernel_coin_bind (cont : Bool → (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle) (coin >>= cont) state =
      (uniformOn (Set.univ : Set Bool)).bind
        (fun bit => FreeM.runKernel (effectKernel oracle) (cont bit) state) := by
  change FreeM.runKernel (effectKernel oracle)
    ((FreeM.lift (P := effects Oracle) (.inl ())).bind cont) state = _
  rw [FreeM.runKernel_bind, FreeM.runKernel_lift]
  change ((uniformOn (Set.univ : Set Bool)).bind (fun bit => Measure.dirac (bit, state))).bind
    (fun out => FreeM.runKernel (effectKernel oracle) (cont out.1) out.2) = _
  rw [Measure.bind_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  simp only [Measure.dirac_bind Measurable.of_discrete]

/-- Unused private randomness has no observable effect, including on the oracle state. -/
theorem runKernel_coin_const (program : (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle) (coin >>= fun _ => program) state =
      FreeM.runKernel (effectKernel oracle) program state := by
  rw [runKernel_coin_bind]
  simp only [Measure.bind_const, measure_univ, one_smul]

end Turing.MultiTapePTM
