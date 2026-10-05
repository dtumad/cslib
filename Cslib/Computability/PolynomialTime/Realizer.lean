/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Support
public import Cslib.Computability.PolynomialTime.Arithmetic
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Rename
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Cost
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Explicit uniform probabilistic realizers

`Realizer` retains the machine witnessing `IsPPT`. Constructions such as saved-coin execution
and rewinding take this data as an input. The machine and its clock are fixed before the input;
forgetting the data recovers exactly the existing polynomial-time predicate.

The realization law compares the complete result and shared oracle state. It can therefore be
used with an oracle that records its interactions, but does not identify private random tapes
across two executions.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeTM PFunctor MeasureTheory ProbabilityTheory

variable {Oracle α β : Type} [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- One finite machine, with a uniform polynomial clock and joint interaction correctness. -/
structure Realizer (input : α ↪ Word) (output : β ↪ Word)
    (program : α → (effects Oracle).FreeM β) where
  /-- Only finitely many operation names are available. -/
  finiteOracle : Finite Oracle
  /-- Number of work tapes. -/
  tapes : ℕ
  /-- Number of communication ports. -/
  ports : ℕ
  /-- The fixed control type. -/
  State : Type
  /-- The control does not grow with the input. -/
  finiteState : Finite State
  /-- The implementing machine. -/
  machine : MultiTapePTM tapes Bool State (Fin ports)
  /-- Different ports may use the same operation and its shared state. -/
  dispatch : Fin ports → Oracle
  /-- Coefficient of the transition bound. -/
  coefficient : ℕ
  /-- Degree of the transition bound. -/
  degree : ℕ
  /-- Every response and coin path halts within the clock. -/
  halts (a : α) : machine.HaltsWithin (coefficient * ((input a).length + 1) ^ degree)
    (machine.initialConfig (input a))
  /-- Correctness retains both the encoded result and the shared oracle state. -/
  realizes (a : α) : machine.Realizes dispatch
    (coefficient * ((input a).length + 1) ^ degree) (input a) output (program a)

variable {input : α ↪ Word} {output : β ↪ Word} {program : α → (effects Oracle).FreeM β}

/-- Forget the chosen implementation, retaining its uniform efficiency certificate. -/
theorem Realizer.isPPT (implementation : Realizer input output program) :
    IsPPT input output program :=
  ⟨implementation.finiteOracle, implementation.tapes, implementation.ports,
    implementation.State, implementation.finiteState, implementation.machine,
    implementation.dispatch, implementation.coefficient, implementation.degree,
    fun a => ⟨implementation.halts a, implementation.realizes a⟩⟩

/-- Retaining an implementation adds data but no new efficiency assumption. -/
theorem isPPT_iff_nonempty_realizer :
    IsPPT input output program ↔ Nonempty (Realizer input output program) := by
  constructor
  · rintro ⟨hf, k, ports, State, hs, machine, dispatch, c, d, h⟩
    exact ⟨⟨hf, k, ports, State, hs, machine, dispatch, c, d,
      fun a => (h a).1, fun a => (h a).2⟩⟩
  · rintro ⟨implementation⟩
    exact implementation.isPPT

namespace Realizer

variable (implementation : Realizer input output program)

/-- Transition budget as a function of encoded input length. -/
def clock (length : ℕ) : ℕ := implementation.coefficient * (length + 1) ^ implementation.degree

theorem polynomiallyBounded_clock : Cslib.PolynomiallyBounded implementation.clock := by
  unfold clock
  fun_prop

/-- Computing the unary transition budget has one uniform polynomial-time machine. -/
theorem isPolyTime_clock : IsPolyTime unaryEncoding
    (fun length => unaryEncoding (implementation.clock length)) :=
  (isPolyTime_const unaryEncoding (unaryEncoding implementation.coefficient)).unary_mul
    (((isPolyTime_input unaryEncoding).unary_add (g := fun _ => 1)
      (isPolyTime_const unaryEncoding [true])).unary_pow implementation.degree)

/-- The same clock is monotone in the input length. -/
theorem clock_mono : Monotone implementation.clock := by
  intro a b hab
  dsimp only [clock]
  gcongr

/-- Execute the chosen machine, translating its ports to the original operation names. -/
def run (a : α) : (effects Oracle).FreeM (Option Word) :=
  (implementation.machine.run (implementation.clock (input a).length) (input a)).liftM
    (rename implementation.dispatch)

/-- Executing the witness preserves the program's complete result-and-state measure. -/
theorem runKernel_run (a : α) {S : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S] (oracle : Oracle → Word → Kernel S (Word × S)) (state : S) :
    FreeM.runKernel (effectKernel oracle) (implementation.run a) state =
      FreeM.runKernel (effectKernel oracle) ((fun value => some (output value)) <$> program a)
        state := by
  rw [run, runKernel_liftM_rename]
  exact implementation.realizes a S oracle state

/-- A witness never times out, and its returned words are exactly the reachable result codes. -/
theorem canReturn_run_iff (a : α) (result : Option Word) :
    MonadAttach.CanReturn (implementation.run a) result ↔
      ∃ value, MonadAttach.CanReturn (program a) value ∧ some (output value) = result := by
  rw [run, canReturn_liftM_rename]
  cases result with
  | none =>
    constructor
    · intro h
      obtain ⟨final, hfinal, hout⟩ := (FreeM.canReturn_map _ _ _).mp h
      have hhalt := implementation.halts a final hfinal
      simp [output?, hhalt] at hout
    · rintro ⟨_, _, h⟩
      cases h
  | some word =>
    simpa only [clock, Option.some.injEq] using (implementation.realizes a).canReturn_iff

/-- Every reachable result fits within the same clock used to implement the program. -/
theorem length_le (a : α) (value : β) (hvalue : MonadAttach.CanReturn (program a) value) :
    (output value).length ≤ implementation.clock (input a).length :=
  length_of_canReturn_run implementation.machine _ _ _
    ((implementation.realizes a).canReturn_iff.mpr ⟨value, hvalue, rfl⟩)

/-- Any selected family of oracle requests inherits the implementation's transition clock.
This is a bound on the chosen machine program; private coin placement is not identified with
the original program's syntax. -/
theorem queryBoundP_run_le (a : α) (select : (effects Oracle).A → Bool)
    (hcoin : select (.inl ()) = false) :
    FreeM.queryBoundP select (implementation.run a) ≤ implementation.clock (input a).length := by
  let selected : (effects (Fin implementation.ports)).A → Bool
    | .inl _ => select (.inl ())
    | .inr (port, word) => select (.inr (implementation.dispatch port, word))
  refine le_trans (FreeM.queryBoundP_liftM_le selected select (rename implementation.dispatch) ?_
    (implementation.machine.run (implementation.clock (input a).length) (input a))) ?_
  · intro op
    cases op with
    | inl token =>
      cases token
      simp only [rename, coin, FreeM.queryBoundP_lift (P := effects Oracle), selected]
      exact le_rfl
    | inr request =>
      rcases request with ⟨port, word⟩
      simp only [rename, query, FreeM.queryBoundP_lift (P := effects Oracle), selected]
      exact le_rfl
  · exact Turing.MultiTapePTM.queryBoundP_run_le implementation.machine selected hcoin _ _

/-- Structural specifications transfer to every completed path of this implementation. -/
theorem postcondition (a : α) {post : β → Prop}
    (hpost : ∀ value, MonadAttach.CanReturn (program a) value → post value)
    {word : Word} (hword : MonadAttach.CanReturn
      (implementation.machine.run (implementation.clock (input a).length) (input a))
        (some word)) : ∃ value, output value = word ∧ post value := by
  obtain ⟨value, hvalue, hencode⟩ := (implementation.realizes a).canReturn hword
  exact ⟨value, hencode, hpost value hvalue⟩

end Realizer

/-- Uniform probabilistic time bounds the encoding of every reachable output. -/
theorem IsPPT.length_le (h : IsPPT input output program) :
    ∃ c d : ℕ, ∀ a value, MonadAttach.CanReturn (program a) value →
      (output value).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨implementation⟩ := isPPT_iff_nonempty_realizer.mp h
  exact ⟨implementation.coefficient, implementation.degree, implementation.length_le⟩

end Turing.MultiTapePTM
