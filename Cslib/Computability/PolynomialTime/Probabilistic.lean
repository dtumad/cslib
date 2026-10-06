/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Computability.PolynomialTime.Defs
public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.MeasureTheory.Option
public import Mathlib.Probability.UniformOn

/-!
# Probabilistic polynomial time

Programs over the operations of probabilistic machines, `effects Oracle`, flip fair coins and send
requests to named oracles. An oracle environment (`OracleEnv`) answers requests from a countable
state shared by all oracles, which each answer may update; `env.run x s` is the joint distribution
of the output of `x` and the final state, run from the state `s`.

A machine realizes a program within a transition budget (`Realizes`) if, under every oracle
environment and from every state, its output and final state are distributed as the encoded output
of the program and its final state. A program family is in probabilistic polynomial time (`IsPPT`)
if one finite-control machine, with finitely many oracle ports, realizes it on every input within
`c * (n + 1) ^ d` transitions on inputs of length `n`, halting on every path of coins and answers.
Sending a request takes one transition; the oracles' own work is not counted.

For oracles without state, a realization is an equality of output measures
(`Realizes.toMeasure_eq`).

Adapted from Samuel Schlesinger's probabilistic polynomial time on oracle machines.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

/-- Binary words carry the discrete σ-algebra. -/
instance : MeasurableSpace Word := ⊤

instance : DiscreteMeasurableSpace Word := ⟨fun _ => trivial⟩

end MultiTapeTM

namespace MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory MultiTapeTM

variable {Oracle : Type}

instance (a : (effects Oracle).A) : MeasurableSpace ((effects Oracle).B a) :=
  match a with
  | .inl _ => inferInstanceAs (MeasurableSpace Bool)
  | .inr _ => inferInstanceAs (MeasurableSpace Word)

instance (a : (effects Oracle).A) : DiscreteMeasurableSpace ((effects Oracle).B a) := by
  cases a with
  | inl _ => exact inferInstanceAs (DiscreteMeasurableSpace Bool)
  | inr _ => exact inferInstanceAs (DiscreteMeasurableSpace Word)

instance (a : (effects Oracle).A) : Countable ((effects Oracle).B a) := by
  cases a with
  | inl _ => exact inferInstanceAs (Countable Bool)
  | inr _ => exact inferInstanceAs (Countable Word)

/-- Named oracles answering from a countable discrete state that they share and may update. -/
structure OracleEnv (Oracle : Type) where
  /-- The shared state of the oracles. -/
  State : Type
  [countable : Countable State]
  [measurableSpace : MeasurableSpace State]
  [discreteMeasurableSpace : DiscreteMeasurableSpace State]
  /-- The distribution of an oracle's answer to a request, together with the updated state. -/
  answer : Oracle → Word → State → Measure (Word × State)

namespace OracleEnv

attribute [instance] countable measurableSpace discreteMeasurableSpace

variable (env : OracleEnv Oracle)

/-- The same oracles, called through the names `dispatch`. -/
abbrev comap {Ports : Type} (dispatch : Ports → Oracle) : OracleEnv Ports where
  State := env.State
  answer port := env.answer (dispatch port)

/-- Answer coins fairly, leaving the state unchanged, and requests by the oracles. -/
noncomputable def sem : (a : ((effects Oracle).withState env.State).A) →
    Measure (((effects Oracle).withState env.State).B a)
  | (.inl (), s) => (uniformOn Set.univ : Measure Bool).map (·, s)
  | (.inr (oracle, word), s) => env.answer oracle word s

/-- The joint distribution of the output of `x` and the final state, run from the state `s`. -/
noncomputable def run {α : Type} [MeasurableSpace α] (x : (effects Oracle).FreeM α)
    (s : env.State) : Measure (α × env.State) :=
  (x.withState s).toMeasure env.sem

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

@[simp]
theorem run_pure (a : α) (s : env.State) : env.run (pure a) s = .dirac (a, s) := rfl

@[simp]
theorem run_coin (s : env.State) :
    env.run coin s = (uniformOn Set.univ : Measure Bool).map (·, s) :=
  FreeM.toMeasure_lift _ _

@[simp]
theorem run_query (oracle : Oracle) (word : Word) (s : env.State) :
    env.run (query oracle word) s = env.answer oracle word s :=
  FreeM.toMeasure_lift _ _

variable [Countable α] [MeasurableSingletonClass α]

@[simp]
theorem run_bind (x : (effects Oracle).FreeM α) (f : α → (effects Oracle).FreeM β)
    (s : env.State) : env.run (x >>= f) s = (env.run x s).bind fun p => env.run (f p.1) p.2 := by
  simp [run]

@[simp]
theorem run_map (f : α → β) (x : (effects Oracle).FreeM α) (s : env.State) :
    env.run (f <$> x) s = (env.run x s).map (Prod.map f id) := by
  simp [run]

/-- The oracles answering each request to `oracle` by `answer oracle`, keeping no state. -/
noncomputable abbrev ofStateless (answer : Oracle → Word → Measure Word) : OracleEnv Oracle where
  State := Unit
  answer oracle word _ := (answer oracle word).map (·, ())

/-- Fair coins, and requests to `oracle` answered by `answer oracle`. -/
noncomputable def statelessMeasure (answer : Oracle → Word → Measure Word) :
    (a : (effects Oracle).A) → Measure ((effects Oracle).B a)
  | .inl () => uniformOn Set.univ
  | .inr (oracle, word) => answer oracle word

omit [Countable α] [MeasurableSingletonClass α] in
theorem run_ofStateless (answer : Oracle → Word → Measure Word) (x : (effects Oracle).FreeM α)
    (s : Unit) :
    (ofStateless answer).run x s = (x.toMeasure (statelessMeasure answer)).map (·, s) :=
  FreeM.toMeasure_withState _ (fun a _ => by rcases a with _ | ⟨_, _⟩ <;> rfl) x s

/-- Fair coins, for programs without oracles. -/
noncomputable abbrev fairCoins [IsEmpty Oracle] :
    (a : (effects Oracle).A) → Measure ((effects Oracle).B a) :=
  statelessMeasure fun oracle => isEmptyElim oracle

omit [Countable α] [MeasurableSingletonClass α] in
/-- Without oracles, running a program flips fair coins and leaves the state unchanged. -/
theorem run_of_isEmpty [IsEmpty Oracle] (x : (effects Oracle).FreeM α) (s : env.State) :
    env.run x s = (x.toMeasure fairCoins).map (·, s) :=
  FreeM.toMeasure_withState _ (fun a _ => by
    rcases a with _ | ⟨oracle, _⟩
    · rfl
    · exact isEmptyElim oracle) x s

end OracleEnv

/-- `machine`, calling the oracle `dispatch p` through each port `p`, realizes `program` on `input`
within `fuel` transitions: under every oracle environment and from every state, its output and final
state are distributed as the encoded output of `program` and its final state. -/
def Realizes {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
    (machine : MultiTapePTM k Bool State Ports) (dispatch : Ports → Oracle) (fuel : ℕ)
    (input : Word) (encode : α ↪ Word) (program : (effects Oracle).FreeM α) : Prop :=
  ∀ (env : OracleEnv Oracle) (s : env.State),
    (env.comap dispatch).run (machine.run fuel input) s =
      env.run ((fun a => some (encode a)) <$> program) s

/-- One finite-control machine with finitely many oracle ports realizes `program a` on the encoding
`input a`, halting on every path within `c * (n + 1) ^ d` transitions, where `n` is its length. -/
def IsPPT {α β : Type} (input : α ↪ Word) (output : β ↪ Word)
    (program : α → (effects Oracle).FreeM β) : Prop :=
  Finite Oracle ∧ ∃ (k ports : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State (Fin ports)) (dispatch : Fin ports → Oracle) (c d : ℕ),
    ∀ a,
      machine.HaltsWithin (c * ((input a).length + 1) ^ d) (machine.initialConfig (input a)) ∧
      machine.Realizes dispatch (c * ((input a).length + 1) ^ d) (input a) output (program a)

variable {k : ℕ} {State Ports α : Type} [DecidableEq Ports]
  {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle} {fuel : ℕ}
  {input : Word} {encode : α ↪ Word} {program : (effects Oracle).FreeM α}

/-- Once every path halts, a larger budget realizes the same program. -/
theorem Realizes.mono (h : machine.Realizes dispatch fuel input encode program)
    (hhalt : machine.HaltsWithin fuel (machine.initialConfig input)) {fuel' : ℕ}
    (hle : fuel ≤ fuel') : machine.Realizes dispatch fuel' input encode program := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  intro env s
  simpa only [run, runFrom, hhalt.runConfigFrom_add] using h env s

/-- A program that runs like a polynomial-time one is polynomial-time. -/
theorem IsPPT.congr {β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {first second : α → (effects Oracle).FreeM β} (hfirst : IsPPT input output first)
    (h : ∀ a (env : OracleEnv Oracle) s,
      env.run ((fun b => some (output b)) <$> first a) s =
        env.run ((fun b => some (output b)) <$> second a) s) :
    IsPPT input output second := by
  obtain ⟨hf, k, ports, State, hs, machine, dispatch, c, d, hm⟩ := hfirst
  exact ⟨hf, k, ports, State, hs, machine, dispatch, c, d,
    fun a => ⟨(hm a).1, fun env s => ((hm a).2 env s).trans (h a env s)⟩⟩

/-- With oracles that keep no state, a realization is an equality of output measures. -/
theorem Realizes.toMeasure_eq (h : machine.Realizes dispatch fuel input encode program)
    (answer : Oracle → Word → Measure Word) :
    (machine.run fuel input).toMeasure (OracleEnv.statelessMeasure (answer ∘ dispatch)) =
      ((fun a => some (encode a)) <$> program).toMeasure (OracleEnv.statelessMeasure answer) := by
  have h' := h (.ofStateless answer) ()
  change (OracleEnv.ofStateless (answer ∘ dispatch)).run _ () =
    (OracleEnv.ofStateless answer).run _ () at h'
  rw [OracleEnv.run_ofStateless, OracleEnv.run_ofStateless] at h'
  have := congrArg (Measure.map Prod.fst) h'
  rwa [Measure.map_map measurable_fst measurable_prodMk_right,
    Measure.map_map measurable_fst measurable_prodMk_right, Function.comp_def, Function.comp_def,
    Measure.map_id', Measure.map_id'] at this

/-- Without oracles, a machine realizes a program exactly when, with fair coins, its output is
distributed as the encoded output of the program. -/
theorem realizes_iff_toMeasure_eq [IsEmpty Oracle] [IsEmpty Ports] :
    machine.Realizes dispatch fuel input encode program ↔
      (machine.run fuel input).toMeasure OracleEnv.fairCoins =
        ((fun a => some (encode a)) <$> program).toMeasure OracleEnv.fairCoins := by
  refine ⟨fun h => ?_, fun h env s => ?_⟩
  · convert h.toMeasure_eq fun oracle => isEmptyElim oracle using 3
  · rw [OracleEnv.run_of_isEmpty, OracleEnv.run_of_isEmpty, h]

/-- The machine writing one fair coin to its output and halting. -/
def coinMachine : MultiTapePTM 0 Bool Unit (Fin 0) where
  initial := ()
  tr _ _ _ _ bit := .step ⟨0, Fin.elim0, some bit, none⟩ Fin.elim0 Fin.elim0

/-- Flipping a fair coin is in probabilistic polynomial time. -/
theorem isPPT_coin [Finite Oracle] {α : Type} (input : α ↪ Word) :
    IsPPT input boolEncoding fun _ => (coin : (effects Oracle).FreeM Bool) := by
  refine ⟨inferInstance, 0, 0, Unit, inferInstance, coinMachine, Fin.elim0, 1, 0, fun a => ⟨?_, ?_⟩⟩
  · simp [HaltsWithin, runConfigFrom, step, coinMachine, MultiTapeMachine.initialConfig, Cfg.init,
      MultiTapeMachine.Config.step, or_imp, forall_and]
  · intro env s
    simp [run, runFrom, runConfigFrom, step, coinMachine, MultiTapeMachine.initialConfig, Cfg.init,
      MultiTapeMachine.Config.step, output?]

end MultiTapePTM

end Turing
