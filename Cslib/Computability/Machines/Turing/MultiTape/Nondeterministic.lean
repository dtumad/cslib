/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan, Samuel Schlesinger
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.RelSeries
public import Cslib.Computability.Machines.Turing.MultiTape.Machine

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. The
computation predicates ask for a path ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/--
A nondeterministic multi-tape Turing machine with `k` work tapes over the alphabet of
`Option Symbol` (where `none` is the blank symbol). Neither `Symbol` nor `State` is required to be
finite. This is the common machine core with an empty oracle-operation type and relational choice.
-/
abbrev MultiTapeNTM (k : ℕ) (Symbol State : Type*) :=
  MultiTapeMachine k Symbol State Empty Set

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- Construct an oracle-free nondeterministic machine from an ordinary transition relation. -/
def mk (q₀ : State) (Tr : State → Option Symbol → (Fin k → Option Symbol) →
    Action k Symbol State → Prop) : MultiTapeNTM k Symbol State where
  initial := q₀
  tr q symbol work _ action :=
    Tr q symbol work (MultiTapeMachine.emptyActionEquiv k Symbol State action)

/-- The initial state, in the ordinary NTM interface. -/
def q₀ (ntm : MultiTapeNTM k Symbol State) : State := ntm.initial

/-- The permitted ordinary actions. Empty oracle observations carry no additional information. -/
def Tr (ntm : MultiTapeNTM k Symbol State) (q : State) (symbol : Option Symbol)
    (work : Fin k → Option Symbol) (action : Action k Symbol State) : Prop :=
  ntm.tr q symbol work Empty.elim
    ((MultiTapeMachine.emptyActionEquiv k Symbol State).symm action)

@[simp] theorem tr_mk (q₀ q : State) (Tr : State → Option Symbol → (Fin k → Option Symbol) →
    Action k Symbol State → Prop) (symbol : Option Symbol) (work : Fin k → Option Symbol)
    (action : Action k Symbol State) :
    (mk q₀ Tr).Tr q symbol work action ↔ Tr q symbol work action := Iff.rfl

/-- The ordinary NTM interface describes every machine in the empty-oracle specialization. -/
theorem mk_q₀_Tr (ntm : MultiTapeNTM k Symbol State) : mk ntm.q₀ ntm.Tr = ntm := by
  cases ntm with
  | mk initial tr =>
    simp only [mk, q₀, Tr, Equiv.symm_apply_apply]
    congr 1
    funext q symbol work answer
    have hanswer : answer = Empty.elim := funext fun oracle => oracle.elim
    rw [hanswer]

/-- The one-step relation on configurations. A halted configuration steps to itself; a running one
steps by any permitted transition. -/
@[scoped grind =]
def Step (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => c₂ = c₁
  | some q =>
    ∃ action, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A finite nonempty list of configurations joined by steps of `ntm`. -/
abbrev RunPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :=
  RelSeries {(c, c') | ntm.Step (input := input) c c'}

namespace RunPath

/-- The number of steps taken by a run path. -/
def time (p : ntm.RunPath input) : ℕ := p.length

/-- The set of positions visited by the head of work tape `i` along a run path. -/
def visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n => (p n).workTapePos i

/-- The number of cells touched by the head of work tape `i` along a run path. -/
def spaceUsedByTape (p : ntm.RunPath input) (i : Fin k) : ℕ :=
  (p.visitedByTapeHead i).card

/-- The number of work tape cells touched along a run path. -/
def space (p : ntm.RunPath input) : ℕ := ∑ i, p.spaceUsedByTape i

end RunPath

/-- A run path starting at the initial configuration for `input`. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    extends toRunPath : ntm.RunPath input where
  /-- the path starts at the initial configuration -/
  head_eq : toRunPath.head = ntm.initCfg input

namespace ComputationPath

/-- The number of steps taken by a computation path. -/
def time (p : ntm.ComputationPath input) : ℕ := RunPath.time p.toRunPath

/-- The number of work tape cells touched along a computation path. -/
def space (p : ntm.ComputationPath input) : ℕ := RunPath.space p.toRunPath

end ComputationPath

/-- `ntm` has a computation on `input` that starts at the initial configuration, halts, emits
`output` and satisfies `P`. The notions below are its instances, so their constraints all refer to
a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.ComputationPath input → Prop) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = output ∧ P p

/-- `ntm` computes `output` from `input`, with no bound on resources. -/
def Computes (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) : Prop :=
  ntm.ComputesSuchThat input output fun _ => True

/-- `ntm` computes `output` from `input` in exactly `t` steps. -/
def ComputesInExactTime (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (t : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInExactSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. Nondeterministic analogue of `MultiTapeTM.ComputesInTimeAndSpace`. -/
def ComputesInExactTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t ∧ p.space = s

end MultiTapeNTM

end Turing
