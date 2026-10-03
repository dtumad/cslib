/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Postprocessing
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Rename
public import Cslib.Computability.Machines.Turing.MultiTape.Relabel

/-!
# Uniform probabilistic polynomial time

`IsPPTOn`, `IsPPT`, and `IsOraclePPT` identify a program's distribution with that of a single
finite-control machine, clocked by `c * (input.length + 1) ^ d`. The machine, `c` and `d` are fixed
before quantifying over encoded inputs. The cryptographic predicates supply the security parameter
in unary, with a delimiter. Neither nonuniform advice nor arbitrary Lean computation is free.

For oracle programs the equality includes the oracle's final private state, for every stateful
oracle. This preserves observable interactions, rather than testing only against stateless
functions. Oracle computation is external; queries are written and answers are read bit by bit.

The definition uses strict polynomial clocks on every execution, not expected polynomial time.
The high-level language can express arbitrary distributions, but efficiency requires realization
using fair bits by the machine model. Output encodings are injective.
In particular, exact uniform sampling from a three-element set need not have a strict fair-coin
PPT realization; bounded rejection sampling with explicit failure is a different program.

`IsPolyTime` supplies deterministic polynomial-time realizability using the existing `MultiTapeTM`.
Its parameterized implementations embed into PPT with the same clock. Fixed Boolean
postprocessing also preserves PPT through an explicit machine construction. Certificates may use
any finite control type; an enumeration by `Fin` is supplied internally. The PPT predicates bound
the length of every supported output, including in the presence of arbitrary oracle states.
`IsPPTOn` exposes the input encoding for typed program composition; `IsPPT` specializes it to the
usual unary security parameter and auxiliary input, via `isPPT_iff_on`.
`Cslib.Computability.Probabilistic.Oracle` gives the multi-operation `IsOraclePPTOn` contract and
its proved equivalence with the single-operation `IsOraclePPT` specialization. Typed request and
reply representations are certified in `Cslib.Computability.Probabilistic.OracleEncoding`.

These are semantic predicates; this module does not supply an automatic compiler or closure
theorems for arbitrary high-level compositions. Uniform bit sampling is certified separately in
`Cslib.Computability.Probabilistic.Sampling`, and fixed word substitutions in
`Cslib.Computability.Probabilistic.Output`. The clock compiler in
`Cslib.Computability.Probabilistic.Clock` proves that every PPT certificate admits a genuinely
halting witness, including when its original machine terminates only through clock exhaustion.
`Cslib.Computability.Probabilistic.Composition` certifies typed sequencing, captured inputs,
deterministic argument preparation, and conditional execution of closed programs.
-/

@[expose] public section

namespace Cslib

namespace Probability

/-- Binary words used at the machine boundary. -/
abbrev Word := List Bool

/-- Unary security parameter, a zero delimiter, then the auxiliary input. -/
def parameterInput (security : ℕ) (input : Word) : Word :=
  List.replicate security true ++ false :: input

@[simp] theorem length_parameterInput (security : ℕ) (input : Word) :
    (parameterInput security input).length = security + input.length + 1 := by
  simp [parameterInput, Nat.add_assoc]

/-- The delimiter makes both the security parameter and auxiliary input recoverable. -/
@[simp] theorem parameterInput_inj {n m : ℕ} {input input' : Word} :
    parameterInput n input = parameterInput m input' ↔ n = m ∧ input = input' := by
  induction n generalizing m with
  | zero => cases m <;> simp [parameterInput, List.replicate_succ]
  | succ n ih =>
    cases m with
    | zero => simp [parameterInput, List.replicate_succ]
    | succ m => simpa [parameterInput, List.replicate_succ] using (ih (m := m))

/-- The identity encoding of binary words. -/
def wordEncoding : Word ↪ Word := Function.Embedding.refl _

/-- The machine input encoding for an algorithm with a security parameter and auxiliary input. -/
def parameterEncoding : (ℕ × Word) ↪ Word where
  toFun pair := parameterInput pair.1 pair.2
  inj' := by
    rintro ⟨n, input⟩ ⟨m, input'⟩ h
    obtain ⟨rfl, rfl⟩ := parameterInput_inj.mp h
    rfl

@[simp] theorem parameterEncoding_apply (input : ℕ × Word) :
    parameterEncoding input = parameterInput input.1 input.2 := rfl

/-- A Boolean is represented by its single bit. -/
def boolEncoding : Bool ↪ Word := ⟨fun b => [b], by intro a b h; simpa using h⟩

/-- A uniform deterministic machine computes `f` from an explicit binary encoding, with a
polynomial bound on every input. The finite control and polynomial are independent of the input. -/
def IsPolyTime {α : Type} (encode : α → Word) (f : α → Word) : Prop :=
  ∃ (k states : ℕ) (machine : Turing.MultiTapeTM k Bool (Fin states)) (c d : ℕ),
    ∀ a, let cfg := machine.runFrom (machine.initCfg (encode a)) (c * ((encode a).length + 1) ^ d)
      cfg.state = none ∧ cfg.output = f a

/-- A deterministic certificate may use any finite control type. Relabelling supplies the
canonical `Fin` presentation without changing execution time or output. -/
theorem isPolyTime_of_finite_machine {α State : Type} [Finite State] {k : ℕ}
    {encode : α → Word} {f : α → Word} (machine : Turing.MultiTapeTM k Bool State) (c d : ℕ)
    (h : ∀ a,
      let cfg := machine.runFrom (machine.initCfg (encode a))
        (c * ((encode a).length + 1) ^ d)
      cfg.state = none ∧ cfg.output = f a) : IsPolyTime encode f := by
  classical
  let := Fintype.ofFinite State
  refine ⟨k, Fintype.card State, machine.relabel (Fintype.equivFin State), c, d, ?_⟩
  intro a
  simp only [Turing.MultiTapeTM.initCfg_relabel, Turing.MultiTapeTM.runFrom_relabel,
    Turing.Cfg.relabel_state, Turing.Cfg.relabel_output]
  exact ⟨congrArg (Option.map (Fintype.equivFin State)) (h a).1, (h a).2⟩

/-- Polynomial time also bounds the size of an explicitly written output. -/
theorem IsPolyTime.length_le {α : Type} {encode : α → Word} {f : α → Word}
    (h : IsPolyTime encode f) : ∃ c d : ℕ, ∀ a, (f a).length ≤ c * ((encode a).length + 1) ^ d := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  have hout := machine.length_output_runFrom_le (machine.initCfg (encode a))
    (c * ((encode a).length + 1) ^ d)
  rw [(h a).2] at hout
  simpa using hout

/-- A uniform probabilistic polynomial-time realization on explicitly encoded inputs and results.
The finite machine and polynomial are fixed before quantifying over the input. -/
def IsPPTOn {α β : Type} (input : α → Word) (output : β ↪ Word)
    (program : α → ProbComp β) : Prop :=
  ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
    ∀ a, (ProbComp.eval (program a)).map output =
      OracleComp.eval (fun _ => PMF.pure [])
        (machine.run (c * ((input a).length + 1) ^ d) (input a))

/-- A uniform PPT realization of a family of closed probabilistic programs. Supplying only an
empty-answer oracle to the machine provides no external computational power. -/
def IsPPT {α : Type} (encode : α ↪ Word) (program : ℕ → Word → ProbComp α) : Prop :=
  IsPPTOn parameterEncoding encode (fun pair => program pair.1 pair.2)

/-- The cryptographic interface is the encoded-input contract with a unary security parameter. -/
theorem isPPT_iff_on {α : Type} {encode : α ↪ Word} {program : ℕ → Word → ProbComp α} :
    IsPPT encode program ↔
      IsPPTOn parameterEncoding encode (fun pair => program pair.1 pair.2) := Iff.rfl

/-- Expose the input encoding of a cryptographic PPT certificate. -/
theorem IsPPT.on {α : Type} {encode : α ↪ Word} {program : ℕ → Word → ProbComp α}
    (h : IsPPT encode program) :
    IsPPTOn parameterEncoding encode (fun pair => program pair.1 pair.2) := isPPT_iff_on.mp h

/-- Return to the cryptographic interface after certifying an encoded-input program. -/
theorem IsPPTOn.isPPT {α : Type} {encode : α ↪ Word} {program : ℕ → Word → ProbComp α}
    (h : IsPPTOn parameterEncoding encode (fun pair => program pair.1 pair.2)) :
    IsPPT encode program := isPPT_iff_on.mpr h

/-- Returning a value with its declared encoding is the same machine-level contract. -/
theorem isPPTOn_iff_encoded {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} : IsPPTOn input output program ↔
      IsPPTOn input wordEncoding (fun a => output <$> program a) := by
  simp only [IsPPTOn, ProbComp.eval_map, show (wordEncoding : Word → Word) = id from rfl,
    PMF.map_id]

/-- View a typed result as its encoded word without changing the implementation. -/
theorem IsPPTOn.encoded {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    IsPPTOn input wordEncoding (fun a => output <$> program a) := isPPTOn_iff_encoded.mp h

/-- A certificate for a program's declared encoding certifies the typed program itself. -/
theorem IsPPTOn.of_encoded {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β}
    (h : IsPPTOn input wordEncoding (fun a => output <$> program a)) :
    IsPPTOn input output program := isPPTOn_iff_encoded.mpr h

/-- A uniform PPT realization that preserves the distribution of the result and final oracle
state for every stateful oracle. The same machine and polynomial work for every oracle. -/
def IsOraclePPT {α : Type} (encode : α ↪ Word)
    (program : ℕ → Word → OracleComp Word (fun _ => Word) α) : Prop :=
  ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
    ∀ security input (State : Type) (oracle : Word → StateT State PMF Word) (s : State),
      OracleComp.runState oracle (encode <$> program security input) s =
        OracleComp.runState oracle
          (machine.run (c * ((parameterInput security input).length + 1) ^ d)
            (parameterInput security input)) s

/-- A typed certificate may use any finite control type; its enumeration is internal. -/
theorem isPPTOn_of_finite_machine {α β State : Type} [Finite State] {k : ℕ}
    {input : α → Word} {output : β ↪ Word} {program : α → ProbComp β}
    (machine : Turing.OracleTM k State) (c d : ℕ)
    (h : ∀ a, (ProbComp.eval (program a)).map output =
      OracleComp.eval (fun _ => PMF.pure [])
        (machine.run (c * ((input a).length + 1) ^ d) (input a))) :
    IsPPTOn input output program := by
  classical
  let := Fintype.ofFinite State
  refine ⟨k, Fintype.card State, machine.rename (Fintype.equivFin State), c, d, ?_⟩
  simpa only [Turing.OracleTM.run_rename] using h

/-- A certificate may use any finite control type; its enumeration is internal to the proof. -/
theorem isPPT_of_finite_machine {α State : Type} [Finite State] {k : ℕ}
    {encode : α ↪ Word} {program : ℕ → Word → ProbComp α}
    (machine : Turing.OracleTM k State) (c d : ℕ)
    (h : ∀ n input, (ProbComp.eval (program n input)).map encode =
      OracleComp.eval (fun _ => PMF.pure [])
        (machine.run (c * ((parameterInput n input).length + 1) ^ d)
          (parameterInput n input))) :
    IsPPT encode program := by
  exact (isPPTOn_of_finite_machine machine c d (fun pair => h pair.1 pair.2)).isPPT

/-- The same finite-control interface preserves every stateful oracle interaction. -/
theorem isOraclePPT_of_finite_machine {α State : Type} [Finite State] {k : ℕ}
    {encode : α ↪ Word} {program : ℕ → Word → OracleComp Word (fun _ => Word) α}
    (machine : Turing.OracleTM k State) (c d : ℕ)
    (h : ∀ n input (OracleState : Type) (oracle : Word → StateT OracleState PMF Word) s,
      OracleComp.runState oracle (encode <$> program n input) s =
        OracleComp.runState oracle
          (machine.run (c * ((parameterInput n input).length + 1) ^ d)
            (parameterInput n input)) s) :
    IsOraclePPT encode program := by
  classical
  let := Fintype.ofFinite State
  refine ⟨k, Fintype.card State, machine.rename (Fintype.equivFin State), c, d, ?_⟩
  simpa only [Turing.OracleTM.run_rename] using h

/-- A deterministic contract gives a probabilistic contract on the same encoded types. -/
theorem IsPolyTime.isPPTOn {α β : Type} {input : α → Word} {output : β ↪ Word} {f : α → β}
    (h : IsPolyTime input (fun a => output (f a))) :
    IsPPTOn input output (fun a => pure (f a)) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨k, states, Turing.OracleTM.ofDeterministic machine, c, d, ?_⟩
  intro a
  simp only [ProbComp.eval_pure, PMF.pure_map, Turing.OracleTM.run,
    Turing.OracleTM.eval_ofDeterministic]
  exact congrArg PMF.pure (h a).2.symm

/-- A deterministic polynomial-time implementation of a parameterized algorithm is PPT.
The hypothesis uses the same explicit input and output encodings as the conclusion. -/
theorem IsPolyTime.isPPT {α : Type} {encode : α ↪ Word} {f : ℕ → Word → α}
    (h : IsPolyTime parameterEncoding (fun pair => encode (f pair.1 pair.2))) :
    IsPPT encode (fun n input => pure (f n input)) := h.isPPTOn.isPPT

/-- The same embedding works in an oracle context and preserves every oracle's private state. -/
theorem IsPolyTime.isOraclePPT {α : Type} {encode : α ↪ Word} {f : ℕ → Word → α}
    (h : IsPolyTime parameterEncoding (fun pair => encode (f pair.1 pair.2))) :
    IsOraclePPT encode (fun n input => pure (f n input)) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨k, states, Turing.OracleTM.ofDeterministic machine, c, d, ?_⟩
  intro n input State oracle s
  simp only [map_pure, OracleComp.runState_pure, Turing.OracleTM.run,
    Turing.OracleTM.runState_ofDeterministic]
  exact congrArg (fun word => PMF.pure (word, s)) (h (n, input)).2.symm

/-- A typed PPT contract bounds the encoded length of every supported result. -/
theorem IsPPTOn.length_le {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ c d : ℕ, ∀ a result, result ∈ (ProbComp.eval (program a)).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, ?_⟩
  intro a result hresult
  have hmap := (PMF.mem_support_map_iff output (ProbComp.eval (program a))
    (output result)).mpr ⟨result, hresult, rfl⟩
  rw [h a] at hmap
  simpa [Turing.OracleTM.initialConfig] using
    Turing.OracleTM.length_output_eval_runFrom_le machine _ _ _ _ hmap

/-- Every supported PPT output has polynomially bounded encoded length. -/
theorem IsPPT.length_le {α : Type} {encode : α ↪ Word} {program : ℕ → Word → ProbComp α}
    (h : IsPPT encode program) :
    ∃ c d : ℕ, ∀ n input result, result ∈ (ProbComp.eval (program n input)).support →
      (encode result).length ≤ c * (n + input.length + 2) ^ d := by
  obtain ⟨c, d, hbound⟩ := h.on.length_le
  exact ⟨c, d, fun n input result hr => by
    simpa [parameterEncoding, Nat.add_assoc] using hbound (n, input) result hr⟩

/-- Oracle PPT has an output-size bound independent of the oracle and its private state. -/
theorem IsOraclePPT.length_le {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α} (h : IsOraclePPT encode program) :
    ∃ c d : ℕ, ∀ n input (State : Type) (oracle : Word → StateT State PMF Word) s s' result,
      (result, s') ∈ (OracleComp.runState oracle (program n input) s).support →
      (encode result).length ≤ c * (n + input.length + 2) ^ d := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, ?_⟩
  intro n input State oracle s s' result hresult
  have hmap : (encode result, s') ∈
      (OracleComp.runState oracle (encode <$> program n input) s).support := by
    rw [OracleComp.runState_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [h n input State oracle s] at hmap
  simpa [Turing.OracleTM.initialConfig, Nat.add_assoc] using
    Turing.OracleTM.length_output_runFrom_le machine oracle _ _ s s' _ hmap

/-- Distributional equality preserves a typed PPT contract. -/
theorem IsPPTOn.congr {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program program' : α → ProbComp β} (h : IsPPTOn input output program)
    (heq : ∀ a, ProbComp.eval (program a) = ProbComp.eval (program' a)) :
    IsPPTOn input output program' := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  exact ⟨k, states, machine, c, d, fun a =>
    (congrArg (PMF.map output) (heq a)).symm.trans (h a)⟩

/-- Distributional equality preserves PPT realizability. -/
theorem IsPPT.congr {α : Type} {encode : α ↪ Word} {program program' : ℕ → Word → ProbComp α}
    (h : IsPPT encode program)
    (heq : ∀ n x, ProbComp.eval (program n x) = ProbComp.eval (program' n x)) :
    IsPPT encode program' := (h.on.congr (fun pair => heq pair.1 pair.2)).isPPT

/-- Any fixed postprocessing of a Boolean answer is PPT, including complementing the answer.
This is a machine construction with the same clock, not a closure assumption. -/
theorem IsPPT.map_bool {program : ℕ → Word → ProbComp Bool}
    (h : IsPPT boolEncoding program) (f : Bool → Bool) :
    IsPPT boolEncoding (fun n input => f <$> program n input) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨k, states, machine.mapOutput f, c, d, ?_⟩
  intro pair
  rw [Turing.OracleTM.run_mapOutput, OracleComp.eval_map, ← h pair]
  simp [ProbComp.eval_map, PMF.map_comp, Function.comp_def, boolEncoding]

/-- Boolean postprocessing preserves oracle PPT and the final state of every oracle. -/
theorem IsOraclePPT.map_bool {program : ℕ → Word → OracleComp Word (fun _ => Word) Bool}
    (h : IsOraclePPT boolEncoding program) (f : Bool → Bool) :
    IsOraclePPT boolEncoding (fun n input => f <$> program n input) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨k, states, machine.mapOutput f, c, d, ?_⟩
  intro n input State oracle s
  rw [Turing.OracleTM.run_mapOutput]
  simp only [OracleComp.runState_map]
  have hh := h n input State oracle s
  rw [OracleComp.runState_map] at hh
  rw [← hh]
  simp [PMF.map_comp, Function.comp_def, boolEncoding]

/-- Every fixed finite-control oracle machine with a polynomial clock is an oracle PPT program. -/
theorem isOraclePPT_run {k states : ℕ} (machine : Turing.OracleTM k (Fin states)) (c d : ℕ) :
    IsOraclePPT wordEncoding (fun n x =>
      machine.run (c * ((parameterInput n x).length + 1) ^ d) (parameterInput n x)) := by
  refine ⟨k, states, machine, c, d, ?_⟩
  intro n x State oracle s
  change OracleComp.runState oracle (id <$> _) s = _
  rw [id_map]

/-- A one-step machine that emits a specified bit and halts. -/
def returnBitMachine (bit : Bool) : Turing.OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ _ _ _ _ => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none } none 0

/-- The empty output has a zero-step PPT realization. -/
theorem isPPT_empty : IsPPT wordEncoding (fun _ _ => pure []) := by
  refine ⟨0, 1, returnBitMachine false, 0, 0, ?_⟩
  intro pair
  simp [Turing.OracleTM.run, Turing.OracleTM.initialConfig,
    wordEncoding, PMF.pure_map]

/-- A constant Boolean program has a one-step PPT realization. -/
theorem isPPT_const_bool (bit : Bool) : IsPPT boolEncoding (fun _ _ => pure bit) := by
  refine ⟨0, 1, returnBitMachine bit, 1, 0, ?_⟩
  intro pair
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig,
    returnBitMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    boolEncoding, PMF.map, Function.comp_def]

end Probability

end Cslib
