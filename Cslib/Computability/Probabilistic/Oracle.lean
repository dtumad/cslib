/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT

/-!
# Uniform PPT with several oracle operations

`IsOraclePPTOn` certifies programs with a finite type of operation names and unbounded word
payloads. The witness is the common `MultiTapePTM`. One machine and one polynomial must preserve
the joint distribution of the output and final private state for every stateful handler. All
operations share that state; there is no assumption that they are independent.

This is the encoded-input interface for oracle programs. The existing single-operation
`IsOraclePPT` is equivalent to its unary-parameter specialization, via `isOraclePPT_iff_on`.
Queries are written and answers are read a symbol at a time. The oracle's own computation is
external, including lazy sampling in the random oracle model.
-/

@[expose] public section

namespace Cslib.Probability

/-- Named operations with word requests and replies. The names do not include the payloads. -/
abbrev WordOracleComp (Operation : Type) (α : Type) :=
  OracleComp (Operation × Word) (fun _ => Word) α

/-- An encoded-input oracle program has one finite machine and polynomial clock, valid for
every input and every shared stateful oracle. The finite control type is internal to the witness. -/
def IsOraclePPTOn {Operation α β : Type} [DecidableEq Operation]
    (input : α → Word) (output : β ↪ Word) (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a (State : Type) (oracle : Operation × Word → StateT State PMF Word) (s : State),
      OracleComp.runState oracle (output <$> program a) s =
        OracleComp.runState oracle
          (machine.run (fun op word => OracleComp.query (op, word))
            (c * ((input a).length + 1) ^ d) (input a)) s

namespace IsOraclePPTOn

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α → Word} {output : β ↪ Word}

/-- A fixed finite-control machine with a polynomial clock supplies a certificate directly. -/
theorem of_machine [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsOraclePPTOn input wordEncoding (fun a =>
      machine.run (fun op word => OracleComp.query (op, word))
        (c * ((input a).length + 1) ^ d) (input a)) := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, c, d, ?_⟩
  intro a State oracle s
  change OracleComp.runState oracle (id <$> _) s = _
  rw [id_map]

/-- An oracle PPT certificate includes finiteness of its operation names. -/
theorem finite_operations {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) : Finite Operation := h.1

/-- Equality of the full stateful semantics preserves efficiency. Equality of output marginals
alone is insufficient, because later operations may observe changes to the oracle state. -/
theorem congr {program program' : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program)
    (heq : ∀ a (State : Type) (oracle : Operation × Word → StateT State PMF Word) s,
      OracleComp.runState oracle (program a) s = OracleComp.runState oracle (program' a) s) :
    IsOraclePPTOn input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a State oracle s => ?_⟩
  simpa only [OracleComp.runState_map, heq] using h a State oracle s

/-- Every supported encoded output has polynomial length, independently of all oracle replies. -/
theorem length_le {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a (State : Type) (oracle : Operation × Word → StateT State PMF Word) s s' result,
      (result, s') ∈ (OracleComp.runState oracle (program a) s).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, ?_⟩
  intro a State oracle s s' result hresult
  have hmap : (output result, s') ∈
      (OracleComp.runState oracle (output <$> program a) s).support := by
    rw [OracleComp.runState_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [h a State oracle s] at hmap
  simpa [Turing.MultiTapeMachine.initialConfig] using
    Turing.MultiTapePTM.length_output_runFrom_le machine _ oracle _
      (machine.initialConfig (input a)) s s' _ hmap

/-- Fixed Boolean postprocessing preserves the same clock and every oracle effect. -/
theorem map_bool {program : α → WordOracleComp Operation Bool}
    (h : IsOraclePPTOn input boolEncoding program) (f : Bool → Bool) :
    IsOraclePPTOn input boolEncoding (fun a => f <$> program a) := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine.mapOutput f, c, d, fun a State oracle s => ?_⟩
  rw [Turing.MultiTapePTM.run_mapOutput]
  simp only [OracleComp.runState_map]
  have hh := h a State oracle s
  rw [OracleComp.runState_map] at hh
  rw [← hh]
  simp [PMF.map_comp, Function.comp_def, boolEncoding]

end IsOraclePPTOn

/-- Make the single operation explicit without changing its request or reply words. -/
def singleOperation {α : Type} (program : OracleComp Word (fun _ => Word) α) :
    WordOracleComp Unit α :=
  OracleComp.simulate (fun word => OracleComp.query ((), word)) program

/-- Naming the single operation preserves the complete interaction with a shared state. -/
@[simp] theorem runState_singleOperation {α State : Type}
    (oracle : Unit × Word → StateT State PMF Word)
    (program : OracleComp Word (fun _ => Word) α) (s : State) :
    OracleComp.runState oracle (singleOperation program) s =
      OracleComp.runState (fun word => oracle ((), word)) program s := by
  simp only [singleOperation, OracleComp.runState_simulate]
  congr 1
  funext word state
  exact OracleComp.runState_query oracle ((), word) state

private theorem singleOperation_run {k : ℕ} {Control : Type}
    (machine : Turing.OracleTM k Control) (fuel : ℕ) (input : Word) :
    singleOperation (machine.run fuel input) =
      Turing.MultiTapePTM.run machine (fun op word => OracleComp.query (op, word)) fuel input := by
  rw [singleOperation, ← Turing.OracleTM.run_core, Turing.MultiTapePTM.simulate_run]
  simp only [OracleComp.simulate_query]

/-- The established single-operation contract and the general interface agree exactly. -/
theorem isOraclePPT_iff_on {α : Type} {output : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α} :
    IsOraclePPT output program ↔ IsOraclePPTOn parameterEncoding output
      (fun pair => singleOperation (program pair.1 pair.2)) := by
  constructor
  · rintro ⟨k, states, machine, c, d, h⟩
    refine ⟨inferInstance, k, Fin states, inferInstance, machine, c, d, ?_⟩
    rintro ⟨n, input⟩ State oracle s
    rw [← singleOperation_run]
    simpa [OracleComp.runState_map, parameterEncoding] using
      h n input State (fun word => oracle ((), word)) s
  · rintro ⟨_, k, Control, hfinite, machine, c, d, h⟩
    let := hfinite
    apply isOraclePPT_of_finite_machine machine c d
    intro n input State oracle s
    have hh := h (n, input) State (fun request => oracle request.2) s
    rw [← singleOperation_run] at hh
    simpa [OracleComp.runState_map, parameterEncoding] using hh

/-- Expose the encoded input and the single operation of a cryptographic certificate. -/
theorem IsOraclePPT.on {α : Type} {output : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α} (h : IsOraclePPT output program) :
    IsOraclePPTOn parameterEncoding output
      (fun pair => singleOperation (program pair.1 pair.2)) := isOraclePPT_iff_on.mp h

/-- Recover the cryptographic facade from its general encoded-input certificate. -/
theorem IsOraclePPTOn.isOraclePPT {α : Type} {output : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α}
    (h : IsOraclePPTOn parameterEncoding output
      (fun pair => singleOperation (program pair.1 pair.2))) : IsOraclePPT output program :=
  isOraclePPT_iff_on.mpr h

end Cslib.Probability
