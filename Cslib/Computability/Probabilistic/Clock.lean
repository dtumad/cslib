/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.PolynomialClock

/-!
# PPT realizations which actually halt
The external clocks in `IsPPT` and `IsOraclePPT` can be compiled into the machine. Thus every
certificate admits a fixed finite-control witness which actually halts within a polynomial
bound. The theorem pays for constructing the clock from blank tapes, and preserves all stateful
oracle effects. It makes no additional termination assumption on the original witness.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.OracleTM

/-- An encoded-input PPT contract admits a genuinely halting realization, including on malformed
words. Its specification is required only on the supplied input encodings. -/
theorem IsPPTOn.exists_halting_machine {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      (∀ input, machine.HaltsWithin (c * (input.length + 1) ^ d) input) ∧
      ∀ a, (ProbComp.eval (program a)).map output =
        OracleComp.eval (fun _ => PMF.pure [])
          (machine.run (c * ((input a).length + 1) ^ d) (input a)) := by
  classical
  obtain ⟨k, states, source, c, d, hsource⟩ := h
  let := Fintype.ofFinite (InternalClock.Control c d (Fin states))
  let e := Fintype.equivFin (InternalClock.Control c d (Fin states))
  refine ⟨k + d + 1, _, (source.withPolynomialClock c d).rename e,
    InternalClock.overhead c d, d + 1, ?_, ?_⟩
  · intro input
    exact (source.withPolynomialClock_haltsWithin c d input _ le_rfl).rename e
  · intro a
    rw [run_rename]
    exact (hsource a).trans
      (eval_withPolynomialClock source c d (input a) _ _ le_rfl).symm

/-- A closed PPT program has a polynomially bounded, genuinely halting machine realization. -/
theorem IsPPT.exists_halting_machine {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      (∀ input, machine.HaltsWithin (c * (input.length + 1) ^ d) input) ∧
      ∀ n input, (ProbComp.eval (program n input)).map encode =
        OracleComp.eval (fun _ => PMF.pure [])
          (machine.run (c * ((parameterInput n input).length + 1) ^ d)
            (parameterInput n input)) := by
  simpa [parameterEncoding] using h.on.exists_halting_machine

/-- An oracle PPT certificate can use a halting witness, with one polynomial working for all
inputs and every stateful oracle. The joint output and private-state distribution is unchanged. -/
theorem IsOraclePPT.exists_halting_machine {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α} (h : IsOraclePPT encode program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      (∀ input, machine.HaltsWithin (c * (input.length + 1) ^ d) input) ∧
      ∀ n input (OracleState : Type) (oracle : Word → StateT OracleState PMF Word)
        (s : OracleState),
        OracleComp.runState oracle (encode <$> program n input) s =
          OracleComp.runState oracle
            (machine.run (c * ((parameterInput n input).length + 1) ^ d)
              (parameterInput n input)) s := by
  classical
  obtain ⟨k, states, source, c, d, hsource⟩ := h
  let := Fintype.ofFinite (InternalClock.Control c d (Fin states))
  let e := Fintype.equivFin (InternalClock.Control c d (Fin states))
  refine ⟨k + d + 1, _, (source.withPolynomialClock c d).rename e,
    InternalClock.overhead c d, d + 1, ?_, ?_⟩
  · intro input
    exact (source.withPolynomialClock_haltsWithin c d input _ le_rfl).rename e
  · intro n input OracleState oracle s
    rw [run_rename]
    exact (hsource n input OracleState oracle s).trans
      (runState_withPolynomialClock source c d (parameterInput n input) oracle _ s le_rfl).symm

end Cslib.Probability
