/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.PPT
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.OutputExpansion

/-!
# Efficient fixed output encodings
Replacing each output bit by a fixed binary word preserves PPT. The two codewords can have
different lengths, including zero. The machine construction uses finite control and a constant
slowdown, and preserves the joint distribution of output and private oracle state.
This is a restricted postprocessing theorem, not arbitrary PPT composition: the codewords are
fixed independently of the security parameter and input.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.OracleTM.OutputExpansion

/-- A fixed word substitution on the output of a PPT program is PPT. -/
theorem IsPPT.flatMap_word {program : ℕ → Word → ProbComp Word}
    (h : IsPPT wordEncoding program) (code : Bool → Word) :
    IsPPT wordEncoding (fun n input => List.flatMap code <$> program n input) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  apply isPPTOn_of_finite_machine (machine.expandOutput code) ((width code + 2) * c) d
  intro pair
  rw [Nat.mul_assoc, Turing.OracleTM.eval_run_expandOutput, ← h pair]
  simp [ProbComp.eval_map, PMF.map_comp, Function.comp_def, wordEncoding]

/-- A fixed output encoding preserves oracle PPT, including every oracle's private state. -/
theorem IsOraclePPT.flatMap_word {program : ℕ → Word → OracleComp Word (fun _ => Word) Word}
    (h : IsOraclePPT wordEncoding program) (code : Bool → Word) :
    IsOraclePPT wordEncoding (fun n input => List.flatMap code <$> program n input) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  apply isOraclePPT_of_finite_machine (machine.expandOutput code) ((width code + 2) * c) d
  intro n input State oracle s
  rw [Nat.mul_assoc, Turing.OracleTM.runState_run_expandOutput, ← h n input State oracle s]
  simp [OracleComp.runState_map, PMF.map_comp, Function.comp_def, wordEncoding]

end Cslib.Probability
