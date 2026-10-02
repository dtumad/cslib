/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.ReplayInput

/-!
# Random tapes for PPT witnesses

A strict PPT certificate supplies a polynomial upper bound on the number of fair bits consumed.
The shared machine's replay theorem therefore presents its output as a deterministic function of
a uniform tape of that length. The witness machine, clock coefficient, and degree are fixed
before the parameter and input are supplied.

This gives the connection needed when a reduction samples a predictor's tape once and reuses it
for several inputs. The deterministic replay compiler also supplies a linear-time realization
from an encoded coin-and-input pair, starting with blank work tapes. Thus the witness's seeded
evaluation has a genuine polynomial-time certificate.
-/

@[expose] public section

namespace Cslib.Probability

/-- Replaying a finite-control machine is deterministic polynomial time in the encoded
coin-and-input length. The certificate includes parsing, tape preparation, and final halting. -/
theorem isPolyTime_replay {k : ℕ} {State : Type} [Finite State]
    (machine : Turing.OracleTM k State) :
    IsPolyTime coinInputEncoding (fun pair =>
      Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) pair.1 pair.2) := by
  apply isPolyTime_of_finite_machine machine.replayInput 9 1
  rintro ⟨coins, input⟩
  change
    let cfg := machine.replayInput.runFrom
      (machine.replayInput.initCfg (List.BitPair.encode coins input))
      (9 * ((List.BitPair.encode coins input).length + 1) ^ 1)
    cfg.state = none ∧ cfg.output =
      Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) coins input
  have h := machine.runFrom_replayInput coins input
  have hbound : 6 * coins.length + 3 * input.length + 12 ≤
      9 * ((List.BitPair.encode coins input).length + 1) ^ 1 := by
    simp
    lia
  rw [Turing.MultiTapeTM.runFrom_eq_of_halt _ _ hbound h.1]
  exact h

/-- A uniform PPT witness realizes its encoded result as a deterministic function of one
uniform polynomial-length coin tape. The same machine and polynomial work for all inputs. -/
theorem IsPPT.exists_coin_machine {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      ∀ n input, (ProbComp.eval (program n input)).map encode =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => [])
            coins (parameterInput n input)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h
  refine ⟨k, states, machine, c, d, ?_⟩
  intro n input
  rw [hmachine n input]
  change OracleComp.eval _ (Turing.OracleTM.runFrom machine _
    (Turing.OracleTM.initialConfig machine _)) = _
  rw [← Turing.OracleTM.runFrom_core]
  exact Turing.MultiTapePTM.eval_run_eq_map_coins machine (fun _ => OracleComp.query)
    (fun _ => PMF.pure []) (fun _ _ => []) (fun _ _ => by simp) _ _

/-- A Boolean PPT program has an exact fixed-coin realization. Decoding its single output bit
preserves the entire distribution. -/
theorem IsPPT.exists_bool_coin_machine
    {program : ℕ → Word → ProbComp Bool} (h : IsPPT boolEncoding program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      ∀ n input, ProbComp.eval (program n input) =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => (Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => [])
            coins (parameterInput n input)).headD false) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.exists_coin_machine
  refine ⟨k, states, machine, c, d, ?_⟩
  intro n input
  have heq := congrArg (PMF.map (fun word : Word => word.headD false)) (hmachine n input)
  simpa [PMF.map_comp, Function.comp_def, boolEncoding, PMF.map,
    Function.Embedding.coeFn_mk] using heq

/-- Every PPT program has one polynomial-time deterministic evaluator driven by a uniform
polynomial-length seed. The evaluator and seed-length polynomial are fixed for the whole family. -/
theorem IsPPT.exists_polyTime_coin_evaluator {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ n input, (ProbComp.eval (program n input)).map encode =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => evaluate coins (parameterInput n input)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.exists_coin_machine
  exact ⟨c, d, fun coins input =>
    Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) coins input,
    isPolyTime_replay machine, hmachine⟩

/-- A Boolean PPT predictor has a polynomial-time seeded evaluator. Reading its first output
bit recovers exactly the predictor's distribution at the prescribed random-tape length. -/
theorem IsPPT.exists_bool_polyTime_coin_evaluator
    {program : ℕ → Word → ProbComp Bool} (h : IsPPT boolEncoding program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ n input, ProbComp.eval (program n input) =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => (evaluate coins (parameterInput n input)).headD false) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.exists_bool_coin_machine
  exact ⟨c, d, fun coins input =>
    Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) coins input,
    isPolyTime_replay machine, hmachine⟩

end Cslib.Probability
