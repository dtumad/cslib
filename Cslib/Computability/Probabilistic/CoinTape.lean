/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.ReplayInput
public import Cslib.Tactic.PolyTime

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

/-- A typed PPT witness realizes its encoded result from one uniform polynomial-length tape.
The same machine and polynomial work for all inputs in the given representation. -/
theorem IsPPTOn.exists_coin_machine {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      ∀ a, (ProbComp.eval (program a)).map output =
        (uniformBits (c * ((input a).length + 1) ^ d)).map
          (fun coins => Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => [])
            coins (input a)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h
  refine ⟨k, states, machine, c, d, ?_⟩
  intro a
  rw [hmachine a]
  change OracleComp.eval _ (Turing.OracleTM.runFrom machine _
    (Turing.OracleTM.initialConfig machine _)) = _
  rw [← Turing.OracleTM.runFrom_core]
  exact Turing.MultiTapePTM.eval_run_eq_map_coins machine (fun _ => OracleComp.query)
    (fun _ => PMF.pure []) (fun _ _ => []) (fun _ _ => by simp) _ _

/-- The cryptographic parameter-and-input interface specializes the typed saved-tape law. -/
theorem IsPPT.exists_coin_machine {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      ∀ n input, (ProbComp.eval (program n input)).map encode =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => [])
            coins (parameterInput n input)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.on.exists_coin_machine
  exact ⟨k, states, machine, c, d, fun n input => hmachine (n, input)⟩

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

/-- The encoded evaluator for any typed PPT program is uniformly polynomial time in its saved
tape and encoded input. Its seed-length polynomial is fixed for the whole family. -/
theorem IsPPTOn.exists_polyTime_coin_evaluator {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ a, (ProbComp.eval (program a)).map output =
        (uniformBits (c * ((input a).length + 1) ^ d)).map
          (fun coins => evaluate coins (input a)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.exists_coin_machine
  exact ⟨c, d, fun coins input =>
    Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => []) coins input,
    isPolyTime_replay machine, hmachine⟩

/-- A cryptographic PPT program has one efficient saved-coin evaluator for every parameter
and auxiliary input. -/
theorem IsPPT.exists_polyTime_coin_evaluator {α : Type} {encode : α ↪ Word}
    {program : ℕ → Word → ProbComp α} (h : IsPPT encode program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ n input, (ProbComp.eval (program n input)).map encode =
        (uniformBits (c * ((parameterInput n input).length + 1) ^ d)).map
          (fun coins => evaluate coins (parameterInput n input)) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := h.on.exists_polyTime_coin_evaluator
  exact ⟨c, d, evaluate, hefficient, fun n input => hrealize (n, input)⟩

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

/-- Every typed PPT program has a total deterministic polynomial-time evaluator. Every coin
word produces a supported result. Any uniform tape longer than the polynomial budget gives
exactly the program's distribution; short tapes are padded and long tapes truncated.

No decoder for arbitrary output words is assumed: the replay machine always produces a valid
encoded result on a normalized tape, and its encoding is the evaluator's actual computation. -/
theorem IsPPTOn.exists_total_seeded_evaluator {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : α → Word → β),
      IsPolyTime (pairEncoding input wordEncoding) (fun pair => output (evaluate pair.1 pair.2)) ∧
      (∀ a coins, evaluate a coins ∈ (ProbComp.eval (program a)).support) ∧
      ∀ a length, c * ((input a).length + 1) ^ d ≤ length →
        ProbComp.eval (program a) = (uniformBits length).map (evaluate a) := by
  classical
  obtain ⟨c, d, raw, hefficient, hrealize⟩ := h.exists_polyTime_coin_evaluator
  let budget (a : α) := c * ((input a).length + 1) ^ d
  let tape (a : α) (coins : Word) := (coins ++ List.replicate (budget a) false).take (budget a)
  have htape (a : α) (coins : Word) : (tape a coins).length = budget a := by
    simp [tape]
  have hvalid (a : α) (coins : Word) : ∃ result,
      result ∈ (ProbComp.eval (program a)).support ∧
        output result = raw (tape a coins) (input a) := by
    have hs : raw (tape a coins) (input a) ∈
        ((uniformBits (budget a)).map (fun coins => raw coins (input a))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr
        ⟨tape a coins, mem_support_uniformBits_iff.mpr (htape a coins), rfl⟩
    rw [← hrealize a] at hs
    exact (PMF.mem_support_map_iff _ _ _).mp hs
  let evaluate (a : α) (coins : Word) := (hvalid a coins).choose
  have hencode (a : α) (coins : Word) :
      output (evaluate a coins) = raw (tape a coins) (input a) := (hvalid a coins).choose_spec.2
  refine ⟨c, d, evaluate, ?_, fun a coins => (hvalid a coins).choose_spec.1, ?_⟩
  · simp_rw [hencode]
    have hinput := isPolyTime_fst input wordEncoding
    have hcoins := isPolyTime_snd input wordEncoding
    apply hefficient.comp_pair
    · dsimp [tape, budget]
      polytime
    · exact hinput
  · intro a length hlength
    apply PMF.map_injective output.injective
    rw [hrealize, PMF.map_comp, ← uniformBits_take hlength, PMF.map_comp]
    apply PMF.bind_congr_on_support
    intro coins hcoins
    change PMF.pure (raw (coins.take (budget a)) (input a)) =
      PMF.pure (output (evaluate a coins))
    congr 1
    have hcoinsLength := length_of_mem_support_uniformBits hcoins
    simp only [hencode, tape, List.take_append_of_le_length
      (show budget a ≤ coins.length by simpa only [budget, hcoinsLength] using hlength)]

/-- Every typed PPT program has an efficient evaluator with exactly its distribution under a
uniform polynomial-length seed. The total evaluator also supports arbitrary longer tapes. -/
theorem IsPPTOn.exists_seeded_evaluator {α β : Type} {input : α ↪ Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : α → Word → β),
      IsPolyTime (pairEncoding input wordEncoding) (fun pair => output (evaluate pair.1 pair.2)) ∧
      ∀ a, ProbComp.eval (program a) =
        (uniformBits (c * ((input a).length + 1) ^ d)).map (evaluate a) := by
  obtain ⟨c, d, evaluate, hefficient, _, hlaw⟩ := h.exists_total_seeded_evaluator
  exact ⟨c, d, evaluate, hefficient, fun a => hlaw a _ le_rfl⟩

/-- A typed program can use one larger saved tape across inputs of different lengths. The
total word evaluator trims to each input's own budget and accepts arbitrary encoded words. -/
theorem IsPPTOn.exists_padded_coin_evaluator {α β : Type} {input : α → Word} {output : β ↪ Word}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ a budget, c * ((input a).length + 1) ^ d ≤ budget →
        (ProbComp.eval (program a)).map output = (uniformBits budget).map
          (fun coins => evaluate coins (input a)) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := h.exists_polyTime_coin_evaluator
  refine ⟨c, d, fun coins input => evaluate (coins.take (c * (input.length + 1) ^ d)) input,
    ?_, ?_⟩
  · apply hefficient.comp_pair <;> polytime
  · intro a budget hbudget
    rw [hrealize, ← uniformBits_take hbudget, PMF.map_comp]
    rfl

/-- Reading the raw evaluator's first bit preserves a Boolean program's distribution. The
common tape budget may depend only on a bound on input size. -/
theorem IsPPTOn.exists_padded_bool_coin_evaluator {α : Type} {input : α → Word}
    {program : α → ProbComp Bool} (h : IsPPTOn input boolEncoding program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ a budget, c * ((input a).length + 1) ^ d ≤ budget →
        ProbComp.eval (program a) = (uniformBits budget).map
          (fun coins => (evaluate coins (input a)).headD false) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := h.exists_padded_coin_evaluator
  refine ⟨c, d, evaluate, hefficient, ?_⟩
  intro a budget hbudget
  have heq := congrArg (PMF.map (fun word : Word => word.headD false)) (hrealize a budget hbudget)
  simpa [PMF.map_comp, Function.comp_def, boolEncoding, PMF.map,
    Function.Embedding.coeFn_mk] using heq

/-- Specialize the common saved-tape evaluator to the cryptographic parameter interface. -/
theorem IsPPT.exists_padded_bool_coin_evaluator
    {program : ℕ → Word → ProbComp Bool} (h : IsPPT boolEncoding program) :
    ∃ (c d : ℕ) (evaluate : Word → Word → Word),
      IsPolyTime coinInputEncoding (fun pair => evaluate pair.1 pair.2) ∧
      ∀ n input budget, c * ((parameterInput n input).length + 1) ^ d ≤ budget →
        ProbComp.eval (program n input) = (uniformBits budget).map
          (fun coins => (evaluate coins (parameterInput n input)).headD false) := by
  obtain ⟨c, d, evaluate, hefficient, hlaw⟩ := h.on.exists_padded_bool_coin_evaluator
  exact ⟨c, d, evaluate, hefficient, fun n input => hlaw (n, input)⟩

end Cslib.Probability
