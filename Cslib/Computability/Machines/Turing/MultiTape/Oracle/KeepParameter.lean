/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.OutputPrefix
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.CopyParameter

/-!
# Keeping the input parameter beside the output
`keepParameter` copies the unary parameter and delimiter to the output, then runs the original
machine on its unchanged input. The preparation costs `2 * n + 3` transitions, uses no additional
work tapes, and preserves the distribution of all subsequent oracle interactions.
-/

@[expose] public section

namespace Turing.OracleTM

open Cslib

variable {k : ℕ} {State OracleState : Type}

/-- Prefix the machine's output with the unary parameter and delimiter from its input. -/
def keepParameter (machine : OracleTM k State) :
    OracleTM k (MultiTapeTM.CopyParameter.Control ⊕ State) :=
  (ofDeterministic (MultiTapeTM.copyParameter k)).seq machine

namespace KeepParameter

/-- The prefix routine leaves all tapes initial except for its completed output. -/
def prepared (k n : ℕ) (input : List Bool) :
    Config k MultiTapeTM.CopyParameter.Control (List.replicate n true ++ false :: input) where
  tapes := ((Cfg.init (MultiTapeTM.copyParameter k).q₀
    (List.replicate n true ++ false :: input)).withState none).withOutput
    (List.replicate n true ++ [false])

theorem runState_copy (oracle : List Bool → StateT OracleState PMF (List Bool))
    (n : ℕ) (input : List Bool) (s : OracleState) :
    OracleComp.runState oracle
      ((ofDeterministic (MultiTapeTM.copyParameter k)).runConfigFrom (2 * n + 3)
        ((ofDeterministic (MultiTapeTM.copyParameter k)).initialConfig
          (List.replicate n true ++ false :: input))) s =
      PMF.pure (prepared k n input, s) := by
  rw [runState_runConfigFrom_ofDeterministic]
  change PMF.pure (({
    tapes := (MultiTapeTM.copyParameter k).runFrom
      ((Cfg.init (MultiTapeTM.copyParameter k).q₀
        (List.replicate n true ++ false :: input)).withState
          (some (MultiTapeTM.copyParameter k).q₀))
      (2 * n + 3) } : Config k MultiTapeTM.CopyParameter.Control _), s) = _
  rw [MultiTapeTM.runFrom_copyParameter _ rfl]
  rfl

theorem start_prepared (machine : OracleTM k State) (n : ℕ) (input : List Bool) :
    Sequential.start machine (prepared k n input) =
      (machine.initialConfig (List.replicate n true ++ false :: input)).prefixOutput
        (List.replicate n true ++ [false]) := by
  simp [Sequential.start, prepared, Config.prefixOutput, initialConfig, Cfg.init,
    Cfg.withState, Cfg.withOutput, Cfg.prependOutput]

end KeepParameter

/-- Copying the parameter adds linear preparation time and preserves the joint distribution
of the final machine configuration and the oracle's private state. -/
theorem runState_runConfigFrom_keepParameter (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (n : ℕ) (input : List Bool) (fuel : ℕ) (s : OracleState)
    (hhalt : machine.HaltsWithin fuel (List.replicate n true ++ false :: input)) :
    OracleComp.runState oracle
      (machine.keepParameter.runConfigFrom (2 * n + 3 + fuel)
        (machine.keepParameter.initialConfig (List.replicate n true ++ false :: input))) s =
      (OracleComp.runState oracle
        (machine.runConfigFrom fuel
          (machine.initialConfig (List.replicate n true ++ false :: input))) s).map
        (fun (final, s') =>
          (Prepend.right (final.prefixOutput (List.replicate n true ++ [false])), s')) := by
  let prep := ofDeterministic (MultiTapeTM.copyParameter k)
  let cfg := prep.initialConfig (List.replicate n true ++ false :: input)
  have hcopy : OracleComp.runState oracle (prep.runConfigFrom (2 * n + 3) cfg) s =
      PMF.pure (KeepParameter.prepared k n input, s) := KeepParameter.runState_copy oracle n input s
  have hfirst : ∀ result ∈
      (OracleComp.runState oracle (prep.runConfigFrom (2 * n + 3) cfg) s).support,
      result.1.tapes.state = none := by
    intro result hresult
    rw [hcopy] at hresult
    have heq := (PMF.mem_support_pure_iff _ _).mp hresult
    exact congrArg (fun result => result.1.tapes.state) heq
  have hsecond : ∀ result ∈
      (OracleComp.runState oracle (prep.runConfigFrom (2 * n + 3) cfg) s).support,
      ∀ final ∈ (OracleComp.runState oracle
        (machine.runConfigFrom fuel (Sequential.start machine result.1)) result.2).support,
        final.1.tapes.state = none := by
    intro result hresult final hfinal
    rw [hcopy] at hresult
    have heq := (PMF.mem_support_pure_iff _ _).mp hresult
    subst result
    rw [KeepParameter.start_prepared, runConfigFrom_prefixOutput, OracleComp.runState_map]
      at hfinal
    obtain ⟨⟨sourceFinal, sourceState⟩, hsource, rfl⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt _ oracle s sourceFinal sourceState hsource
  change OracleComp.runState oracle
    ((prep.seq machine).runConfigFrom (2 * n + 3 + fuel) (Sequential.left machine cfg)) s = _
  rw [runState_runConfigFrom_seq prep machine oracle cfg (2 * n + 3) fuel s hfirst hsecond,
    hcopy, PMF.pure_bind, KeepParameter.start_prepared, runConfigFrom_prefixOutput,
    OracleComp.runState_map, PMF.map_comp]
  rfl

/-- The copied parameter precedes the original output, with identical oracle effects. -/
theorem runState_keepParameter (machine : OracleTM k State)
    (oracle : List Bool → StateT OracleState PMF (List Bool))
    (n : ℕ) (input : List Bool) (fuel : ℕ) (s : OracleState)
    (hhalt : machine.HaltsWithin fuel (List.replicate n true ++ false :: input)) :
    OracleComp.runState oracle
      (machine.keepParameter.run (2 * n + 3 + fuel) (List.replicate n true ++ false :: input)) s =
      (OracleComp.runState oracle
        (machine.run fuel (List.replicate n true ++ false :: input)) s).map
        (fun (word, s') => (List.replicate n true ++ false :: word, s')) := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (runState_runConfigFrom_keepParameter machine oracle n input fuel s hhalt)
  simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.runState_map, PMF.map_comp,
    Function.comp_def, List.append_assoc] using h

/-- In particular, the observable word distribution retains the parameter. -/
theorem eval_keepParameter (machine : OracleTM k State) (oracle : List Bool → PMF (List Bool))
    (n : ℕ) (input : List Bool) (fuel : ℕ)
    (hhalt : machine.HaltsWithin fuel (List.replicate n true ++ false :: input)) :
    OracleComp.eval oracle
      (machine.keepParameter.run (2 * n + 3 + fuel) (List.replicate n true ++ false :: input)) =
      (OracleComp.eval oracle (machine.run fuel (List.replicate n true ++ false :: input))).map
        (fun word => List.replicate n true ++ false :: word) := by
  have h := congrArg (PMF.map Prod.fst) (runState_keepParameter machine
    (fun q (s : Unit) => (oracle q).map (fun answer => (answer, s))) n input fuel () hhalt)
  rw [OracleComp.runState_stateless, OracleComp.runState_stateless] at h
  simpa [PMF.map, Function.comp_def] using h

/-- The prepended parameter routine and the original machine both actually halt. -/
theorem HaltsWithin.keepParameter {machine : OracleTM k State} {n fuel : ℕ} {input : List Bool}
    (hhalt : machine.HaltsWithin fuel (List.replicate n true ++ false :: input)) :
    machine.keepParameter.HaltsWithin (2 * n + 3 + fuel)
      (List.replicate n true ++ false :: input) := by
  intro OracleState oracle s final s' hfinal
  rw [runState_runConfigFrom_keepParameter machine oracle n input fuel s hhalt] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, hsource, heq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp hfinal
  have hstate := congrArg (fun result => result.1.tapes.state) heq
  simpa [hhalt _ oracle s sourceFinal sourceState hsource] using hstate.symm

end Turing.OracleTM
