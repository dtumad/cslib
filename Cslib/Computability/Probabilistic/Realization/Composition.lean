/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Clock
public import Cslib.Computability.Probabilistic.Realization.PolynomialTime
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Composition
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.OutputPrefix
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Machine realizations of probabilistic sequencing

`IsPPTOn.bind` buffers an encoded result and passes it to the continuation through the shared
machine composition compiler. Polynomial output length bounds the continuation's runtime.
`IsPPTOn.prefix` computes retained input data with a workspace-restoring deterministic routine,
then runs the probabilistic source on the original input. Both constructions charge every copy,
rewind, and initialization. Typed pairing and captured continuations are derived from these two
realizations in the public `Composition` module.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.OracleTM

open Turing in
/-- Prepend efficiently computed input data to a probabilistic result. The deterministic
preparation restores its workspace, so the original program runs on the original input. -/
theorem IsPPTOn.prefix {α : Type} {input : α → Word} {pre : α → Word}
    {program : α → ProbComp Word} (hprogram : IsPPTOn input wordEncoding program)
    (hprefix : IsPolyTime input pre) :
    IsPPTOn input wordEncoding (fun a => (pre a ++ ·) <$> program a) := by
  obtain ⟨ki, InitState, hfinite, initializer, ci, di, hi⟩ := hprefix.exists_restoring_machine
  let : Finite InitState := hfinite
  obtain ⟨ks, states, source, cs, ds, hhalt, hsource⟩ := hprogram.exists_halting_machine
  let prep := initializer.extendTapes (Fin.castAddEmb ks)
  let runner := source.extendTapes (Fin.natAddEmb ki)
  let compiled := (ofDeterministic prep).seq runner
  let prepareTime := fun length => ci * (length + 1) ^ di
  let runTime := fun length => cs * (length + 1) ^ ds
  have hpoly : PolynomiallyBounded (fun length => prepareTime length + runTime length) := by
    fun_prop
  obtain ⟨coefficient, degree, htime⟩ := hpoly
  have hprep (a : α) :
      prep.runFrom (Cfg.init prep.q₀ (input a)) (prepareTime (input a).length) =
        wordsCfg (input a) none (fun _ => []) (pre a) := by
    rw [Cfg.init_eq_wordsCfg]
    apply MultiTapeTM.runFrom_extendTapes_words
    · simpa [prepareTime, Function.comp_def] using hi a []
    · intro i _
      rfl
  have hrunner (a : α) : runner.HaltsWithin (runTime (input a).length) (input a) :=
    (hhalt (input a)).extendTapes (Fin.natAddEmb ki)
  have hrun (a : α) (OracleState : Type) (oracle : Word → StateT OracleState PMF Word)
      (s : OracleState) :
      OracleComp.runState oracle
        (compiled.runConfigFrom (prepareTime (input a).length + runTime (input a).length)
          (compiled.initialConfig (input a))) s =
        (OracleComp.runState oracle (runner.runConfigFrom (runTime (input a).length)
          (runner.initialConfig (input a))) s).map
          (fun (final, s') => (Prepend.right (final.prefixOutput (pre a)), s')) := by
    let cfg := (ofDeterministic prep).initialConfig (input a)
    let ready : Config (ki + ks) InitState (input a) :=
      { tapes := wordsCfg (input a) none (fun _ => []) (pre a) }
    have hfirst : OracleComp.runState oracle
        ((ofDeterministic prep).runConfigFrom (prepareTime (input a).length) cfg) s =
        PMF.pure (ready, s) := by
      rw [runState_runConfigFrom_ofDeterministic]
      change PMF.pure (({ tapes := (prep.runFrom (Cfg.init prep.q₀ (input a))
        (prepareTime (input a).length)) } : Config (ki + ks) InitState (input a)), s) = _
      rw [hprep]
    have hstart : Sequential.start runner ready =
        (runner.initialConfig (input a)).prefixOutput (pre a) := by
      simp [Sequential.start, ready, initialConfig, Config.prefixOutput,
        Cfg.prependOutput, wordsCfg, Cfg.withState]
    have hsecond : ∀ final ∈ (OracleComp.runState oracle
        (runner.runConfigFrom (runTime (input a).length)
          (Sequential.start runner ready)) s).support,
        final.1.tapes.state = none := by
      intro final hfinal
      rw [hstart, runConfigFrom_prefixOutput, OracleComp.runState_map] at hfinal
      obtain ⟨⟨original, state⟩, horiginal, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      exact (congrArg (fun result => result.1.tapes.state) heq).symm.trans
        (hrunner a OracleState oracle s original state horiginal)
    change OracleComp.runState oracle
      (((ofDeterministic prep).seq runner).runConfigFrom
        (prepareTime (input a).length + runTime (input a).length)
        (Sequential.left runner cfg)) s = _
    rw [runState_runConfigFrom_seq_pure _ _ oracle cfg ready _ _ s hfirst rfl hsecond,
      hstart, runConfigFrom_prefixOutput, OracleComp.runState_map, PMF.map_comp]
    rfl
  have hcompiled (a : α) : compiled.HaltsWithin
      (prepareTime (input a).length + runTime (input a).length) (input a) := by
    intro OracleState oracle s final s' hfinal
    rw [hrun] at hfinal
    obtain ⟨⟨original, state⟩, horiginal, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    have hstate := congrArg (fun result => result.1.tapes.state) heq
    simpa [hrunner a OracleState oracle s original state horiginal] using hstate.symm
  apply isPPTOn_of_finite_machine compiled coefficient degree
  intro a
  rw [(hcompiled a).eval_run_eq _ _ (htime (input a).length)]
  have hresult := congrArg (PMF.map (fun result => result.1.tapes.output))
    (hrun a Unit (fun _ (s : Unit) => (PMF.pure ([] : Word)).map (fun answer => (answer, s))) ())
  rw [OracleComp.runState_stateless, OracleComp.runState_stateless] at hresult
  have hout : OracleComp.eval (fun _ => PMF.pure [])
      (compiled.run (prepareTime (input a).length + runTime (input a).length) (input a)) =
      (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (runTime (input a).length) (input a))).map (pre a ++ ·) := by
    simpa [run, runFrom_eq_map_runConfigFrom, OracleComp.eval_map, PMF.map_comp,
      Function.comp_def, runner, initialConfig_extendTapes, runConfigFrom_embed] using hresult
  rw [hout, ← hsource a]
  simp only [ProbComp.eval_map, show (wordEncoding : Word → Word) = id from rfl, PMF.map_id]

/-- Sequence two encoded-input programs. Every intermediate code is produced by the first
program, and its polynomial length bound controls the continuation's running time. -/
theorem IsPPTOn.bind {α β γ : Type} {input : α → Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → ProbComp β} {second : β → ProbComp γ}
    (hfirst : IsPPTOn input middle first) (hsecond : IsPPTOn middle output second) :
    IsPPTOn input output (fun a => do
      let b ← first a
      second b) := by
  obtain ⟨k₀, states₀, source, c₀, d₀, hsourceHalt, hsource⟩ := hfirst.exists_halting_machine
  obtain ⟨k₁, states₁, target, c₁, d₁, htargetHalt, htarget⟩ := hsecond.exists_halting_machine
  let firstTime := fun length => c₀ * (length + 1) ^ d₀
  let secondTime := fun length => c₁ * (firstTime length + 1) ^ d₁
  have hpoly : PolynomiallyBounded
      (fun length => firstTime length + (firstTime length + 4 + secondTime length)) := by fun_prop
  obtain ⟨coefficient, degree, htime⟩ := hpoly
  apply isPPTOn_of_finite_machine (source.comp target) coefficient degree
  intro a
  let encoded := input a
  have hlength (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      word.length ≤ firstTime encoded.length := by
    simpa [initialConfig] using length_output_eval_runFrom_le source _ _
      (source.initialConfig encoded) word hword
  have hbound (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      c₁ * (word.length + 1) ^ d₁ ≤ secondTime encoded.length :=
    Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right (hlength word hword) 1) d₁)
  have htargetBound (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      target.HaltsWithin (secondTime encoded.length) word :=
    (htargetHalt word).mono (hbound word hword)
  have hhalt := (hsourceHalt encoded).comp htargetBound
  rw [hhalt.eval_run_eq _ _ (htime encoded.length), eval_comp source target encoded
    (firstTime encoded.length) (secondTime encoded.length) (hsourceHalt encoded) htargetBound]
  rw [← hsource a, PMF.bind_map]
  simp only [ProbComp.eval_bind, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro result hresult
  have hword : middle result ∈
      (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support := by
    rw [← hsource a]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, hresult, rfl⟩
  exact (htarget result).trans
    ((htargetHalt (middle result)).eval_run_eq _ _ (hbound _ hword)).symm

end Cslib.Probability
