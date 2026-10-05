/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Machine.Step
public import Cslib.Computability.PolynomialTime.Machine.Size
public import Cslib.Computability.PolynomialTime.Sampling.Iteration
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Handler
import Mathlib.Data.Fintype.Order

/-! # Uniform machines for randomized oracle substitution -/

public section

namespace Turing.MultiTapeTM

open Cslib MultiTapeMachine MultiTapePTM

variable {α State : Type} {k ports : ℕ} [Finite State]
  {input : α ↪ Word} {control : State ↪ Word}

/-- The deterministic part of a randomized transition is certified from its handler. -/
theorem isPolyTime_stepWithRandomness
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : α → Fin ports → Word → Word → Word)
    (hhandler : ∀ port, IsPolyTime (pairEncoding input (pairEncoding wordEncoding wordEncoding))
      (fun pair => handler pair.1 port pair.2.1 pair.2.2)) :
    IsPolyTime (pairEncoding input
      (pairEncoding (machineSnapshotEncoding k ports control) wordEncoding))
      (fun pair => machineSnapshotEncoding k ports control
        (machine.stepWithRandomness (input pair.1) (handler pair.1) pair.2.1 pair.2.2)) := by
  let context := pairEncoding input wordEncoding
  let execute (port : Fin ports) (request : Word) (st : α × Word) :=
    (handler st.1 port request st.2, st)
  have hcall (port : Fin ports) : IsPolyTime (pairEncoding wordEncoding context)
      (fun pair => pairEncoding wordEncoding context (execute port pair.1 pair.2)) := by
    have hr := isPolyTime_fst wordEncoding context
    have hc := isPolyTime_snd wordEncoding context
    exact ((hhandler port).comp_encoded (hc.fst.pair (hr.pair hc.snd))).pair hc
  have ha := isPolyTime_fst input
    (pairEncoding (machineSnapshotEncoding k ports control) wordEncoding)
  have hs := (isPolyTime_snd input
    (pairEncoding (machineSnapshotEncoding k ports control) wordEncoding)).fst
  have hc := (isPolyTime_snd input
    (pairEncoding (machineSnapshotEncoding k ports control) wordEncoding)).snd
  have h := (isPolyTime_stepSnapshot machine execute hcall hs ha
    (ha.pair hc.tail) (hc.headD false)).fst
  convert h using 1
  funext ⟨a, snapshot, coins⟩
  simp only [wordEncoding, Function.Embedding.refl_apply]
  dsimp only [stepWithRandomness, stepSnapshot]
  cases snapshot.state with
  | none => rfl
  | some q =>
    dsimp only
    cases machine.tr q (snapshot.inputSymbol (input a)) snapshot.workSymbols
      snapshot.answerSymbols (coins.headD false) <;> rfl

end Turing.MultiTapeTM

namespace Turing.MultiTapePTM

open Cslib PFunctor MultiTapeMachine MultiTapeTM MeasureTheory ProbabilityTheory

variable {α State Target : Type} {k ports : ℕ} [Finite State] [Finite Target]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
  {input : α ↪ Word} {control : State ↪ Word}

/-- Inline fixed-width randomized handlers into a clocked source machine. The simulator charges
for the source transitions, handler computation, reply copying, and all private random bits.
The reply bound concerns data size; the runtime bound is constructed by the loop compiler. -/
theorem isPPT_run_oracleHandler
    (machine : MultiTapePTM k Bool State (Fin ports))
    (handler : α → Fin ports → Word → Word → Word)
    {bits count : α → ℕ}
    (hhandler : ∀ port, IsPolyTime (pairEncoding input (pairEncoding wordEncoding wordEncoding))
      (fun pair => handler pair.1 port pair.2.1 pair.2.2))
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    {reply : ℕ → ℕ} (hreply : PolynomiallyBounded reply)
    (hbound : ∀ a port request coins, request.length ≤ count a → coins.length ≤ bits a →
      (handler a port request coins).length ≤ reply (input a).length) :
    IsPPT input (optionEncoding wordEncoding) (fun a =>
      (machine.run (count a) (input a)).liftM (oracleHandler (fun port request =>
        handler a port request <$> (List.replicate (bits a) ()).mapM
          (fun _ => coin (Oracle := Target))))) := by
  let : Fintype State := Fintype.ofFinite State
  let control := finiteEncoding State
  let encoding := machineSnapshotEncoding k ports control
  let initial := Snapshot.initial (k := k) (Symbol := Bool) (Oracle := Fin ports) machine.initial
  obtain ⟨bound, hcontrol⟩ := Finite.exists_le (fun state => (control state).length)
  obtain ⟨cc, dc, hc⟩ := hcount.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hc
  let delta (n : ℕ) := 2 * bound + 56 * k + 24 * ports + 6 + 20 * ports * (reply n + 1)
  have hloop := isPPT_iterate_sampleBits (Oracle := Target)
    (stateEncoding := encoding) (initial := fun _ => initial)
    (bits := fun a => bits a + 1) (count := count)
    (step := fun a => machine.stepWithRandomness (input a) (handler a))
    (isPolyTime_const input (encoding initial))
    (hbits.unary_add (isPolyTime_const input [true])) hcount
    (isPolyTime_stepWithRandomness machine handler hhandler)
    (fun a index snapshot =>
      (∀ port, (snapshot.channels port).queryBuffer.length ≤ index) ∧
        (encoding snapshot).length ≤ (encoding initial).length + index * delta (input a).length)
    (by intro a; exact ⟨by simp [initial, Snapshot.initial], by simp⟩)
    (by
      intro a index snapshot coins hi hinv hcoins
      have htail : coins.tail.length ≤ bits a := by
        simp only [List.length_tail] at *
        omega
      cases hs : snapshot.state with
      | none =>
        simp only [stepWithRandomness, stepSnapshot, hs, Id.run_pure]
        exact ⟨fun port => (hinv.1 port).trans (by omega), hinv.2.trans
          (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ index)) _)⟩
      | some q =>
        simp only [stepWithRandomness, stepSnapshot, hs]
        cases ha : machine.tr q (snapshot.inputSymbol (input a)) snapshot.workSymbols
            snapshot.answerSymbols (coins.headD false) with
        | step action symbol move =>
          refine ⟨fun port => (snapshot.length_query_step_le _ _ _ _ port).trans
            (Nat.add_le_add_right (hinv.1 port) 1), ?_⟩
          have h := length_machineSnapshotEncoding_step_le snapshot (input a)
            action symbol move hcontrol
          change (encoding (snapshot.step _ _ _ _)).length ≤ _
          change (encoding (snapshot.step _ _ _ _)).length ≤ _ at h
          have := hinv.2
          dsimp only [delta, encoding] at *
          rw [Nat.add_mul, Nat.one_mul]
          omega
        | query port next =>
          let answer := handler a port (snapshot.channels port).queryBuffer coins.tail
          have hr := hbound a port (snapshot.channels port).queryBuffer coins.tail
            ((hinv.1 port).trans (by omega)) htail
          refine ⟨fun other => (snapshot.length_query_receive_le port other next answer).trans
            ((hinv.1 other).trans (by omega)), ?_⟩
          have h := length_machineSnapshotEncoding_receive_le snapshot port next answer hcontrol
          have hm := Nat.mul_le_mul_left (20 * ports) (Nat.add_le_add_right hr 1)
          change (encoding (snapshot.receive port next answer)).length ≤ _
          change (encoding (snapshot.receive port next answer)).length ≤ _ at h
          have := hinv.2
          dsimp only [delta, encoding, answer] at *
          rw [Nat.add_mul, Nat.one_mul]
          omega)
    (size := fun n => (encoding initial).length + cc * (n + 1) ^ dc * delta n)
    (by dsimp only [delta]; fun_prop)
    (fun a index snapshot hi hinv => hinv.2.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hi.trans (hc a))) _))
  have houtput := hloop.map (isPolyTime_input encoding).machineSnapshot_output?
  apply houtput.congr
  intro a S _ _ _ oracle state
  simp only [run, runFrom, FreeM.liftM_map]
  simp only [map_eq_pure_bind]
  simpa only [map_eq_pure_bind] using
    runKernel_stepWithRandomness machine (input a) (handler a) (bits a) (count a)
    oracle initial (machine.initialConfig (input a))
    (Snapshot.represents_initial _ _)
    (fun final => pure (if final.state.isNone then some final.output else none))
    (fun final => pure (output? final))
    (by intro snapshot cfg h; simp only [output?, h.state, h.output]) state

variable {Oracle β : Type}

/-- A uniform probabilistic program remains uniform polynomial time after replacing every oracle
by certified computation on fresh fixed-width bits. Reply-size bounds follow from the handler
certificates and the source machine's request clock; callers need no separate query bound. -/
theorem IsPPT.liftM_sampleBits {output : β ↪ Word}
    {program : α → (effects Oracle).FreeM β}
    (hprogram : IsPPT input output program)
    (handler : α → Oracle → Word → Word → Word) {bits : α → ℕ}
    (hbits : IsPolyTime input (fun a => unaryEncoding (bits a)))
    (hhandler : ∀ port, IsPolyTime (pairEncoding input (pairEncoding wordEncoding wordEncoding))
      (fun pair => handler pair.1 port pair.2.1 pair.2.2)) :
    IsPPT input output (fun a => (program a).liftM (oracleHandler (fun port request =>
      handler a port request <$> (List.replicate (bits a) ()).mapM
        (fun _ => coin (Oracle := Target))))) := by
  obtain ⟨_, k, ports, State, hfinite, machine, dispatch, c, d, hm⟩ := hprogram
  let : Finite State := hfinite
  let clock (a : α) := c * ((input a).length + 1) ^ d
  have hclock : IsPolyTime input (fun a => unaryEncoding (clock a)) :=
    (isPolyTime_const input (unaryEncoding c)).unary_mul
      (((isPolyTime_input input).unaryLength.unary_add (g := fun _ => 1)
        (isPolyTime_const input [true])).unary_pow d)
  have hb := hbits.length_le
  obtain ⟨cb, db, hb⟩ := hb
  simp only [unaryEncoding_apply, List.length_replicate] at hb
  have hh (port : Fin ports) := (hhandler (dispatch port)).length_le
  choose coefficients degrees hh using hh
  obtain ⟨coefficient, hcoefficient⟩ := Finite.exists_le coefficients
  obtain ⟨degree, hdegree⟩ := Finite.exists_le degrees
  let reply (n : ℕ) := coefficient * (2 * n + 2 * (c * (n + 1) ^ d) +
    cb * (n + 1) ^ db + 3) ^ degree
  have hrun := isPPT_run_oracleHandler (Target := Target) machine
    (fun a port => handler a (dispatch port))
    (fun port => hhandler (dispatch port)) hbits hclock
    (reply := reply) (by dsimp only [reply]; fun_prop) (by
      intro a port request coins hr hc
      have h := hh port (a, request, coins)
      simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply] at h
      refine h.trans ?_
      dsimp only [reply]
      apply Nat.mul_le_mul (hcoefficient port)
      have hbase : 2 * (input a).length + (2 * request.length + coins.length + 1) + 1 + 1 ≤
          2 * (input a).length + 2 * (c * ((input a).length + 1) ^ d) +
            cb * ((input a).length + 1) ^ db + 3 := by
        have := hb a
        dsimp only [clock] at hr
        omega
      apply (Nat.pow_le_pow_left hbase _).trans
      exact Nat.pow_le_pow_right (by omega) (hdegree port))
  have hfinish := hrun.map
    ((isPolyTime_input (optionEncoding wordEncoding)).option_getD
      (fallback := fun _ => []) (isPolyTime_const (optionEncoding wordEncoding) []))
  apply isPPT_map_encoding_iff.mp
  let : Countable β := output.injective.countable
  let : MeasurableSpace β := ⊤
  apply hfinish.congr
  intro a S _ _ _ oracle state
  let localHandler (port : Oracle) (request : Word) : (effects Target).FreeM Word :=
    handler a port request <$> (List.replicate (bits a) ()).mapM (fun _ => coin)
  have heq : FreeM.runKernel (effectKernel oracle)
      ((machine.run (clock a) (input a)).liftM
        (oracleHandler (fun port => localHandler (dispatch port)))) state =
      FreeM.runKernel (effectKernel oracle)
        (((fun value => some (output value)) <$> program a).liftM (oracleHandler localHandler))
        state := by
    rw [runKernel_liftM_oracleHandler, runKernel_liftM_oracleHandler]
    exact (hm a).2 S (fun port request =>
      FreeM.runKernel (effectKernel oracle) (localHandler port request)) state
  simp only [FreeM.liftM_map] at heq
  simp only [localHandler, ← FreeM.map_eq_map, FreeM.runKernel_map] at heq ⊢
  rw [heq, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end Turing.MultiTapePTM
