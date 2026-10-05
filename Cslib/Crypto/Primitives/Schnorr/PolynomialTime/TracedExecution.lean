/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.Trace
public import Cslib.Crypto.Primitives.Schnorr.Fork
import Cslib.Tactic.PolyTime

/-! # Certified machine execution with a fresh-hash transcript -/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

variable {F G : ℕ → Type}
  [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word)
  {State : Type} {k ports : ℕ}

/-- Recording fresh hashes preserves the entire completed adversary execution, including its
snapshot, cache, private tape, and rejection behavior. -/
theorem runTracedSignatureMachine_forget
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    (machine.runSnapshotFromCoins (m := StateT _ Option) word
      (fun _ => tracedSignatureMachineHandler element scalar) coins snapshot state).map
        (fun out => (out.1, ⟨out.2.1, out.2.2.1⟩)) =
      machine.runSnapshotFromCoins (m := StateT _ Option) word
        (fun _ => seededSignatureMachineHandler element scalar) coins snapshot
          ⟨state.1, state.2.1⟩ :=
  runSnapshotFromCoins_map_state machine word
    (fun _ => seededSignatureMachineHandler element scalar)
    (fun _ => tracedSignatureMachineHandler element scalar) (fun state => ⟨state.1, state.2.1⟩)
    (fun _ => tracedSignatureMachineHandler_forget element scalar) coins snapshot state

/-- Every completed machine run attributes each cached answer to a signature or a fresh hash. -/
theorem runTracedSignatureMachine_recorded
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    (hstate : ∀ input challenge, state.2.1.2.2.1.2.lookup input = some challenge →
      input.1 ∈ state.2.1.2.2.1.1 ∨ (input, challenge) ∈ state.2.2)
    {out : Snapshot k Bool State (Fin ports) × Σ n,
      (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
        (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : machine.runSnapshotFromCoins (m := StateT _ Option) word
      (fun _ => tracedSignatureMachineHandler element scalar) coins snapshot state = some out) :
    ∀ input challenge, out.2.2.1.2.2.1.2.lookup input = some challenge →
      input.1 ∈ out.2.2.1.2.2.1.1 ∨ (input, challenge) ∈ out.2.2.2 := by
  apply runSnapshotFromCoins_preserves machine word
    (fun _ => tracedSignatureMachineHandler element scalar)
    (fun state => ∀ input challenge, state.2.1.2.2.1.2.lookup input = some challenge →
      input.1 ∈ state.2.1.2.2.1.1 ∨ (input, challenge) ∈ state.2.2) _
    coins snapshot state hstate h
  intro port request st hst result hresult
  obtain ⟨traced, htraced, hresult⟩ := Option.bind_eq_some_iff.mp hresult
  cases Option.some.inj hresult
  exact traceSeededSignatureWordHandler_recorded (element st.1) (scalar st.1)
    st.2.1.1 st.2.1.2.1 request st.2.1.2.2 st.2.2 hst htraced

/-- The transcript records precisely the consumed answer prefix of the actual machine run.
Words allow the statement to retain the interpreter's parameter-dependent scalar encoding. -/
theorem runTracedSignatureMachine_answers
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    {out : Snapshot k Bool State (Fin ports) × Σ n,
      (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
        (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : machine.runSnapshotFromCoins (m := StateT _ Option) word
      (fun _ => tracedSignatureMachineHandler element scalar) coins snapshot state = some out) :
    out.2.2.2.map (fun event => scalar out.2.1 event.2) ++
      out.2.2.1.2.2.2.2.map (scalar out.2.1) =
        state.2.2.map (fun event => scalar state.1 event.2) ++
          state.2.1.2.2.2.2.map (scalar state.1) := by
  apply runSnapshotFromCoins_preserves machine word
    (fun _ => tracedSignatureMachineHandler element scalar)
    (fun st => st.2.2.map (fun event => scalar st.1 event.2) ++
      st.2.1.2.2.2.2.map (scalar st.1) =
        state.2.2.map (fun event => scalar state.1 event.2) ++
          state.2.1.2.2.2.2.map (scalar state.1)) _ coins snapshot state rfl h
  intro port request st hst result hresult
  obtain ⟨traced, htraced, hresult⟩ := Option.bind_eq_some_iff.mp hresult
  cases Option.some.inj hresult
  have heq := congrArg (List.map (scalar st.1))
    (traceSeededSignatureWordHandler_answers (element st.1) (scalar st.1)
      st.2.1.1 st.2.1.2.1 request st.2.1.2.2 st.2.2 htraced)
  simp only [List.map_append, List.map_map, Function.comp_def] at heq
  exact heq.trans hst

/-- The actual clocked adversary records its fresh hashes in uniform polynomial time.
Each call adds at most one bounded event; the interpreter charges for the accumulated log. -/
theorem isPolyTime_runTracedSignatureMachine [Finite State]
    (hz : IsPolyTime unaryEncoding (fun n => scalar n 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))
    {α : Type} {input : α → Word} {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word}
    {state : α → Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => tracedSignatureMachineStateEncoding element scalar (state a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, (scalar n value).length ≤ scalarSize n) :
    IsPolyTime input (fun a => optionEncoding
      (pairEncoding (machineSnapshotEncoding k ports control)
        (tracedSignatureMachineStateEncoding element scalar))
      (machine.runSnapshotFromCoins (m := StateT _ Option) (word a)
        (fun _ => tracedSignatureMachineHandler element scalar)
          (coins a) (snapshot a) (state a))) := by
  obtain ⟨cp, dp, hp⟩ := hst.sigma_fst.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hp
  obtain ⟨cs, ds, hslen⟩ := hs.length_le
  obtain ⟨cc, dc, hclen⟩ := hc.length_le
  obtain ⟨cg, dg, hg⟩ := hgroup
  obtain ⟨cf, df, hf⟩ := hscalar
  let groupBound (n : ℕ) := cg * (cp * (n + 1) ^ dp + 1) ^ dg
  let scalarBound (n : ℕ) := cf * (cp * (n + 1) ^ dp + 1) ^ df
  let requests (n : ℕ) := cs * (n + 1) ^ ds + cc * (n + 1) ^ dc
  have hrun := isPolyTime_runSnapshotFromCoins_optionT_of_growth machine
    (fun _ => tracedSignatureMachineHandler element scalar)
    (fun _ => isPolyTime_tracedSignatureMachineHandler element scalar hz hdecode hsmul hsub)
    hs hw hc hst (fun a st => st.1 = (state a).1) (fun _ => rfl)
    (reply := fun n => 2 * groupBound n + scalarBound n + 1)
    (growth := fun n => 56 * requests n + 20 * groupBound n + 10 * scalarBound n + 43)
    (by dsimp only [groupBound, scalarBound]; fun_prop)
    (by dsimp only [groupBound, scalarBound, requests]; fun_prop) (by
      intro a port request st hrequest hinv result hresult
      obtain ⟨out, hout, hresult⟩ := Option.bind_eq_some_iff.mp hresult
      have heq : (out.1, ⟨st.1, (st.2.1.1, st.2.1.2.1, out.2.1), out.2.2⟩) = result :=
        Option.some.inj hresult
      subst result
      obtain ⟨hreply, hstate, hevents⟩ := traceSeededSignatureWordHandler_size
        (element st.1) (scalar st.1) st.2.1.1 st.2.1.2.1 request st.2.1.2.2 st.2.2 hout
        (groupBound (input a).length) (scalarBound (input a).length) (fun value => by
          apply (hgsize st.1 value).trans ((hg st.1).trans _)
          dsimp only [groupBound]
          rw [hinv]
          exact Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (Nat.add_le_add_right (hp a) 1) dg))
        (fun value => by
          apply (hfsize st.1 value).trans ((hf st.1).trans _)
          dsimp only [scalarBound]
          rw [hinv]
          exact Nat.mul_le_mul_left cf (Nat.pow_le_pow_left (Nat.add_le_add_right (hp a) 1) df))
      refine ⟨hinv, hreply, ?_⟩
      have hq : request.length ≤ requests (input a).length :=
        hrequest.trans (Nat.add_le_add (hslen a) (hclen a))
      simp only [tracedSignatureMachineStateEncoding, length_sigmaEncoding, length_pairEncoding]
      omega)
  simp only [runSnapshotFromCoins_optionT_id] at hrun
  convert hrun using 1
  rfl

variable (scalarCode : ∀ n, Computability.Encoding (F n) Bool)

/-- Decode and verify a completed machine output, retaining the final verifier's fresh hash. -/
def checkTracedSignatureMachine (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    Option (Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) := do
  let (candidate, state', events') ← traceSeededCall
    (checkSeededForgeryOutput (element state.1) (scalarCode state.1)
      state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none))
        (state.2.1.2.2, state.2.2)
  pure (pairEncoding wordEncoding
    (pairEncoding (element state.1).toEmbedding (scalarCode state.1).toEmbedding) candidate,
      ⟨state.1, (state.2.1.1, state.2.1.2.1, state'), events'⟩)

/-- The complete checked execution returns the fresh-hash transcript used for fork selection. -/
def runCheckedTracedSignatureMachine (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    Option (Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) := do
  let (final, state') ← machine.runSnapshotFromCoins (m := StateT _ Option) word
    (fun _ => tracedSignatureMachineHandler element (fun n => (scalarCode n).toEmbedding))
      coins snapshot state
  checkTracedSignatureMachine element scalarCode final state'

/-- The recorded final verification has exactly the original checker's rejection behavior. -/
theorem checkTracedSignatureMachine_forget (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    (checkTracedSignatureMachine element scalarCode snapshot state).map
      (fun out => (out.1, ⟨out.2.1, out.2.2.1⟩)) =
        checkSeededSignatureMachine element scalarCode snapshot ⟨state.1, state.2.1⟩ := by
  dsimp +instances only [checkTracedSignatureMachine, traceSeededCall, checkSeededSignatureMachine]
  cases checkSeededForgeryOutput (element state.1) (scalarCode state.1)
    state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none)
      state.2.1.2.2 <;> rfl

/-- The final verifier extends the same answer prefix, including when it is the first query
at the forgery's hash input. -/
theorem checkTracedSignatureMachine_answers (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    {out : Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : checkTracedSignatureMachine element scalarCode snapshot state = some out) :
    out.2.2.2.map (fun event => (scalarCode out.2.1).encode event.2) ++
      out.2.2.1.2.2.2.2.map (scalarCode out.2.1).encode =
        state.2.2.map (fun event => (scalarCode state.1).encode event.2) ++
          state.2.1.2.2.2.2.map (scalarCode state.1).encode := by
  obtain ⟨traced, htraced, hresult⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hresult
  have hplain : checkSeededForgeryOutput (element state.1) (scalarCode state.1)
      state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none)
        state.2.1.2.2 = some (traced.1, traced.2.1) := by
    rw [← traceSeededCall_forget
      (checkSeededForgeryOutput (element state.1) (scalarCode state.1)
        state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none))
      state.2.1.2.2 state.2.2, htraced]
    rfl
  obtain ⟨candidate, hword, _⟩ := (checkSeededForgeryOutput_eq_some_iff
    (element state.1) (scalarCode state.1) _ _ _ _ _).mp hplain
  rw [hword, checkSeededForgeryOutput_encode] at htraced
  have heq := congrArg (List.map (scalarCode state.1).encode)
    (traceSeededCall_check_answers state.2.1.1 state.2.1.2.1 candidate
      state.2.1.2.2 state.2.2 htraced)
  simpa only [List.map_append, List.map_map, Function.comp_def] using heq

/-- Complete checked execution preserves the tape decomposition used to restart a fork. -/
theorem runCheckedTracedSignatureMachine_answers
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    {out : Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : runCheckedTracedSignatureMachine element scalarCode machine word coins snapshot state =
      some out) :
    out.2.2.2.map (fun event => (scalarCode out.2.1).encode event.2) ++
      out.2.2.1.2.2.2.2.map (scalarCode out.2.1).encode =
        state.2.2.map (fun event => (scalarCode state.1).encode event.2) ++
          state.2.1.2.2.2.2.map (scalarCode state.1).encode := by
  obtain ⟨result, hrun, hcheck⟩ := Option.bind_eq_some_iff.mp h
  exact (checkTracedSignatureMachine_answers element scalarCode result.1 result.2 hcheck).trans
    (runTracedSignatureMachine_answers element (fun n => (scalarCode n).toEmbedding)
      machine word coins snapshot state hrun)

/-- Recording does not alter the full checked execution, including final verification. -/
theorem runCheckedTracedSignatureMachine_forget
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)) :
    (runCheckedTracedSignatureMachine element scalarCode machine word coins snapshot state).map
      (fun out => (out.1, ⟨out.2.1, out.2.2.1⟩)) =
        runCheckedSeededSignatureMachine element scalarCode machine word coins snapshot
          ⟨state.1, state.2.1⟩ := by
  unfold runCheckedTracedSignatureMachine runCheckedSeededSignatureMachine
  rw [← runTracedSignatureMachine_forget element (fun n => (scalarCode n).toEmbedding)
    machine word coins snapshot state]
  cases machine.runSnapshotFromCoins (m := StateT _ Option) word
    (fun _ => tracedSignatureMachineHandler element (fun n => (scalarCode n).toEmbedding))
      coins snapshot state with
  | none => rfl
  | some out => exact checkTracedSignatureMachine_forget element scalarCode out.1 out.2

/-- Final verification supplies an accepting recorded hash for every successful checked output. -/
theorem checkTracedSignatureMachine_forkPoint (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    (hstate : ∀ input challenge, state.2.1.2.2.1.2.lookup input = some challenge →
      input.1 ∈ state.2.1.2.2.1.1 ∨ (input, challenge) ∈ state.2.2)
    {out : Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : checkTracedSignatureMachine element scalarCode snapshot state = some out) :
    ∃ candidate, out.1 = ((Computability.encodingList Bool).bitPair
      ((element out.2.1).bitPair (scalarCode out.2.1))).encode candidate ∧
        (findForkPoint out.2.2.1.1 out.2.2.1.2.1 (some candidate) out.2.2.2).isSome := by
  obtain ⟨traced, htraced, hresult⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj hresult
  have hplain : checkSeededForgeryOutput (element state.1) (scalarCode state.1)
      state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none)
        state.2.1.2.2 = some (traced.1, traced.2.1) := by
    rw [← traceSeededCall_forget
      (checkSeededForgeryOutput (element state.1) (scalarCode state.1)
        state.2.1.1 state.2.1.2.1 (if snapshot.state.isNone then some snapshot.output else none))
      state.2.1.2.2 state.2.2, htraced]
    rfl
  obtain ⟨candidate, hword, _⟩ := (checkSeededForgeryOutput_eq_some_iff
    (element state.1) (scalarCode state.1) _ _ _ _ _).mp hplain
  rw [hword, checkSeededForgeryOutput_encode] at htraced
  obtain ⟨heq, challenge, haccepts, hmem⟩ :=
    traceSeededCall_check_recorded state.2.1.1 state.2.1.2.1 candidate state.2.1.2.2 state.2.2
      (fun input answer hlookup => hstate input answer (by
        simpa only [List.lookup_eq_some_iff, bne_iff_ne] using hlookup)) htraced
  refine ⟨traced.1, rfl, ?_⟩
  rw [heq]
  simp only [findForkPoint, List.findIdx?_isSome, List.any_eq_true, decide_eq_true_eq]
  exact ⟨((candidate.1, candidate.2.1), challenge), hmem, rfl, haccepts⟩

/-- A successful checked adversary run has a fork point in its actual fresh-hash log.
The premise holds immediately for an initially empty cache, signing log, and transcript. -/
theorem runCheckedTracedSignatureMachine_forkPoint
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    (word coins : Word) (snapshot : Snapshot k Bool State (Fin ports))
    (state : Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n))
    (hstate : ∀ input challenge, state.2.1.2.2.1.2.lookup input = some challenge →
      input.1 ∈ state.2.1.2.2.1.1 ∨ (input, challenge) ∈ state.2.2)
    {out : Word × Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (h : runCheckedTracedSignatureMachine element scalarCode machine word coins snapshot state =
      some out) :
    ∃ candidate, out.1 = ((Computability.encodingList Bool).bitPair
      ((element out.2.1).bitPair (scalarCode out.2.1))).encode candidate ∧
        (findForkPoint out.2.2.1.1 out.2.2.1.2.1 (some candidate) out.2.2.2).isSome := by
  obtain ⟨result, hrun, hcheck⟩ := Option.bind_eq_some_iff.mp h
  exact checkTracedSignatureMachine_forkPoint element scalarCode result.1 result.2
    (runTracedSignatureMachine_recorded element (fun n => (scalarCode n).toEmbedding)
      machine word coins snapshot state hstate hrun) hcheck

variable
  (hz : IsPolyTime unaryEncoding (fun n => (scalarCode n).encode 0))
  (hgroupDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
    (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
  (hscalarDecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
    (fun arg => optionEncoding (scalarCode arg.1).toEmbedding ((scalarCode arg.1).decode arg.2)))
  (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (scalarCode n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
  (hadd : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 + arg.2.2)))

include hz hgroupDecode hscalarDecode hsmul hadd

/-- Output parsing, forgery verification, and recording the verifier's query are uniform. -/
theorem isPolyTime_checkTracedSignatureMachine (control : State ↪ Word) :
    IsPolyTime (pairEncoding (machineSnapshotEncoding k ports control)
      (tracedSignatureMachineStateEncoding element (fun n => (scalarCode n).toEmbedding)))
      (fun pair => optionEncoding (pairEncoding wordEncoding
        (tracedSignatureMachineStateEncoding element (fun n => (scalarCode n).toEmbedding)))
        (checkTracedSignatureMachine element scalarCode pair.1 pair.2)) := by
  let input := pairEncoding (machineSnapshotEncoding k ports control)
    (tracedSignatureMachineStateEncoding element (fun n => (scalarCode n).toEmbedding))
  have hi := isPolyTime_input input
  have hp := hi.snd.sigma_fst
  have hg : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1.1) := by
    dsimp only [input, tracedSignatureMachineStateEncoding]
    polytime
  have hpk : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1.2.1) := by
    dsimp only [input, tracedSignatureMachineStateEncoding]
    polytime
  have hst : IsPolyTime input (fun pair => seededSignatureStateEncoding
      (element pair.2.1).toEmbedding (scalarCode pair.2.1).toEmbedding wordEncoding
        pair.2.2.1.2.2) := by
    dsimp only [input, tracedSignatureMachineStateEncoding]
    polytime
  have hcheck := isPolyTime_checkSeededForgeryOutput element scalarCode
    (messages := fun pair => pair.2.2.1.2.2.1.1) (cache := fun pair => pair.2.2.1.2.2.1.2)
    (privateScalars := fun pair => pair.2.2.1.2.2.2.1)
    (hashScalars := fun pair => pair.2.2.1.2.2.2.2) hp hg hpk hi.fst.machineSnapshot_output?
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode] using hst.bitPair_fst.bitPair_fst)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode, List.BitPair.snd_encode] using hst.bitPair_fst.bitPair_snd)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.fst_encode, List.BitPair.snd_encode] using hst.bitPair_snd.bitPair_fst)
    (by simpa only [seededSignatureStateEncoding, pairEncoding_apply,
      List.BitPair.snd_encode] using hst.bitPair_snd.bitPair_snd)
    (hz.comp_encoded hp) hgroupDecode hscalarDecode hsmul hadd
  have hevents : IsPolyTime input (fun pair => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element pair.2.1).toEmbedding)
        (scalarCode pair.2.1).toEmbedding) pair.2.2.2) := by
    dsimp only [input, tracedSignatureMachineStateEncoding]
    polytime
  have htrace := isPolyTime_traceSeededCall (encode := input)
    (state := fun pair => pair.2.2.1.2.2) (events := fun pair => pair.2.2.2)
    (fun pair => (element pair.2.1).toEmbedding) (fun pair => (scalarCode pair.2.1).toEmbedding)
    (fun _ => wordEncoding) (fun pair => pairEncoding wordEncoding
      (pairEncoding (element pair.2.1).toEmbedding (scalarCode pair.2.1).toEmbedding))
    (fun pair => checkSeededForgeryOutput (element pair.2.1) (scalarCode pair.2.1)
      pair.2.2.1.1 pair.2.2.1.2.1 (if pair.1.state.isNone then some pair.1.output else none))
    hcheck hst hevents (fallback := fun pair => ([], pair.2.2.1.1, 0))
    ((isPolyTime_const input []).pair (left := wordEncoding) (right := wordEncoding)
      (hg.pair (left := wordEncoding) (right := wordEncoding) (hz.comp_encoded hp)))
  have hkeys := hg.pair (left := wordEncoding) (right := wordEncoding)
    (hpk.pair (left := wordEncoding) (right := wordEncoding) htrace.tail.bitPair_snd.bitPair_fst)
  have hstate := hp.pair (right := wordEncoding)
    (hkeys.pair (left := wordEncoding) (right := wordEncoding) htrace.tail.bitPair_snd.bitPair_snd)
  have hsuccess := (htrace.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert htrace.option_isSome.cond hsuccess (isPolyTime_const input []) using 1
  funext pair
  dsimp +instances only [checkTracedSignatureMachine]
  cases traceSeededCall (checkSeededForgeryOutput (element pair.2.1) (scalarCode pair.2.1)
    pair.2.2.1.1 pair.2.2.1.2.1 (if pair.1.state.isNone then some pair.1.output else none))
      (pair.2.2.1.2.2, pair.2.2.2) <;>
    simp [tracedSignatureMachineStateEncoding, sigmaEncoding, pairEncoding_apply, wordEncoding]
  rfl

/-- The entire checked, traced adversary has one uniform polynomial-time machine. No certificate
for a complete run, transcript producer, or fork selector is assumed here. -/
theorem isPolyTime_runCheckedTracedSignatureMachine [Finite State]
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))
    {α : Type} {input : α → Word} {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word}
    {state : α → Σ n, (G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) × List ((Word × G n) × F n)}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a =>
      tracedSignatureMachineStateEncoding element (fun n => (scalarCode n).toEmbedding) (state a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, ((scalarCode n).encode value).length ≤ scalarSize n) :
    IsPolyTime input (fun a => optionEncoding (pairEncoding wordEncoding
      (tracedSignatureMachineStateEncoding element (fun n => (scalarCode n).toEmbedding)))
      (runCheckedTracedSignatureMachine element scalarCode machine
        (word a) (coins a) (snapshot a) (state a))) := by
  have hrun := isPolyTime_runTracedSignatureMachine element (fun n => (scalarCode n).toEmbedding)
    hz hgroupDecode hsmul hsub machine hs hw hc hst hgroup hscalar hgsize hfsize
  have hfinal := (isPolyTime_checkTracedSignatureMachine element scalarCode hz hgroupDecode
    hscalarDecode hsmul hadd control).comp_encoded (hrun.option_getD (hs.pair hst))
  exact hrun.option_bind_getD (fallback := fun a => (snapshot a, state a)) hfinal

end Cslib.Crypto.Schnorr
