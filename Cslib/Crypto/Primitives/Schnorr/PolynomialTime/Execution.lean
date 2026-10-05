/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime.HandlerBounds
public import Cslib.Computability.PolynomialTime.Machine.Option

/-!
# Executing an adversary against Schnorr's signing simulator

The interpreter retains the security parameter, generator, and public key alongside the
simulator state. One machine handles every parameter and every source transition. The
per-call size theorem bounds accumulated logs and caches; no runtime bound for the simulated
execution is assumed.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

variable {F G : ℕ → Type}

/-- The simulator state includes its parameter and public algebra inputs. -/
def seededSignatureMachineStateEncoding
    (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word) :
    (Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) × (List (F n) × List (F n)))) ↪
      Word :=
  sigmaEncoding unaryEncoding (fun n => pairEncoding (element n).toEmbedding
    (pairEncoding (element n).toEmbedding
      (seededSignatureStateEncoding (element n).toEmbedding (scalar n) wordEncoding)))

variable [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)]

/-- Invoke the saved-tape handler while retaining the parameter, generator, and public key. -/
def seededSignatureMachineHandler
    (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word)
    (word : Word)
    (state : Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) :
    Option (Word × Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))) := do
  let (answer, state') ← seededSignatureWordHandler (element state.1) (scalar state.1)
    state.2.1 state.2.2.1 word state.2.2.2
  pure (answer, ⟨state.1, state.2.1, state.2.2.1, state'⟩)

variable (element : ∀ n, Computability.Encoding (G n) Bool) (scalar : ∀ n, F n ↪ Word)
  (hz : IsPolyTime unaryEncoding (fun n => scalar n 0))
  (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
    (fun arg => optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
  (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (scalar n) (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 • arg.2.2)))
  (hsub : IsPolyTime (sigmaEncoding unaryEncoding
    (fun n => pairEncoding (element n).toEmbedding (element n).toEmbedding))
    (fun arg => (element arg.1).encode (arg.2.1 - arg.2.2)))

include hz hdecode hsmul hsub

/-- Parameter retention and response assembly preserve the uniform handler certificate. -/
theorem isPolyTime_seededSignatureMachineHandler :
    IsPolyTime (pairEncoding wordEncoding (seededSignatureMachineStateEncoding element scalar))
      (fun pair => optionEncoding
        (pairEncoding wordEncoding (seededSignatureMachineStateEncoding element scalar))
        (seededSignatureMachineHandler element scalar pair.1 pair.2)) := by
  let input := pairEncoding wordEncoding (seededSignatureMachineStateEncoding element scalar)
  have hi := isPolyTime_input input
  have hp := hi.snd.sigma_fst
  have hd := hi.snd.sigma_snd
  have hg : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode,
      Computability.Encoding.toEmbedding_apply] using hd.bitPair_fst
  have hpk : IsPolyTime input (fun pair => (element pair.2.1).encode pair.2.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode,
      Computability.Encoding.toEmbedding_apply] using hd.bitPair_snd.bitPair_fst
  have hs : IsPolyTime input (fun pair => seededSignatureStateEncoding
      (element pair.2.1).toEmbedding (scalar pair.2.1) wordEncoding pair.2.2.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hd.bitPair_snd.bitPair_snd
  have hm : IsPolyTime input
      (fun pair => listEncoding wordEncoding pair.2.2.2.2.1.1) := by
    simpa only [seededSignatureStateEncoding, pairEncoding_apply, List.BitPair.fst_encode] using
      hs.bitPair_fst.bitPair_fst
  have hc : IsPolyTime input (fun pair => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element pair.2.1).toEmbedding) (scalar pair.2.1))
        pair.2.2.2.2.1.2) := by
    simpa only [seededSignatureStateEncoding, pairEncoding_apply, List.BitPair.fst_encode,
      List.BitPair.snd_encode] using hs.bitPair_fst.bitPair_snd
  have hprivate : IsPolyTime input
      (fun pair => listEncoding (scalar pair.2.1) pair.2.2.2.2.2.1) := by
    simpa only [seededSignatureStateEncoding, pairEncoding_apply, List.BitPair.fst_encode,
      List.BitPair.snd_encode] using hs.bitPair_snd.bitPair_fst
  have hhash : IsPolyTime input
      (fun pair => listEncoding (scalar pair.2.1) pair.2.2.2.2.2.2) := by
    simpa only [seededSignatureStateEncoding, pairEncoding_apply, List.BitPair.snd_encode] using
      hs.bitPair_snd.bitPair_snd
  have hcall := isPolyTime_seededSignatureWordHandler element scalar hp hg hpk hi.fst
    hm hc hprivate hhash (hz.comp_encoded hp) hdecode hsmul hsub
  have hdata := hg.pair (left := wordEncoding) (right := wordEncoding)
    (hpk.pair (left := wordEncoding) (right := wordEncoding) hcall.tail.bitPair_snd)
  have hstate := hp.pair (right := wordEncoding) hdata
  have hsuccess := (hcall.tail.bitPair_fst.pair
    (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert hcall.option_isSome.cond hsuccess (isPolyTime_const input []) using 1
  funext pair
  dsimp +instances only [seededSignatureMachineHandler, wordEncoding,
    Function.Embedding.refl_apply]
  cases hrun : seededSignatureWordHandler (element pair.2.1) (scalar pair.2.1)
    pair.2.2.1 pair.2.2.2.1 pair.1 pair.2.2.2.2 <;>
    simp [hrun, seededSignatureMachineStateEncoding, sigmaEncoding, pairEncoding_apply,
      wordEncoding]
  rfl

/-- Execute every transition of an adversary against the saved-tape Schnorr simulator with a
uniform polynomial machine. Bounds on group and scalar representation sizes suffice: handler
costs, cache growth, tape consumption, copying, and rejection are all derived. -/
theorem isPolyTime_runSeededSignatureMachine
    {α State : Type} {k ports : ℕ} [Finite State]
    {input : α → Word} {control : State ↪ Word}
    (machine : Turing.MultiTapePTM k Bool State (Fin ports))
    {snapshot : α → Snapshot k Bool State (Fin ports)} {word coins : α → Word}
    {state : α → Σ n, G n × G n × ((List Word × List ((Word × G n) × F n)) ×
      (List (F n) × List (F n)))}
    (hs : IsPolyTime input (fun a => machineSnapshotEncoding k ports control (snapshot a)))
    (hw : IsPolyTime input word) (hc : IsPolyTime input coins)
    (hst : IsPolyTime input (fun a => seededSignatureMachineStateEncoding element scalar (state a)))
    {groupSize scalarSize : ℕ → ℕ}
    (hgroup : PolynomiallyBounded groupSize) (hscalar : PolynomiallyBounded scalarSize)
    (hgsize : ∀ n value, ((element n).encode value).length ≤ groupSize n)
    (hfsize : ∀ n value, (scalar n value).length ≤ scalarSize n) :
    IsPolyTime input (fun a => optionEncoding
      (pairEncoding (machineSnapshotEncoding k ports control)
        (seededSignatureMachineStateEncoding element scalar))
      (Id.run (((machine.runSnapshotFromCoins (m := StateT _ (OptionT Id)) (word a)
        (fun _ request st => OptionT.mk (pure
          (seededSignatureMachineHandler element scalar request st)))
        (coins a) (snapshot a)).run (state a)).run))) := by
  obtain ⟨cp, dp, hp⟩ := hst.sigma_fst.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at hp
  obtain ⟨cs, ds, hslen⟩ := hs.length_le
  obtain ⟨cc, dc, hclen⟩ := hc.length_le
  obtain ⟨cg, dg, hg⟩ := hgroup
  obtain ⟨cf, df, hf⟩ := hscalar
  let groupBound (n : ℕ) := cg * (cp * (n + 1) ^ dp + 1) ^ dg
  let scalarBound (n : ℕ) := cf * (cp * (n + 1) ^ dp + 1) ^ df
  let requests (n : ℕ) := cs * (n + 1) ^ ds + cc * (n + 1) ^ dc
  apply isPolyTime_runSnapshotFromCoins_optionT_of_growth machine
    (fun _ => seededSignatureMachineHandler element scalar)
    (fun _ => isPolyTime_seededSignatureMachineHandler element scalar hz hdecode hsmul hsub)
    hs hw hc hst (fun a st => st.1 = (state a).1) (fun _ => rfl)
    (reply := fun n => 2 * groupBound n + scalarBound n + 1)
    (growth := fun n => 24 * requests n + 8 * groupBound n + 4 * scalarBound n + 18)
    (by dsimp only [groupBound, scalarBound]; fun_prop)
    (by dsimp only [groupBound, scalarBound, requests]; fun_prop)
  intro a port request st hrequest hinv result hresult
  obtain ⟨out, hout, hresult⟩ := Option.bind_eq_some_iff.mp hresult
  have heq : (out.1, ⟨st.1, st.2.1, st.2.2.1, out.2⟩) = result := Option.some.inj hresult
  subst result
  have hbound := seededSignatureWordHandler_size (element st.1) (scalar st.1)
    st.2.1 st.2.2.1 request st.2.2.2 hout
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
  refine ⟨hinv, hbound.1, ?_⟩
  have hq : request.length ≤ requests (input a).length :=
    hrequest.trans (Nat.add_le_add (hslen a) (hclen a))
  simp only [seededSignatureMachineStateEncoding, length_sigmaEncoding, length_pairEncoding]
  have := hbound.2
  omega

end Cslib.Crypto.Schnorr
