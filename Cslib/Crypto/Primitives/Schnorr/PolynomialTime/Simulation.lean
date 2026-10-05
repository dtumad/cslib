/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Simulation
public import Cslib.Crypto.RandomOracle.PolynomialTime
import Cslib.Tactic.PolyTime

/-! # Uniform machine certificates for Schnorr's signing simulator -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM

variable {α : Type} {F G M : ℕ → Type}
  [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]

/-- Programming the simulated commitment charges for lookup and copying the whole cache.
The transcript and its representation may depend on the security parameter. -/
theorem isPolyTime_simulateSign_finish {encode : α → Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    {transcript : ∀ a, G (parameter a) × F (parameter a) × F (parameter a)}
    (hm : IsPolyTime encode (fun a => messageCode (parameter a) (message a)))
    (hc : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (ht : IsPolyTime encode (fun a => pairEncoding (element (parameter a))
      (pairEncoding (scalar (parameter a)) (scalar (parameter a))) (transcript a))) :
    IsPolyTime encode (fun a => optionEncoding
      (pairEncoding (pairEncoding (element (parameter a)) (scalar (parameter a)))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (scalar (parameter a)))))
      (simulateSign.finish (message a) (cache a) (transcript a))) := by
  have hcommit : IsPolyTime encode (fun a => element (parameter a) (transcript a).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using ht.bitPair_fst
  have hchallenge : IsPolyTime encode (fun a => scalar (parameter a) (transcript a).2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode, List.BitPair.snd_encode] using
      ht.bitPair_snd.bitPair_fst
  have hresponse : IsPolyTime encode (fun a => scalar (parameter a) (transcript a).2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using ht.bitPair_snd.bitPair_snd
  have hinput : IsPolyTime encode (fun a =>
      pairEncoding (messageCode (parameter a)) (element (parameter a))
        (message a, (transcript a).1)) :=
    hm.pair (left := wordEncoding) (right := wordEncoding) hcommit
  have hlookup := hinput.list_lookup_indexed (parameter := parameter)
    (key := fun n => pairEncoding (messageCode n) (element n)) (value := scalar) hc
  have hentry := hinput.pair (left := wordEncoding) (right := wordEncoding) hchallenge
  have hstate := hentry.pair (left := wordEncoding) (right := wordEncoding) hc
  have hsignature := hcommit.pair (left := wordEncoding) (right := wordEncoding) hresponse
  have hsuccess :=
    (hsignature.pair (left := wordEncoding) (right := wordEncoding) hstate).option_some
  convert hlookup.option_isSome.cond (isPolyTime_const encode []) hsuccess using 1
  funext a
  cases hfind : (cache a).lookup (message a, (transcript a).1) <;>
    simp only [simulateSign.finish, hfind] <;> rfl

variable [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]

/-- The seeded simulator checks freshness and retains the complete cache. It computes the
commitment from the public key, with no access to the secret key. -/
theorem isPolyTime_simulateSign_seeded {encode : α → Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    {generator publicKey : ∀ a, G (parameter a)} {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    {challenge response : ∀ a, F (parameter a)}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hm : IsPolyTime encode (fun a => messageCode (parameter a) (message a)))
    (hc : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (hchallenge : IsPolyTime encode (fun a => scalar (parameter a) (challenge a)))
    (hresponse : IsPolyTime encode (fun a => scalar (parameter a) (response a)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 - arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding
      (pairEncoding (pairEncoding (element (parameter a)) (scalar (parameter a)))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (scalar (parameter a)))))
      (simulateSign.finish (message a) (cache a)
        (response a • generator a - challenge a • publicKey a, challenge a, response a))) := by
  apply isPolyTime_simulateSign_finish element scalar messageCode hm hc
  polytime

/-- Optional seeds preserve two distinct failure cases: sampling exhaustion is `none`, while
a programming collision is `some none`. Both paths have the same uniform runtime guarantee. -/
theorem isPolyTime_simulateSign_option {encode : α → Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    {generator publicKey : ∀ a, G (parameter a)} {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    {challenge response : ∀ a, Option (F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hm : IsPolyTime encode (fun a => messageCode (parameter a) (message a)))
    (hc : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (hchallenge : IsPolyTime encode (fun a => optionEncoding (scalar (parameter a)) (challenge a)))
    (hresponse : IsPolyTime encode (fun a => optionEncoding (scalar (parameter a)) (response a)))
    (hz : IsPolyTime encode (fun a => scalar (parameter a) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 - arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding (optionEncoding
      (pairEncoding (pairEncoding (element (parameter a)) (scalar (parameter a)))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (scalar (parameter a))))))
      (Option.map₂ (fun c z => simulateSign.finish (message a) (cache a)
        (z • generator a - c • publicKey a, c, z)) (challenge a) (response a))) := by
  have hfinish := isPolyTime_simulateSign_seeded element scalar messageCode hp hg hpk hm hc
    (hchallenge.option_getD hz) (hresponse.option_getD hz) hsmul hsub
  have h := (hchallenge.option_isSome.bool₂ hresponse.option_isSome Bool.and).cond
    hfinish.option_some (isPolyTime_const encode [])
  convert h using 1
  funext a
  cases challenge a <;> cases response a <;> rfl

variable {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- The actual signing simulator has a uniform machine implementation using two bounded
binary samplers. Sampling failure and programming collisions remain distinct in the output. -/
theorem isPPT_simulateSign {encoding : α ↪ Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    (order : ℕ → ℕ) (attempts : α → ℕ) (scalar : ∀ n, F n ≃ Fin (order n))
    {generator publicKey : ∀ a, G (parameter a)} {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    (hp : IsPolyTime encoding (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encoding (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encoding (fun a => element (parameter a) (publicKey a)))
    (hm : IsPolyTime encoding (fun a => messageCode (parameter a) (message a)))
    (hc : IsPolyTime encoding (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (finEquivEncoding (scalar (parameter a)))) (cache a)))
    (horder : IsPolyTime encoding (fun a => binaryEncoding (order (parameter a))))
    (hattempts : IsPolyTime encoding (fun a => unaryEncoding (attempts a)))
    (hz : IsPolyTime encoding (fun a => finEquivEncoding (scalar (parameter a)) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 - arg.2.2))) :
    IsPPT (Oracle := Oracle) encoding wordEncoding (fun a =>
      let sample : OptionT (effects Oracle).FreeM (F (parameter a)) :=
        OptionT.mk (Option.map (scalar (parameter a)).symm <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            (order (parameter a)) (order (parameter a)).size (attempts a))
      optionEncoding (optionEncoding (pairEncoding
        (pairEncoding (element (parameter a)) (finEquivEncoding (scalar (parameter a))))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (finEquivEncoding (scalar (parameter a))))))) <$>
        ((simulateSign sample (generator a) (publicKey a) (message a)).run (cache a)).run.run) := by
  let Sampled := Σ a, Option (F (parameter a))
  let Twice := Σ arg : Sampled, Option (F (parameter arg.1))
  let first := sigmaEncoding encoding
    (fun a => optionEncoding (finEquivEncoding (scalar (parameter a))))
  let second := sigmaEncoding first
    (fun arg => optionEncoding (finEquivEncoding (scalar (parameter arg.1))))
  let post (arg : Twice) := optionEncoding (optionEncoding (pairEncoding
    (pairEncoding (element (parameter arg.1.1)) (finEquivEncoding (scalar (parameter arg.1.1))))
    (listEncoding (pairEncoding
      (pairEncoding (messageCode (parameter arg.1.1)) (element (parameter arg.1.1)))
      (finEquivEncoding (scalar (parameter arg.1.1)))))))
      (Option.map₂ (fun c z => simulateSign.finish (message arg.1.1) (cache arg.1.1)
        (z • generator arg.1.1 - c • publicKey arg.1.1, c, z)) arg.1.2 arg.2)
  have hi := isPolyTime_input second
  have ha : IsPolyTime second (fun arg => encoding arg.1.1) := hi.sigma_fst.sigma_fst
  have hpost : IsPolyTime second post := by
    apply isPolyTime_simulateSign_option (parameter := fun arg : Twice => parameter arg.1.1)
      element (fun n => finEquivEncoding (scalar n)) messageCode
    · exact hp.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hg.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hpk.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hm.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hc.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hi.sigma_fst.sigma_snd
    · exact hi.sigma_snd
    · exact hz.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hsmul
    · exact hsub
  have hone := isPPT_sampleFin_equiv (Oracle := Oracle) (input := encoding)
    (β := fun a => F (parameter a)) (fun a => scalar (parameter a)) horder hattempts
  have htwo := isPPT_sampleFin_equiv (Oracle := Oracle) (input := first)
    (β := fun arg => F (parameter arg.1)) (fun arg => scalar (parameter arg.1))
    (horder.comp_encoded (f := Sigma.fst) (isPolyTime_input first).sigma_fst)
    (hattempts.comp_encoded (f := Sigma.fst) (isPolyTime_input first).sigma_fst)
  have h := hone.bind (htwo.map (output := wordEncoding) (f := post)
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost))
  apply h.congr
  intro a S _ _ _ oracle state
  simp only [post, bind_map_left, ← comp_map, Function.comp_def, simulateSign, simulateTranscript,
    StateT.run, bind_assoc, pure_bind]
  rw [OptionT.run_mk]
  simp only [OptionT.run_bind, OptionT.run_pure, OptionT.run_mk]
  simp only [Option.elimM, map_bind, bind_map_left]
  apply FreeM.runKernel_bind_congr_of_canReturn
  intro challenge _ state
  cases challenge with
  | none =>
    simp only [Option.map_none]
    rw [map_eq_pure_bind]
    exact runKernel_sampleFin_const (α := Word) oracle _ _ _ (pure []) state
  | some challenge =>
    simp only [Option.map_some, Option.elim_some, map_bind]
    rw [map_eq_pure_bind]
    apply FreeM.runKernel_bind_congr_of_canReturn
    intro response _ state
    cases response <;> rfl

end Cslib.Crypto.Schnorr
