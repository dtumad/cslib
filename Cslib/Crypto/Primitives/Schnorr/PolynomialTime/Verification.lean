/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
public import Cslib.Crypto.RandomOracle.PolynomialTime

/-! # Uniform machine certificates for cached Schnorr verification -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM

variable {α : Type} {F G M : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]

private theorem run_verify {m : Type → Type*} [Monad m] [LawfulMonad m] (n : ℕ)
    (sample : m (F n)) (g pk : G n) (message : M n) (signature : G n × F n)
    (cache : List ((M n × G n) × F n)) :
    verify (RandomOracle.query sample) g pk message signature cache =
      (fun out => (decide (Accepts g pk signature.1 out.1 signature.2), out.2)) <$>
        RandomOracle.query sample (message, signature.1) cache := by
  change StateT.run (verify (RandomOracle.query sample) g pk message signature) cache = _
  simp only [verify, ← map_eq_pure_bind]
  exact StateT.run_map _ _ _

variable {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Verification shares the signer's cache and propagates sampling failure only on a fresh hash
query. One uniform clock charges for group arithmetic, cache traversal, and the returned state. -/
theorem isPPT_verify {encoding : α ↪ Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    (order : ℕ → ℕ) (attempts : α → ℕ) (scalar : ∀ n, F n ≃ Fin (order n))
    {generator publicKey : ∀ a, G (parameter a)} {message : ∀ a, M (parameter a)}
    {signature : ∀ a, G (parameter a) × F (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    (hp : IsPolyTime encoding (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encoding (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encoding (fun a => element (parameter a) (publicKey a)))
    (hm : IsPolyTime encoding (fun a => messageCode (parameter a) (message a)))
    (hsig : IsPolyTime encoding (fun a => pairEncoding (element (parameter a))
      (finEquivEncoding (scalar (parameter a))) (signature a)))
    (hc : IsPolyTime encoding (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (finEquivEncoding (scalar (parameter a)))) (cache a)))
    (horder : IsPolyTime encoding (fun a => binaryEncoding (order (parameter a))))
    (hattempts : IsPolyTime encoding (fun a => unaryEncoding (attempts a)))
    (hz : IsPolyTime encoding (fun a => finEquivEncoding (scalar (parameter a)) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPPT (Oracle := Oracle) encoding wordEncoding (fun a =>
      let sample : OptionT (effects Oracle).FreeM (F (parameter a)) :=
        OptionT.mk (Option.map (scalar (parameter a)).symm <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            (order (parameter a)) (order (parameter a)).size (attempts a))
      optionEncoding (pairEncoding boolEncoding (listEncoding (pairEncoding
        (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (finEquivEncoding (scalar (parameter a)))))) <$>
        (verify (RandomOracle.query sample) (generator a) (publicKey a)
          (message a) (signature a) (cache a)).run) := by
  let Answered := Σ a, Option (F (parameter a) ×
    List ((M (parameter a) × G (parameter a)) × F (parameter a)))
  let answerCode (a : α) := optionEncoding (pairEncoding (finEquivEncoding (scalar (parameter a)))
    (listEncoding (pairEncoding
      (pairEncoding (messageCode (parameter a)) (element (parameter a)))
      (finEquivEncoding (scalar (parameter a))))))
  let answered := sigmaEncoding encoding answerCode
  let post (arg : Answered) := optionEncoding (pairEncoding boolEncoding (listEncoding (pairEncoding
    (pairEncoding (messageCode (parameter arg.1)) (element (parameter arg.1)))
    (finEquivEncoding (scalar (parameter arg.1))))))
      (arg.2.map fun out => (decide (Accepts (generator arg.1) (publicKey arg.1)
        (signature arg.1).1 out.1 (signature arg.1).2), out.2))
  have hi := isPolyTime_input answered
  have ha : IsPolyTime answered (fun arg => encoding arg.1) := hi.sigma_fst
  have hout := hi.sigma_snd.option_getD (fallback := fun arg : Answered => (0, cache arg.1))
    ((hz.comp_encoded (f := Sigma.fst) ha).pair (left := wordEncoding) (right := wordEncoding)
      (hc.comp_encoded (f := Sigma.fst) ha))
  have hchallenge : IsPolyTime answered (fun arg => finEquivEncoding (scalar (parameter arg.1))
      (arg.2.getD (0, cache arg.1)).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hout.bitPair_fst
  have hcache : IsPolyTime answered (fun arg => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter arg.1)) (element (parameter arg.1)))
        (finEquivEncoding (scalar (parameter arg.1)))) (arg.2.getD (0, cache arg.1)).2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hout.bitPair_snd
  have hcommit : IsPolyTime encoding (fun a => element (parameter a) (signature a).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hsig.bitPair_fst
  have hresponse : IsPolyTime encoding
      (fun a => finEquivEncoding (scalar (parameter a)) (signature a).2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hsig.bitPair_snd
  have hvalid : IsPolyTime answered (fun arg => boolEncoding (decide
      (Accepts (generator arg.1) (publicKey arg.1) (signature arg.1).1
        (arg.2.getD (0, cache arg.1)).1 (signature arg.1).2))) := by
    apply (isPolyTime_accepts
      (fun n => finEquivEncoding (scalar n)) element hsmul hadd).comp_encoded
      (f := fun arg : Answered => ⟨parameter arg.1, generator arg.1, publicKey arg.1,
        (signature arg.1).1, (arg.2.getD (0, cache arg.1)).1, (signature arg.1).2⟩)
    apply (hp.comp_encoded (f := Sigma.fst) ha).sigma
    exact (hg.comp_encoded (f := Sigma.fst) ha).pair (left := wordEncoding) (right := wordEncoding)
      ((hpk.comp_encoded (f := Sigma.fst) ha).pair (left := wordEncoding) (right := wordEncoding)
        ((hcommit.comp_encoded (f := Sigma.fst) ha).pair
          (left := wordEncoding) (right := wordEncoding)
          (hchallenge.pair (left := wordEncoding) (right := wordEncoding)
            (hresponse.comp_encoded (f := Sigma.fst) ha))))
  have hpost : IsPolyTime answered post := by
    have h := hi.sigma_snd.option_isSome.cond
      (hvalid.pair (left := wordEncoding) (right := wordEncoding) hcache).option_some
      (isPolyTime_const answered [])
    convert h using 1
    funext arg
    dsimp only [post]
    cases arg.2 <;> rfl
  have hquery := RandomOracle.isPPT_query (Oracle := Oracle) (parameter := parameter)
    (key := fun n => pairEncoding (messageCode n) (element n))
    (input := fun a => (message a, (signature a).1)) order attempts scalar horder hattempts
    (hm.pair (left := wordEncoding) (right := wordEncoding) hcommit) hc
  have h := hquery.sigma.map (output := wordEncoding) (f := post)
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost)
  convert h using 1
  funext a
  simp only [post, ← comp_map, Function.comp_def, run_verify, OptionT.run_map]

end Cslib.Crypto.Schnorr
