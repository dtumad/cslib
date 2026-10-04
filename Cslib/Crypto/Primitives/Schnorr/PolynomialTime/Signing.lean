/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
public import Cslib.Crypto.RandomOracle.PolynomialTime

/-! # Uniform machine certificates for cached Schnorr signing -/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM

variable {α : Type} {F G M : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]

/-- Seeded signing charges for scalar arithmetic and the complete shared hash cache.
The optional seeds distinguish nonce exhaustion from an unused hash draw on a cache hit. -/
theorem isPolyTime_sign_option {encode : α → Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (scalar : ∀ n, F n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    {generator : ∀ a, G (parameter a)} {secret : ∀ a, F (parameter a)}
    {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    {nonce challenge : ∀ a, Option (F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hs : IsPolyTime encode (fun a => scalar (parameter a) (secret a)))
    (hm : IsPolyTime encode (fun a => messageCode (parameter a) (message a)))
    (hc : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a))) (cache a)))
    (hn : IsPolyTime encode (fun a => optionEncoding (scalar (parameter a)) (nonce a)))
    (hh : IsPolyTime encode (fun a => optionEncoding (scalar (parameter a)) (challenge a)))
    (hz : IsPolyTime encode (fun a => scalar (parameter a) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hrespond : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (pairEncoding (scalar n) (scalar n))))
      (fun arg => scalar arg.1 (respond arg.2.1 arg.2.2.1 arg.2.2.2))) :
    IsPolyTime encode (fun a =>
      optionEncoding (pairEncoding (pairEncoding (element (parameter a)) (scalar (parameter a)))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (scalar (parameter a)))))
        (sign (m := StateT _ Option) (monadLift (nonce a))
          (RandomOracle.query (challenge a)) (generator a) (secret a) (message a) (cache a))) := by
  have hn' := hn.option_getD hz
  have hcommit : IsPolyTime encode
      (fun a => element (parameter a) ((nonce a).getD 0 • generator a)) := by
    apply hsmul.comp_encoded (f := fun a => ⟨parameter a, (nonce a).getD 0, generator a⟩)
    exact hp.sigma (hn'.pair (left := wordEncoding) (right := wordEncoding) hg)
  have hquery := RandomOracle.isPolyTime_query_option
    (parameter := parameter) (key := fun n => pairEncoding (messageCode n) (element n))
    (value := scalar) (input := fun a => (message a, (nonce a).getD 0 • generator a))
    (hm.pair (left := wordEncoding) (right := wordEncoding) hcommit) hc hh
  have hout := hquery.option_getD (fallback := fun a => (0, cache a))
    (hz.pair (left := wordEncoding) (right := wordEncoding) hc)
  have hanswer : IsPolyTime encode (fun a => scalar (parameter a)
      ((RandomOracle.query (challenge a) (message a, (nonce a).getD 0 • generator a)
        (cache a)).getD (0, cache a)).1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hout.bitPair_fst
  have hcache : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding (messageCode (parameter a)) (element (parameter a)))
        (scalar (parameter a)))
      ((RandomOracle.query (challenge a) (message a, (nonce a).getD 0 • generator a)
        (cache a)).getD (0, cache a)).2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hout.bitPair_snd
  have hresponse : IsPolyTime encode (fun a => scalar (parameter a)
      (respond (secret a) ((nonce a).getD 0)
        ((RandomOracle.query (challenge a) (message a, (nonce a).getD 0 • generator a)
          (cache a)).getD (0, cache a)).1)) := by
    apply hrespond.comp_encoded (f := fun a => ⟨parameter a, secret a, (nonce a).getD 0,
      ((RandomOracle.query (challenge a) (message a, (nonce a).getD 0 • generator a)
        (cache a)).getD (0, cache a)).1⟩)
    exact hp.sigma (hs.pair (left := wordEncoding) (right := wordEncoding)
      (hn'.pair (left := wordEncoding) (right := wordEncoding) hanswer))
  have hsignature := hcommit.pair (left := wordEncoding) (right := wordEncoding) hresponse
  have hsuccess :=
    (hsignature.pair (left := wordEncoding) (right := wordEncoding) hcache).option_some
  have h := (hn.option_isSome.bool₂ hquery.option_isSome Bool.and).cond hsuccess
    (isPolyTime_const encode [])
  convert h using 1
  funext a
  cases hn : nonce a with
  | none => rfl
  | some r =>
    change optionEncoding _ ((RandomOracle.query (challenge a) (message a, r • generator a)
      (cache a)).bind fun out => some ((r • generator a, respond (secret a) r out.1), out.2)) = _
    cases hfind : (cache a).lookup (message a, r • generator a) <;>
      cases hh : challenge a <;>
      simp only [RandomOracle.query, Option.getD_some, hfind] <;> rfl

private theorem run_sign {m : Type → Type*} [Monad m] [LawfulMonad m] (n : ℕ)
    (draw sample : m (F n)) (g : G n) (secret : F n) (message : M n)
    (cache : List ((M n × G n) × F n)) :
    sign (monadLift draw) (RandomOracle.query sample) g secret message cache = (do
      let nonce ← draw
      let (challenge, cache') ← RandomOracle.query sample (message, nonce • g) cache
      pure ((nonce • g, respond secret nonce challenge), cache')) := by
  change StateT.run
    (sign (monadLift draw) (RandomOracle.query sample) g secret message) cache = _
  simp only [sign, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind]
  rfl

variable {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Honest signing with a shared hash cache is uniformly polynomial time. The only algebraic
certificates concern scalar multiplication, field addition and multiplication, and scalar zero. -/
theorem isPPT_sign {encoding : α ↪ Word} {parameter : α → ℕ}
    (element : ∀ n, G n ↪ Word) (messageCode : ∀ n, M n ↪ Word)
    (order : ℕ → ℕ) (attempts : α → ℕ) (scalar : ∀ n, F n ≃ Fin (order n))
    {generator : ∀ a, G (parameter a)} {secret : ∀ a, F (parameter a)}
    {message : ∀ a, M (parameter a)}
    {cache : ∀ a, List ((M (parameter a) × G (parameter a)) × F (parameter a))}
    (hp : IsPolyTime encoding (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encoding (fun a => element (parameter a) (generator a)))
    (hs : IsPolyTime encoding (fun a => finEquivEncoding (scalar (parameter a)) (secret a)))
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
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (finEquivEncoding (scalar n))))
      (fun arg => finEquivEncoding (scalar arg.1) (arg.2.1 + arg.2.2)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (finEquivEncoding (scalar n)) (finEquivEncoding (scalar n))))
      (fun arg => finEquivEncoding (scalar arg.1) (arg.2.1 * arg.2.2))) :
    IsPPT (Oracle := Oracle) encoding wordEncoding (fun a =>
      let sample : OptionT (effects Oracle).FreeM (F (parameter a)) :=
        OptionT.mk (Option.map (scalar (parameter a)).symm <$>
          FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
            (order (parameter a)) (order (parameter a)).size (attempts a))
      optionEncoding (pairEncoding
        (pairEncoding (element (parameter a)) (finEquivEncoding (scalar (parameter a))))
        (listEncoding (pairEncoding
          (pairEncoding (messageCode (parameter a)) (element (parameter a)))
          (finEquivEncoding (scalar (parameter a)))))) <$>
        (sign (monadLift sample) (RandomOracle.query sample)
          (generator a) (secret a) (message a) (cache a)).run) := by
  let Sampled := Σ a, Option (F (parameter a))
  let Twice := Σ arg : Sampled, Option (F (parameter arg.1))
  let first := sigmaEncoding encoding
    (fun a => optionEncoding (finEquivEncoding (scalar (parameter a))))
  let second := sigmaEncoding first
    (fun arg => optionEncoding (finEquivEncoding (scalar (parameter arg.1))))
  let post (arg : Twice) := optionEncoding (pairEncoding
    (pairEncoding (element (parameter arg.1.1)) (finEquivEncoding (scalar (parameter arg.1.1))))
    (listEncoding (pairEncoding
      (pairEncoding (messageCode (parameter arg.1.1)) (element (parameter arg.1.1)))
      (finEquivEncoding (scalar (parameter arg.1.1))))))
      (sign (m := StateT _ Option) (monadLift arg.1.2) (RandomOracle.query arg.2)
        (generator arg.1.1) (secret arg.1.1) (message arg.1.1) (cache arg.1.1))
  have hi := isPolyTime_input second
  have ha : IsPolyTime second (fun arg => encoding arg.1.1) := hi.sigma_fst.sigma_fst
  have hpost : IsPolyTime second post := by
    apply isPolyTime_sign_option (parameter := fun arg : Twice => parameter arg.1.1)
      element (fun n => finEquivEncoding (scalar n)) messageCode
    · exact hp.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hg.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hs.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hm.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hc.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hi.sigma_fst.sigma_snd
    · exact hi.sigma_snd
    · exact hz.comp_encoded (f := fun arg : Twice => arg.1.1) ha
    · exact hsmul
    · exact isPolyTime_respond _ hadd hmul
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
  simp only [post, bind_map_left, ← comp_map, Function.comp_def, run_sign]
  simp only [OptionT.run_bind, OptionT.run_pure, RandomOracle.run_query_optionT]
  simp only [OptionT.run, OptionT.mk, Option.elimM, map_bind, bind_map_left]
  apply FreeM.runKernel_bind_congr_of_canReturn
  intro nonce _ state
  cases nonce with
  | none =>
    simp only [Option.map_none]
    rw [map_eq_pure_bind]
    exact runKernel_sampleFin_const (α := Word) oracle _ _ _ (pure []) state
  | some nonce =>
    simp only [Option.map_some, Option.elim_some, Option.bind_eq_bind, Option.bind_some]
    cases hfind : (cache a).lookup
        (message a, (scalar (parameter a)).symm nonce • generator a) with
    | some answer =>
      simp only [RandomOracle.query, hfind, Option.pure_def,
        Option.bind_some, pure_bind, Option.elim_some, map_pure]
      rw [map_eq_pure_bind]
      exact runKernel_sampleFin_const oracle (order (parameter a)) (order (parameter a)).size
        (attempts a) (pure (optionEncoding (pairEncoding
          (pairEncoding (element (parameter a)) (finEquivEncoding (scalar (parameter a))))
          (listEncoding (pairEncoding
            (pairEncoding (messageCode (parameter a)) (element (parameter a)))
            (finEquivEncoding (scalar (parameter a))))))
          (some (((scalar (parameter a)).symm nonce • generator a,
            respond (secret a) ((scalar (parameter a)).symm nonce) answer), cache a)))) state
    | none =>
      simp only [RandomOracle.query, hfind, Option.bind_eq_bind, Option.pure_def,
        map_bind, bind_map_left, ← comp_map, Function.comp_def]
      rw [map_eq_pure_bind]
      apply FreeM.runKernel_bind_congr_of_canReturn
      intro challenge _ state
      cases challenge <;> rfl

end Cslib.Crypto.Schnorr
