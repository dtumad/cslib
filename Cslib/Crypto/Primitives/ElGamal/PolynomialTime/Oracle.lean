/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.PolynomialTime
public import Cslib.Computability.PolynomialTime.Encoding.Decoding
public import Cslib.Computability.PolynomialTime.Machine.Handler

/-!
# Certified ElGamal encryption oracles

Requests are canonically encoded messages. Replies encode an optional ciphertext: invalid
requests and exhausted nonce sampling return `none`. Each call samples fresh bits. The adversary
may inspect failure and continue; the simulator implements exactly this public algorithm.
-/

@[expose] public section

namespace Cslib.Crypto.ElGamal

open PFunctor Turing.MultiTapePTM Turing.MultiTapeTM MeasureTheory ProbabilityTheory

/-- The word interface to public encryption, retaining bounded sampling failure in its reply. -/
def encryptWord {G : Type} [Group G] {Oracle : Type} {order : ℕ}
    (element : Computability.Encoding G Bool)
    (sample : (effects Oracle).FreeM (Option (Fin order))) (g pk : G) (request : Word) :
    (effects Oracle).FreeM Word :=
  match element.decodeChecked request with
  | none => pure []
  | some message => optionEncoding (pairEncoding element.toEmbedding element.toEmbedding) <$>
    (encrypt (m := OptionT (effects Oracle).FreeM) (OptionT.mk sample) g pk message).run

/-- A canonical request has precisely the typed encryption algorithm's optional result. -/
@[simp] theorem encryptWord_encode {G : Type} [Group G] {Oracle : Type} {order : ℕ}
    (element : Computability.Encoding G Bool)
    (sample : (effects Oracle).FreeM (Option (Fin order))) (g pk message : G) :
    encryptWord element sample g pk (element.encode message) =
      optionEncoding (pairEncoding element.toEmbedding element.toEmbedding) <$>
        (encrypt (m := OptionT (effects Oracle).FreeM) (OptionT.mk sample) g pk message).run := by
  simp [encryptWord]

/-- Decoding a well-formed reply preserves exhaustion as a valid `none`, distinct from an
interface decoding error. This is a program equality, before choosing probability semantics. -/
theorem decode_encryptWord_encode {G : Type} [Group G] {Oracle : Type} {order : ℕ}
    (element : Computability.Encoding G Bool)
    (sample : (effects Oracle).FreeM (Option (Fin order))) (g pk message : G) :
    (element.bitPair element).bitOption.decodeChecked <$>
        encryptWord element sample g pk (element.encode message) =
      some <$>
        (encrypt (m := OptionT (effects Oracle).FreeM) (OptionT.mk sample) g pk message).run := by
  rw [encryptWord_encode, ← comp_map]
  congr 1
  funext result
  exact (element.bitPair element).bitOption.decodeChecked_encode result

/-- The same encryption interface evaluated from a finite private random block. -/
def encryptWordFromBits {G : Type} [Group G]
    (element : Computability.Encoding G Bool) (order attempts : ℕ) (g pk : G)
    (request coins : Word) : Word :=
  optionEncoding (pairEncoding element.toEmbedding element.toEmbedding)
    ((element.decodeChecked request).bind (fun message =>
      (selectBelow order order.size attempts coins).map (fun nonce =>
        (g ^ nonce, message * pk ^ nonce))))

/-- Sampling one block realizes the actual bounded encryption algorithm, including invalid
requests and exhaustion. The equality also retains any surrounding shared oracle state. -/
theorem runKernel_encryptWordFromBits {G Oracle S : Type} [Group G]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (oracle : Oracle → Word → Kernel S (Word × S))
    (element : Computability.Encoding G Bool) (order attempts : ℕ) (g pk : G)
    (request : Word) (state : S) :
    FreeM.runKernel (effectKernel oracle)
      (encryptWordFromBits element order attempts g pk request <$>
        (List.replicate (order.size * attempts) ()).mapM (fun _ => coin)) state =
      FreeM.runKernel (effectKernel oracle)
        (encryptWord element (FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          order order.size attempts) g pk request) state := by
  cases h : element.decodeChecked request with
  | none =>
    simp only [encryptWordFromBits, encryptWord, h, Option.bind_none, optionEncoding_none,
      map_eq_pure_bind]
    exact runKernel_sampleBits_const oracle _ _ state
  | some message =>
    change FreeM.runKernel (effectKernel oracle)
      ((fun coins => encryptWordFromBits element order attempts g pk request coins) <$>
        (List.replicate (order.size * attempts) ()).mapM (fun _ => coin)) state = _
    let encode (nonce : Option ℕ) :=
      optionEncoding (pairEncoding element.toEmbedding element.toEmbedding)
        (nonce.map (fun r => (g ^ r, message * pk ^ r)))
    have hsample := congrArg (fun measure => measure.map
      (fun out : Option ℕ × S => (encode out.1, out.2)))
      (runKernel_selectBelow oracle order order.size attempts state)
    simp only [← FreeM.runKernel_map, FreeM.map_eq_map, ← comp_map,
      Function.comp_def] at hsample
    simpa only [encryptWordFromBits, encryptWord, h, Option.bind_some,
      encrypt, ← map_eq_pure_bind, OptionT.run_map, OptionT.run_mk,
      ← comp_map, Function.comp_def, encode, Option.map_map] using hsample

variable {G : ℕ → Type} [∀ n, Group (G n)]
  (element : ∀ n, Computability.Encoding (G n) Bool) (order attempts : ℕ → ℕ)
  (g : ∀ n, G n)

/-- Canonical parsing, binary rejection, both powers, and the ciphertext product are efficient
uniformly across the family, assuming certificates for identity and multiplication. -/
theorem isPolyTime_encryptWordFromBits
    (horder : IsPolyTime unaryEncoding (fun n => binaryEncoding (order n)))
    (hattempts : IsPolyTime unaryEncoding (fun n => unaryEncoding (attempts n)))
    (hg : IsPolyTime unaryEncoding (fun n => (element n).encode (g n)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 * arg.2.2)))
    (hone : IsPolyTime unaryEncoding (fun n => (element n).encode 1))
    (hdecode : IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun arg =>
      optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ n (value : G n), ((element n).encode value).length ≤ size n) :
    IsPolyTime (pairEncoding (sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding))
      (pairEncoding wordEncoding wordEncoding))
      (fun arg => encryptWordFromBits (element arg.1.1) (order arg.1.1) (attempts arg.1.1)
        (g arg.1.1) arg.1.2 arg.2.1 arg.2.2) := by
  let context := sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding)
  let input := pairEncoding context (pairEncoding wordEncoding wordEncoding)
  have ha := isPolyTime_fst context (pairEncoding wordEncoding wordEncoding)
  have hp := ha.sigma_fst
  have hpk := ha.sigma_snd
  have hr := (isPolyTime_snd context (pairEncoding wordEncoding wordEncoding)).fst
  have hc := (isPolyTime_snd context (pairEncoding wordEncoding wordEncoding)).snd
  have hmessage := IsPolyTime.decodeChecked_indexed element hr
    (hdecode.comp_encoded (hp.pair hr))
  have hm := hmessage.option_getD (fallback := fun _ => 1) (hone.comp_encoded hp)
  have hnonce := (horder.comp_encoded hp).selectBelow
    ((horder.comp_encoded hp).binary_size) (hattempts.comp_encoded hp) hc
  have hn := hnonce.option_getD (fallback := fun _ => 0) (isPolyTime_const input [])
  have hpow := isPolyTime_pow (fun n => (element n).toEmbedding) hmul hone hpoly hsize
  have hhead := hpow.comp_encoded
    (f := fun arg : (Σ n, G n) × Word × Word =>
      ⟨arg.1.1, g arg.1.1,
        (selectBelow (order arg.1.1) (order arg.1.1).size (attempts arg.1.1) arg.2.2).getD 0⟩)
    (hp.sigma ((hg.comp_encoded hp).pair (left := wordEncoding) (right := wordEncoding) hn))
  have hmask := hpow.comp_encoded
    (f := fun arg : (Σ n, G n) × Word × Word =>
      ⟨arg.1.1, arg.1.2,
        (selectBelow (order arg.1.1) (order arg.1.1).size (attempts arg.1.1) arg.2.2).getD 0⟩)
    (hp.sigma (hpk.pair (left := wordEncoding) (right := wordEncoding) hn))
  have hbody := hmul.comp_encoded
    (f := fun arg : (Σ n, G n) × Word × Word =>
      ⟨arg.1.1, ((element arg.1.1).decodeChecked arg.2.1).getD 1,
        arg.1.2 ^
          (selectBelow (order arg.1.1) (order arg.1.1).size (attempts arg.1.1) arg.2.2).getD 0⟩)
    (hp.sigma (hm.pair (left := wordEncoding) (right := wordEncoding) hmask))
  have h := (hmessage.option_isSome.bool₂ hnonce.option_isSome (· && ·)).cond
    (hhead.pair (left := wordEncoding) (right := wordEncoding) hbody).option_some
    (isPolyTime_const input [])
  convert h using 1
  funext ⟨⟨n, pk⟩, request, coins⟩
  simp only [encryptWordFromBits, wordEncoding, Function.Embedding.refl_apply]
  cases (element n).decodeChecked request <;>
    cases selectBelow (order n) (order n).size (attempts n) coins <;> rfl

/-- A uniform adversary can simulate adaptive calls to public encryption. The source machine and
the group primitives supply the whole runtime certificate, with no assumed inlining cost or query
budget. Captured context retains the same public key throughout the phase. -/
theorem isPPT_liftM_encryptWord {Input Result Target : Type} [Finite Target]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    {input : Input ↪ Word} {output : Result ↪ Word}
    {program : Input → (effects Unit).FreeM Result}
    (hprogram : IsPPT input output program) (context : Input → Σ n, G n)
    (hcontext : IsPolyTime input (fun a =>
      sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding) (context a)))
    (horder : IsPolyTime unaryEncoding (fun n => binaryEncoding (order n)))
    (hattempts : IsPolyTime unaryEncoding (fun n => unaryEncoding (attempts n)))
    (hg : IsPolyTime unaryEncoding (fun n => (element n).encode (g n)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 * arg.2.2)))
    (hone : IsPolyTime unaryEncoding (fun n => (element n).encode 1))
    (hdecode : IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun arg =>
      optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ n (value : G n), ((element n).encode value).length ≤ size n) :
    IsPPT input output (fun a => (program a).liftM (oracleHandler (fun _ request =>
      encryptWord (element (context a).1) (FreeM.sampleFin
        ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin (Oracle := Target))
        (order (context a).1) (order (context a).1).size (attempts (context a).1))
        (g (context a).1) (context a).2 request))) := by
  have hhandler := isPolyTime_encryptWordFromBits element order attempts g
    horder hattempts hg hmul hone hdecode hpoly hsize
  have hbits := ((horder.binary_size).unary_mul hattempts).comp_encoded hcontext.sigma_fst
  have h := hprogram.liftM_sampleBits (Target := Target)
    (fun a _ => encryptWordFromBits (element (context a).1) (order (context a).1)
      (attempts (context a).1) (g (context a).1) (context a).2) hbits
    (fun _ => hhandler.comp_encoded
      ((hcontext.comp_encoded (isPolyTime_fst input (pairEncoding wordEncoding wordEncoding))).pair
        (isPolyTime_snd input (pairEncoding wordEncoding wordEncoding))))
  let : Countable Result := output.injective.countable
  let : MeasurableSpace Result := ⊤
  apply h.congr
  intro a S _ _ _ oracle state
  rw [runKernel_liftM_oracleHandler, runKernel_liftM_oracleHandler]
  congr 2
  funext op
  cases op with
  | inl _ => rfl
  | inr request =>
    ext st : 1
    exact runKernel_encryptWordFromBits oracle (element (context a).1) (order (context a).1)
      (attempts (context a).1) (g (context a).1) (context a).2 request.2 st

variable {State : ℕ → Type}

/-- The entire DDH reduction, including encryption queries in both adaptive phases, has one
uniform machine. The challenge public key is retained for every simulated encryption call. -/
theorem isPPT_ddhReduction_encryptWord {Target : Type} [Finite Target]
    [MeasurableSpace Word] [DiscreteMeasurableSpace Word]
    (state : ∀ n, State n ↪ Word)
    (choose : ∀ n, G n → (effects Unit).FreeM (G n × G n × State n))
    (guess : ∀ n, State n → G n × G n → (effects Unit).FreeM Bool)
    (hchoose : IsPPT (sigmaEncoding unaryEncoding (fun n => (element n).toEmbedding))
      wordEncoding (fun arg =>
        pairEncoding (element arg.1).toEmbedding
          (pairEncoding (element arg.1).toEmbedding (state arg.1)) <$> choose arg.1 arg.2))
    (hguess : IsPPT (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (state n) (pairEncoding (element n).toEmbedding (element n).toEmbedding)))
        boolEncoding (fun arg => guess arg.1 arg.2.1 arg.2.2))
    (horder : IsPolyTime unaryEncoding (fun n => binaryEncoding (order n)))
    (hattempts : IsPolyTime unaryEncoding (fun n => unaryEncoding (attempts n)))
    (hg : IsPolyTime unaryEncoding (fun n => (element n).encode (g n)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 * arg.2.2)))
    (hone : IsPolyTime unaryEncoding (fun n => (element n).encode 1))
    (hdecode : IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun arg =>
      optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ n (value : G n), ((element n).encode value).length ≤ size n) :
    IsPPT (sigmaEncoding unaryEncoding (fun n => pairEncoding (element n).toEmbedding
      (pairEncoding (element n).toEmbedding (element n).toEmbedding))) boolEncoding (fun arg =>
        (ddhReduction coin (choose arg.1) (guess arg.1) arg.2.1 arg.2.2.1 arg.2.2.2).liftM
          (oracleHandler (fun _ request => encryptWord (element arg.1) (FreeM.sampleFin
            ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin (Oracle := Target))
            (order arg.1) (order arg.1).size (attempts arg.1))
            (g arg.1) arg.2.1 request))) := by
  have hreduce := isPPT_ddhReduction (fun n => (element n).toEmbedding) state choose guess
    hchoose hguess hmul
  apply isPPT_liftM_encryptWord element order attempts g hreduce
    (fun arg => ⟨arg.1, arg.2.1⟩) _ horder hattempts hg hmul hone hdecode hpoly hsize
  have hi := isPolyTime_input (sigmaEncoding unaryEncoding (fun n =>
    pairEncoding (element n).toEmbedding
      (pairEncoding (element n).toEmbedding (element n).toEmbedding)))
  apply hi.sigma_fst.sigma
  simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hi.sigma_snd.bitPair_fst

end Cslib.Crypto.ElGamal
