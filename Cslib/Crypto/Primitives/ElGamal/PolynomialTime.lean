/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal
public import Cslib.Computability.PolynomialTime.Monoid
public import Cslib.Computability.PolynomialTime.Sampling.Rejection

/-!
# Uniform machine certificates for honest ElGamal

The security parameter is unary, while group elements and exponents use binary encodings.
All primitive certificates quantify over the entire group family before choosing a machine.
Bounded rejection sampling keeps exhaustion explicit in `OptionT`; encoding an outcome does not
remove that failure case. Exponentiation is derived by repeated squaring.
-/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor Turing.MultiTapePTM Turing.MultiTapeTM

variable {G : ℕ → Type} [∀ parameter, Group (G parameter)]
  {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- One probabilistic machine implements key generation for the whole family. The only assumed
machine certificates are the parameter data, identity, and group multiplication. -/
theorem isPPT_keygen
    (element : ∀ parameter, G parameter ↪ Word) (order attempts : ℕ → ℕ)
    (generator : ∀ parameter, G parameter)
    (horder : IsPolyTime unaryEncoding (fun parameter => binaryEncoding (order parameter)))
    (hattempts : IsPolyTime unaryEncoding (fun parameter => unaryEncoding (attempts parameter)))
    (hgenerator : IsPolyTime unaryEncoding
      (fun parameter => element parameter (generator parameter)))
    (hmul : IsPolyTime
      (sigmaEncoding unaryEncoding
        (fun parameter => pairEncoding (element parameter) (element parameter)))
      (fun value => element value.1 (value.2.1 * value.2.2)))
    (hone : IsPolyTime unaryEncoding (fun parameter => element parameter 1))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ parameter (value : G parameter), (element parameter value).length ≤ size parameter) :
    IsPPT unaryEncoding wordEncoding (fun parameter =>
      optionEncoding (pairEncoding (element parameter) (finBinaryEncoding (order parameter))) <$>
      (keygen (m := OptionT (effects Oracle).FreeM)
        (OptionT.mk (FreeM.sampleFin
          ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
          (order parameter) (order parameter).size (attempts parameter)))
        (generator parameter)).run) := by
  let input := pairEncoding unaryEncoding (optionEncoding binaryEncoding)
  have hp := isPolyTime_fst unaryEncoding (optionEncoding binaryEncoding)
  have hr := isPolyTime_snd unaryEncoding (optionEncoding binaryEncoding)
  have hnonce := hr.option_getD (fallback := fun _ => 0) (isPolyTime_const input [])
  have hpublic : IsPolyTime input
      (fun pair => element pair.1 (generator pair.1 ^ pair.2.getD 0)) := by
    apply (isPolyTime_pow element hmul hone hpoly hsize).comp_encoded
      (f := fun pair : ℕ × Option ℕ => ⟨pair.1, generator pair.1, pair.2.getD 0⟩)
    apply hp.sigma
    exact (hgenerator.comp_encoded hp).pair (left := wordEncoding) (right := wordEncoding) hnonce
  have hpost : IsPolyTime input (fun pair =>
      optionEncoding (pairEncoding (element pair.1) binaryEncoding)
        (pair.2.map (fun nonce => (generator pair.1 ^ nonce, nonce)))) := by
    have h := hr.option_isSome.cond
      (hpublic.pair (left := wordEncoding) (right := wordEncoding) hnonce).option_some
      (isPolyTime_const input [])
    convert h using 1
    funext pair
    cases pair.2 <;> rfl
  have h := (isPPT_sampleFin_size (Oracle := Oracle) horder hattempts).map_with
    (output := wordEncoding) (f := fun parameter nonce =>
      optionEncoding (pairEncoding (element parameter) binaryEncoding)
        (nonce.map (fun nonce => (generator parameter ^ nonce, nonce))))
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost)
  convert h using 1
  funext parameter
  simp only [keygen, ← map_eq_pure_bind, OptionT.run_map, ← comp_map, Function.comp_def]
  congr 1
  funext result
  cases result <;> rfl

/-- Honest encryption is uniformly polynomial time in the parameter, public key, and message.
The certificate includes the nonce sampler, both exponentiations, and multiplication by the mask. -/
theorem isPPT_encrypt
    (element : ∀ parameter, G parameter ↪ Word) (order attempts : ℕ → ℕ)
    (generator : ∀ parameter, G parameter)
    (horder : IsPolyTime unaryEncoding (fun parameter => binaryEncoding (order parameter)))
    (hattempts : IsPolyTime unaryEncoding (fun parameter => unaryEncoding (attempts parameter)))
    (hgenerator : IsPolyTime unaryEncoding
      (fun parameter => element parameter (generator parameter)))
    (hmul : IsPolyTime
      (sigmaEncoding unaryEncoding
        (fun parameter => pairEncoding (element parameter) (element parameter)))
      (fun value => element value.1 (value.2.1 * value.2.2)))
    (hone : IsPolyTime unaryEncoding (fun parameter => element parameter 1))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ parameter (value : G parameter), (element parameter value).length ≤ size parameter) :
    IsPPT (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (element parameter) (element parameter))) wordEncoding
      (fun input => optionEncoding (pairEncoding (element input.1) (element input.1)) <$>
        (encrypt (m := OptionT (effects Oracle).FreeM)
          (OptionT.mk (FreeM.sampleFin
            ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
            (order input.1) (order input.1).size (attempts input.1)))
          (generator input.1) input.2.1 input.2.2).run) := by
  let input := sigmaEncoding unaryEncoding
    (fun parameter => pairEncoding (element parameter) (element parameter))
  let captured := pairEncoding input (optionEncoding binaryEncoding)
  have ha := isPolyTime_fst input (optionEncoding binaryEncoding)
  have hp := ha.sigma_fst
  have hpk : IsPolyTime captured (fun pair => element pair.1.1 pair.1.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using ha.sigma_snd.bitPair_fst
  have hmessage : IsPolyTime captured (fun pair => element pair.1.1 pair.1.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using ha.sigma_snd.bitPair_snd
  have hr := isPolyTime_snd input (optionEncoding binaryEncoding)
  have hnonce := hr.option_getD (fallback := fun _ => 0) (isPolyTime_const captured [])
  have hpow := isPolyTime_pow element hmul hone hpoly hsize
  have hhead : IsPolyTime captured
      (fun pair => element pair.1.1 (generator pair.1.1 ^ pair.2.getD 0)) := by
    apply hpow.comp_encoded (f := fun pair : (Σ n, G n × G n) × Option ℕ =>
      ⟨pair.1.1, generator pair.1.1, pair.2.getD 0⟩)
    apply hp.sigma
    exact (hgenerator.comp_encoded hp).pair (left := wordEncoding) (right := wordEncoding) hnonce
  have hmask : IsPolyTime captured
      (fun pair => element pair.1.1 (pair.1.2.1 ^ pair.2.getD 0)) := by
    apply hpow.comp_encoded (f := fun pair : (Σ n, G n × G n) × Option ℕ =>
      ⟨pair.1.1, pair.1.2.1, pair.2.getD 0⟩)
    apply hp.sigma
    exact hpk.pair (left := wordEncoding) (right := wordEncoding) hnonce
  have hbody : IsPolyTime captured
      (fun pair => element pair.1.1 (pair.1.2.2 * pair.1.2.1 ^ pair.2.getD 0)) := by
    apply hmul.comp_encoded (f := fun pair : (Σ n, G n × G n) × Option ℕ =>
      ⟨pair.1.1, pair.1.2.2, pair.1.2.1 ^ pair.2.getD 0⟩)
    apply hp.sigma
    exact hmessage.pair (left := wordEncoding) (right := wordEncoding) hmask
  have hpost : IsPolyTime captured (fun pair =>
      optionEncoding (pairEncoding (element pair.1.1) (element pair.1.1))
        (pair.2.map (fun nonce =>
          (generator pair.1.1 ^ nonce, pair.1.2.2 * pair.1.2.1 ^ nonce)))) := by
    have h := hr.option_isSome.cond
      (hhead.pair (left := wordEncoding) (right := wordEncoding) hbody).option_some
      (isPolyTime_const captured [])
    convert h using 1
    funext pair
    cases pair.2 <;> rfl
  have hparameter := (isPolyTime_input input).sigma_fst
  have h := (isPPT_sampleFin_size (Oracle := Oracle)
    (horder.comp_encoded hparameter) (hattempts.comp_encoded hparameter)).map_with
    (output := wordEncoding) (f := fun arg nonce =>
      optionEncoding (pairEncoding (element arg.1) (element arg.1))
        (nonce.map (fun nonce => (generator arg.1 ^ nonce, arg.2.2 * arg.2.1 ^ nonce))))
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost)
  convert h using 1
  funext arg
  simp only [encrypt, ← map_eq_pure_bind, OptionT.run_map, ← comp_map, Function.comp_def]
  congr 1
  funext result
  cases result <;> rfl

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
/-- Decryption has a uniform deterministic certificate, including binary exponentiation and
inversion of the mask. Secret exponents retain their original `Fin` type. -/
theorem isPolyTime_decrypt
    (element : ∀ parameter, G parameter ↪ Word) (order : ℕ → ℕ)
    (hmul : IsPolyTime
      (sigmaEncoding unaryEncoding
        (fun parameter => pairEncoding (element parameter) (element parameter)))
      (fun value => element value.1 (value.2.1 * value.2.2)))
    (hone : IsPolyTime unaryEncoding (fun parameter => element parameter 1))
    (hinv : IsPolyTime (sigmaEncoding unaryEncoding element)
      (fun value => element value.1 value.2⁻¹))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ parameter (value : G parameter), (element parameter value).length ≤ size parameter) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (finBinaryEncoding (order parameter))
        (pairEncoding (element parameter) (element parameter))))
      (fun input => element input.1 (decrypt input.2.1 input.2.2)) := by
  let input := sigmaEncoding unaryEncoding (fun parameter =>
    pairEncoding (finBinaryEncoding (order parameter))
      (pairEncoding (element parameter) (element parameter)))
  have ha := isPolyTime_input input
  have hp := ha.sigma_fst
  have hx : IsPolyTime input (fun arg => binaryEncoding arg.2.1.val) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode, finBinaryEncoding_apply] using
      ha.sigma_snd.bitPair_fst
  have hhead : IsPolyTime input (fun arg => element arg.1 arg.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_fst
  have hbody : IsPolyTime input (fun arg => element arg.1 arg.2.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_snd
  have hmask : IsPolyTime input (fun arg => element arg.1 (arg.2.2.1 ^ arg.2.1.val)) := by
    apply (isPolyTime_pow element hmul hone hpoly hsize).comp_encoded
      (f := fun arg : Σ n, Fin (order n) × G n × G n => ⟨arg.1, arg.2.2.1, arg.2.1.val⟩)
    apply hp.sigma
    exact hhead.pair (left := wordEncoding) (right := wordEncoding) hx
  have hinverse : IsPolyTime input (fun arg => element arg.1 (arg.2.2.1 ^ arg.2.1.val)⁻¹) := by
    apply hinv.comp_encoded
      (f := fun arg : Σ n, Fin (order n) × G n × G n => ⟨arg.1, arg.2.2.1 ^ arg.2.1.val⟩)
    exact hp.sigma hmask
  simp only [decrypt, div_eq_mul_inv]
  apply hmul.comp_encoded (f := fun arg : Σ n, Fin (order n) × G n × G n =>
    ⟨arg.1, arg.2.2.2, (arg.2.2.1 ^ arg.2.1.val)⁻¹⟩)
  apply hp.sigma
  exact hbody.pair (left := wordEncoding) (right := wordEncoding) hinverse

end Cslib.Crypto.ElGamal
