/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Computability.PolynomialTime.Encoding.Finite
public import Cslib.Computability.PolynomialTime.Sampling.Rejection
import Cslib.Tactic.PolyTime

/-!
# Uniform machine certificates for Schnorr

Scalars use a supplied finite-range equivalence and binary indices. Group representations are
independent of that scalar encoding. Primitive certificates concern one machine over the whole
family, including the unary security parameter. Bounded sampling retains explicit failure.
-/

public section

namespace Cslib.Crypto.Schnorr

open PFunctor Turing.MultiTapePTM Turing.MultiTapeTM

variable {F G : ℕ → Type} [∀ parameter, Field (F parameter)]
  [∀ parameter, AddCommGroup (G parameter)] [∀ parameter, Module (F parameter) (G parameter)]

private def scalarOfNat {order : ℕ → ℕ} (scalar : ∀ parameter, F parameter ≃ Fin (order parameter))
    (parameter value : ℕ) : F parameter :=
  if h : value < order parameter then (scalar parameter).symm ⟨value, h⟩ else 0

private theorem scalarOfNat_val {order : ℕ → ℕ}
    (scalar : ∀ parameter, F parameter ≃ Fin (order parameter))
    (parameter : ℕ) (value : Fin (order parameter)) :
    scalarOfNat scalar parameter value.val = (scalar parameter).symm value := by
  simp [scalarOfNat, value.isLt]

variable {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Honest Schnorr key generation is uniformly polynomial time given certified parameter data,
scalar zero, and scalar multiplication. Binary rejection sampling implements the random scalar. -/
theorem isPPT_keygen
    (element : ∀ parameter, G parameter ↪ Word) (order attempts : ℕ → ℕ)
    (scalar : ∀ parameter, F parameter ≃ Fin (order parameter))
    (generator : ∀ parameter, G parameter)
    (horder : IsPolyTime unaryEncoding (fun parameter => binaryEncoding (order parameter)))
    (hattempts : IsPolyTime unaryEncoding (fun parameter => unaryEncoding (attempts parameter)))
    (hgenerator : IsPolyTime unaryEncoding
      (fun parameter => element parameter (generator parameter)))
    (hzero : IsPolyTime unaryEncoding
      (fun parameter => finEquivEncoding (scalar parameter) 0))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (finEquivEncoding (scalar parameter)) (element parameter)))
      (fun value => element value.1 (value.2.1 • value.2.2))) :
    IsPPT unaryEncoding wordEncoding (fun parameter =>
      optionEncoding (pairEncoding (element parameter) (finEquivEncoding (scalar parameter))) <$>
        (keygen (m := OptionT (effects Oracle).FreeM)
          (OptionT.mk (Option.map (scalar parameter).symm <$>
            FreeM.sampleFin
              ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin)
              (order parameter) (order parameter).size (attempts parameter)))
          (generator parameter)).run) := by
  let input := pairEncoding unaryEncoding (optionEncoding binaryEncoding)
  have hp := isPolyTime_fst unaryEncoding (optionEncoding binaryEncoding)
  have hr := isPolyTime_snd unaryEncoding (optionEncoding binaryEncoding)
  have hnonce := hr.option_getD (fallback := fun _ => 0) (isPolyTime_const input [])
  have hs : IsPolyTime input (fun pair => finEquivEncoding (scalar pair.1)
      (scalarOfNat scalar pair.1 (pair.2.getD 0))) :=
    IsPolyTime.finEquiv_decode scalar (horder.comp_encoded hp) hnonce (hzero.comp_encoded hp)
  have hpublic : IsPolyTime input (fun pair => element pair.1
      (scalarOfNat scalar pair.1 (pair.2.getD 0) • generator pair.1)) := by
    apply hsmul.comp_encoded (f := fun pair : ℕ × Option ℕ =>
      ⟨pair.1, scalarOfNat scalar pair.1 (pair.2.getD 0), generator pair.1⟩)
    apply hp.sigma
    exact hs.pair (left := wordEncoding) (right := wordEncoding) (hgenerator.comp_encoded hp)
  have hpost : IsPolyTime input (fun pair =>
      optionEncoding (pairEncoding (element pair.1) (finEquivEncoding (scalar pair.1)))
        (pair.2.map (fun nonce =>
          (scalarOfNat scalar pair.1 nonce • generator pair.1,
            scalarOfNat scalar pair.1 nonce)))) := by
    have h := hr.option_isSome.cond
      (hpublic.pair (left := wordEncoding) (right := wordEncoding) hs).option_some
      (isPolyTime_const input [])
    convert h using 1
    funext pair
    cases pair.2 <;> rfl
  have h := (isPPT_sampleFin_size (Oracle := Oracle) horder hattempts).map_with
    (output := wordEncoding) (f := fun parameter nonce =>
      optionEncoding (pairEncoding (element parameter) (finEquivEncoding (scalar parameter)))
        (nonce.map (fun nonce =>
          (scalarOfNat scalar parameter nonce • generator parameter,
            scalarOfNat scalar parameter nonce))))
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost)
  convert h using 1
  funext parameter
  simp only [keygen, ← map_eq_pure_bind, OptionT.run_map]
  simp only [OptionT.run, OptionT.mk, ← comp_map, Function.comp_def]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some value => simp [scalarOfNat_val]

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
/-- The response uses one certified field multiplication and one certified addition. -/
theorem isPolyTime_respond (scalar : ∀ parameter, F parameter ↪ Word)
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (scalar parameter) (scalar parameter)))
      (fun value => scalar value.1 (value.2.1 + value.2.2)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (scalar parameter) (scalar parameter)))
      (fun value => scalar value.1 (value.2.1 * value.2.2))) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (scalar parameter) (pairEncoding (scalar parameter) (scalar parameter))))
      (fun input => scalar input.1 (respond input.2.1 input.2.2.1 input.2.2.2)) := by
  unfold respond
  polytime

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
/-- Special-soundness extraction has a uniform certificate from field subtraction and division.
The caller still checks distinct challenges before using the extracted value. -/
theorem isPolyTime_extract (scalar : ∀ parameter, F parameter ↪ Word)
    (hsub : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (scalar parameter) (scalar parameter)))
      (fun value => scalar value.1 (value.2.1 - value.2.2)))
    (hdiv : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (scalar parameter) (scalar parameter)))
      (fun value => scalar value.1 (value.2.1 / value.2.2))) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (pairEncoding (scalar parameter) (scalar parameter))
        (pairEncoding (scalar parameter) (scalar parameter))))
      (fun input => scalar input.1 (extract input.2.1.1 input.2.1.2 input.2.2.1 input.2.2.2)) := by
  unfold extract
  polytime

omit [MeasurableSpace Word] [DiscreteMeasurableSpace Word] in
/-- Transcript verification uses certified scalar multiplication and addition, and compares
the resulting group encodings. It needs no additional group-equality primitive. -/
theorem isPolyTime_accepts [∀ parameter, DecidableEq (G parameter)]
    (scalar : ∀ parameter, F parameter ↪ Word) (element : ∀ parameter, G parameter ↪ Word)
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (scalar parameter) (element parameter)))
      (fun value => element value.1 (value.2.1 • value.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (element parameter) (element parameter)))
      (fun value => element value.1 (value.2.1 + value.2.2))) :
    IsPolyTime (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (element parameter) (pairEncoding (element parameter)
        (pairEncoding (element parameter) (pairEncoding (scalar parameter) (scalar parameter))))))
      (fun input => boolEncoding (decide (Accepts input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2))) := by
  let input := sigmaEncoding unaryEncoding (fun parameter =>
    pairEncoding (element parameter) (pairEncoding (element parameter)
      (pairEncoding (element parameter) (pairEncoding (scalar parameter) (scalar parameter)))))
  have ha := isPolyTime_input input
  have hp := ha.sigma_fst
  have hg : IsPolyTime input (fun arg => element arg.1 arg.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using ha.sigma_snd.bitPair_fst
  have hpk : IsPolyTime input (fun arg => element arg.1 arg.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_fst
  have hcommit : IsPolyTime input (fun arg => element arg.1 arg.2.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_snd.bitPair_fst
  have hc : IsPolyTime input (fun arg => scalar arg.1 arg.2.2.2.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode, List.BitPair.fst_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_snd.bitPair_snd.bitPair_fst
  have hz : IsPolyTime input (fun arg => scalar arg.1 arg.2.2.2.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using
      ha.sigma_snd.bitPair_snd.bitPair_snd.bitPair_snd.bitPair_snd
  have hleft : IsPolyTime input (fun arg => element arg.1 (arg.2.2.2.2.2 • arg.2.1)) := by
    apply hsmul.comp_encoded (f := fun arg : Σ n, G n × G n × G n × F n × F n =>
      ⟨arg.1, arg.2.2.2.2.2, arg.2.1⟩)
    apply hp.sigma
    exact hz.pair (left := wordEncoding) (right := wordEncoding) hg
  have hchallenge : IsPolyTime input
      (fun arg => element arg.1 (arg.2.2.2.2.1 • arg.2.2.1)) := by
    apply hsmul.comp_encoded (f := fun arg : Σ n, G n × G n × G n × F n × F n =>
      ⟨arg.1, arg.2.2.2.2.1, arg.2.2.1⟩)
    apply hp.sigma
    exact hc.pair (left := wordEncoding) (right := wordEncoding) hpk
  have hright : IsPolyTime input
      (fun arg => element arg.1 (arg.2.2.2.1 + arg.2.2.2.2.1 • arg.2.2.1)) := by
    apply hadd.comp_encoded (f := fun arg : Σ n, G n × G n × G n × F n × F n =>
      ⟨arg.1, arg.2.2.2.1, arg.2.2.2.2.1 • arg.2.2.1⟩)
    apply hp.sigma
    exact hcommit.pair (left := wordEncoding) (right := wordEncoding) hchallenge
  convert hleft.beq hright using 1
  funext arg
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, (element arg.1).injective.eq_iff]
  exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩

end Cslib.Crypto.Schnorr
