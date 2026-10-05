/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Binary

/-!
# Computational security of binary ElGamal with encryption queries

Uniform DDH hardness implies negligible CPA bias for the actual bounded binary implementation.
Both adversary phases may make adaptive encryption requests. The reduction's machine is
constructed from their certificates, a canonical group parser, and the efficient group primitives.
The only approximation is two challenge draws, with explicit error `2 * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ`.
-/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor MeasureTheory ProbabilityTheory Turing.MultiTapePTM Turing.MultiTapeTM

variable {G State : ℕ → Type} [∀ n, Group (G n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, MeasurableSingletonClass (G n)]
  [∀ n, MeasurableSpace (State n)] [∀ n, MeasurableSingletonClass (State n)]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- Fully implemented ElGamal is CPA secure under uniform DDH. The attempt budget is efficiently
computed and at least the security parameter. Oracle exhaustion is an ordinary optional reply;
key and challenge exhaustion count as failure without conditioning or renormalization. -/
theorem negligible_cpaWordExperiment_of_ddh
    (element : ∀ n, Computability.Encoding (G n) Bool)
    (state : ∀ n, State n ↪ Word) (order attempts : ℕ → ℕ) [∀ n, NeZero (order n)]
    (g : ∀ n, G n)
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
    (hbudget : ∀ n, n ≤ attempts n)
    (hg : IsPolyTime unaryEncoding (fun n => (element n).encode (g n)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding (fun n =>
      pairEncoding (element n).toEmbedding (element n).toEmbedding))
      (fun arg => (element arg.1).encode (arg.2.1 * arg.2.2)))
    (hone : IsPolyTime unaryEncoding (fun n => (element n).encode 1))
    (hdecode : IsPolyTime (pairEncoding unaryEncoding wordEncoding) (fun arg =>
      optionEncoding (element arg.1).toEmbedding ((element arg.1).decode arg.2)))
    {size : ℕ → ℕ} (hpoly : PolynomiallyBounded size)
    (hsize : ∀ n (value : G n), ((element n).encode value).length ≤ size n)
    (hgenerator : ∀ n, Function.Bijective (fun x : Fin (order n) => g n ^ x.val))
    (hddh : Game.Secure
      (fun (test : (Σ n, G n × G n × G n) → (effects Empty).FreeM Bool) n =>
        (uniformOn (Set.univ : Set (Fin (order n)))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin (order n)))).bind (fun r =>
            FreeM.denote coinMeasure (test ⟨n, g n ^ x.val, g n ^ r.val,
              g n ^ (x.val * r.val)⟩))))
      (fun test n =>
        (uniformOn (Set.univ : Set (Fin (order n)))).bind (fun x =>
          (uniformOn (Set.univ : Set (Fin (order n)))).bind (fun r =>
            (uniformOn (Set.univ : Set (Fin (order n)))).bind (fun z =>
              FreeM.denote coinMeasure (test ⟨n, g n ^ x.val, g n ^ r.val, g n ^ z.val⟩)))))
      (IsPPT (sigmaEncoding unaryEncoding (fun n => pairEncoding (element n).toEmbedding
        (pairEncoding (element n).toEmbedding (element n).toEmbedding))) boolEncoding)) :
    Negligible (fun n => |(FreeM.denote coinMeasure
      (cpaWordExperiment (element n) (order n) (attempts n) (g n) (choose n) (guess n))
        {some true}).toReal - 1 / 2|) := by
  let sample n := FreeM.sampleFin
    ((fun bit => (⟨bit.toNat, Bool.toNat_lt bit⟩ : Fin 2)) <$> coin (Oracle := Empty))
      (order n) (order n).size (attempts n)
  let handler n pk := oracleHandler (fun _ : Unit =>
    encryptWord (element n) (sample n) (g n) pk)
  let test (arg : Σ n, G n × G n × G n) :=
    (ddhReduction coin (choose arg.1) (guess arg.1) arg.2.1 arg.2.2.1 arg.2.2.2).liftM
      (handler arg.1 arg.2.1)
  have htest := isPPT_ddhReduction_encryptWord (Target := Empty)
    element order attempts g state choose guess
    hchoose hguess horder hattempts hg hmul hone hdecode hpoly hsize
  have hsecurity := hddh test htest
  have herror : Negligible (fun n => (2 : ℝ) * (2⁻¹ : ℝ) ^ attempts n) :=
    negligible_sampling_error (draws := fun _ => 2) (by fun_prop) hbudget
  apply negligible_of_le (hsecurity.add herror) (fun _ => abs_nonneg _)
  intro n
  let : Countable (State n) := (state n).injective.countable
  let : Fintype (G n) := Fintype.ofEquiv (Fin (order n)) (Equiv.ofBijective _ (hgenerator n))
  let choose' pk := (fun out : G n × G n × State n => (out.1, out.2.1, (pk, out.2.2))) <$>
    (choose n pk).liftM (handler n pk)
  let guess' (saved : G n × State n) ciphertext :=
    (guess n saved.2 ciphertext).liftM (handler n saved.1)
  have hreduce (pk head mask : G n) :
      ddhReduction coin choose' guess' pk head mask = test ⟨n, pk, head, mask⟩ := by
    simp [test, ddhReduction, choose', guess', handler, FreeM.liftM_bind]
  have h := advantage_binary_le_ddh (order n) (attempts n) (g n) choose' guess' (hgenerator n)
  simpa only [cpaWordExperiment, sample, handler, choose', guess', hreduce, Pi.add_apply] using h

end Cslib.Crypto.ElGamal
