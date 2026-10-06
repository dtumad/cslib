/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Assumptions.DDH.Asymptotic
public import Cslib.Crypto.Primitives.ElGamal.Security
public import Cslib.Crypto.Primitives.PKE.Defs

/-!
# Asymptotic security of ElGamal encryption

ElGamal encryption over a group generator `𝒢` (`ElGamal.scheme`) is a public-key encryption
scheme whose public key is a sampled group description with an element of the group. It is
correct (`ElGamal.isCorrect`).

From an eavesdropper `A`, the distinguisher `ElGamal.reduction coin A` plays the challenge phase
with `A` on a triple `(pk, head, mask)`, encrypting the chosen message as `(head, message * mask)`
and keeping the public key in the state of `A`. At every security parameter, the advantage of `A`
is the advantage of the reduction (`ElGamal.eavAdvantage_eq_ddhAdvantage`), given uniform samplers
and coin, and algorithms, such as the group generator and the eavesdropper, that return almost
surely. Hence ElGamal is secure against the eavesdroppers whose reductions are admissible, if DDH is
hard against those (`ElGamal.eavSecure_of_ddhHard`). A computational model can take both
predicates to be efficiency.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Cslib.Crypto.ElGamal

variable {m₀ : Type → Type*} (𝒢 : GroupGen m₀) {m : Type → Type*} [Monad m] [MonadLiftT m₀ m]
  (uniform : (k : ℕ+) → m (Fin k))

/-- ElGamal encryption over the groups sampled by `𝒢`, with exponents sampled by `uniform`. Its
keys, messages and ciphertexts unfold to group elements. -/
abbrev scheme : PKE m where
  PK := Σ d, 𝒢.Elem d
  SK pk := Fin (𝒢.order pk.1)
  Msg pk := 𝒢.Elem pk.1
  Ctxt pk := 𝒢.Elem pk.1 × 𝒢.Elem pk.1
  gen n := do
    let d ← monadLift (𝒢.setup n)
    let (h, x) ← keygen (uniform (𝒢.order d)) (𝒢.gen d)
    pure ⟨⟨d, h⟩, x⟩
  enc pk message := encrypt (uniform (𝒢.order pk.1)) (𝒢.gen pk.1) pk.2 message
  dec _ x c := some (decrypt x c)

theorem isCorrect [LawfulMonad m] : (scheme 𝒢 uniform).IsCorrect := by
  intro n message
  simp [scheme, keygen, encrypt]

variable {𝒢 uniform} [Monad m₀] (coin : m₀ Bool)

/-- The distinguisher playing the challenge phase with `A` on a triple `(pk, head, mask)`,
encrypting the chosen message as `(head, message * mask)`. It keeps the public key in the state
of `A`. -/
def reduction (A : (scheme 𝒢 uniform).EavAdversary m₀) : 𝒢.DDHAdversary :=
  fun n d => ddhReduction coin
    (fun pk => (fun r => (r.1, r.2.1, (r.2.2, pk))) <$> A.choose n ⟨d, pk⟩)
    (fun state c => A.guess n state.1 ⟨d, state.2⟩ c)

variable [LawfulMonad m] [LawfulMonad m₀] [LawfulMonadLiftT m₀ m]

/-- The eavesdropping experiment against ElGamal samples a group and plays the chosen-plaintext
experiment in it. -/
theorem eavExp_scheme (A : (scheme 𝒢 uniform).EavAdversary m₀) (n : ℕ) :
    (scheme 𝒢 uniform).eavExp coin A n = monadLift (𝒢.setup n) >>= fun d =>
      cpaExperiment (uniform (𝒢.order d)) (monadLift coin) (𝒢.gen d)
        (fun pk => monadLift ((fun r => (r.1, r.2.1, (r.2.2, pk))) <$> A.choose n ⟨d, pk⟩))
        (fun state c => monadLift (A.guess n state.1 ⟨d, state.2⟩ c)) := by
  simp [PKE.eavExp, scheme, cpaExperiment, challenge, keygen, encrypt]

variable {sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α}
  (hsem : IsMeasureSemantics m sem) (huniform : ∀ k, sem (uniform k) = uniformOn Set.univ)
  (hcoin : sem (monadLift coin : m Bool) = uniformOn Set.univ)
  [∀ {α : Type} [MeasurableSpace α] (x : m₀ α), IsProbabilityMeasure (sem (monadLift x : m α))]
include hsem huniform hcoin

/-- The advantage of an eavesdropper against ElGamal is the advantage of its reduction at every
security parameter. -/
theorem eavAdvantage_eq_ddhAdvantage (A : (scheme 𝒢 uniform).EavAdversary m₀) (n : ℕ) :
    (scheme 𝒢 uniform).eavAdvantage sem coin A n =
      𝒢.ddhAdvantage sem uniform (reduction coin A) n := by
  have hreal : sem ((scheme 𝒢 uniform).eavExp coin A n) =
      sem (𝒢.ddhReal uniform (reduction coin A) n) := by
    rw [eavExp_scheme, GroupGen.ddhReal, hsem.map_bind_of_discrete, hsem.map_bind_of_discrete]
    congr 1
    funext d
    simp only [reduction, map_ddhReduction IsMonadHom.monadLiftT]
    exact (sem_realExperiment_ddhReduction hsem _ _ _ _ _).symm
  have hideal : sem (𝒢.ddhIdeal uniform (reduction coin A) n) = uniformOn Set.univ := by
    rw [GroupGen.ddhIdeal, hsem.map_bind_of_discrete]
    simp only [reduction, map_ddhReduction IsMonadHom.monadLiftT]
    simp only [sem_idealExperiment_ddhReduction hsem _ _ _ _ _ (𝒢.bijective_pow _) (huniform _)
      hcoin, Measure.bind_const, measure_univ, one_smul]
  rw [PKE.eavAdvantage, GroupGen.ddhAdvantage, hreal, hideal]
  congr 2
  rw [measureReal_def, uniformOn_univ]
  simp

/-- If DDH is hard relative to `𝒢` against admissible distinguishers, ElGamal is secure against
the eavesdroppers whose reductions are admissible. -/
theorem eavSecure_of_ddhHard {Admissible : (scheme 𝒢 uniform).EavAdversary m₀ → Prop}
    {AdmissibleDDH : 𝒢.DDHAdversary → Prop}
    (hreduction : ∀ A, Admissible A → AdmissibleDDH (reduction coin A))
    (hddh : 𝒢.DDHHard sem uniform AdmissibleDDH) :
    (scheme 𝒢 uniform).EavSecure sem coin Admissible := fun A hA => by
  simpa only [funext (eavAdvantage_eq_ddhAdvantage coin hsem huniform hcoin A)] using
    hddh _ (hreduction A hA)

end Cslib.Crypto.ElGamal
