/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal
public import Cslib.Computability.PolynomialTime.Sampling
import Cslib.Tactic.PolyTime

/-!
# Uniform efficiency of the ElGamal reduction

The reduction composes the two adversary phases with a fair bit and one group multiplication.
All certificates use the same group and private-state families for every security parameter.
The captured continuation retains the challenge and chosen messages, charging for their copying.
-/

public section

namespace Cslib.Crypto.ElGamal

open PFunctor Turing.MultiTapePTM Turing.MultiTapeTM

variable {G State : ℕ → Type} [∀ parameter, Group (G parameter)]
  {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- The actual DDH reduction preserves uniform PPT admissibility. Its only algebraic operation
is the certified multiplication; the adversary's private state keeps its original encoding. -/
theorem isPPT_ddhReduction
    (element : ∀ parameter, G parameter ↪ Word) (state : ∀ parameter, State parameter ↪ Word)
    (choose : ∀ parameter, G parameter → (effects Oracle).FreeM
      (G parameter × G parameter × State parameter))
    (guess : ∀ parameter, State parameter → G parameter × G parameter →
      (effects Oracle).FreeM Bool)
    (hchoose : IsPPT (sigmaEncoding unaryEncoding element) wordEncoding (fun input =>
      pairEncoding (element input.1) (pairEncoding (element input.1) (state input.1)) <$>
        choose input.1 input.2))
    (hguess : IsPPT (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (state parameter) (pairEncoding (element parameter) (element parameter))))
      boolEncoding (fun input => guess input.1 input.2.1 input.2.2))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun parameter => pairEncoding (element parameter) (element parameter)))
      (fun input => element input.1 (input.2.1 * input.2.2))) :
    IsPPT (sigmaEncoding unaryEncoding (fun parameter =>
      pairEncoding (element parameter) (pairEncoding (element parameter) (element parameter))))
      boolEncoding (fun input => ddhReduction coin (choose input.1) (guess input.1)
        input.2.1 input.2.2.1 input.2.2.2) := by
  let input := sigmaEncoding unaryEncoding (fun parameter =>
    pairEncoding (element parameter) (pairEncoding (element parameter) (element parameter)))
  let middle := fun value : Σ parameter, G parameter × G parameter × G parameter =>
    pairEncoding (element value.1) (pairEncoding (element value.1) (state value.1))
  have hfirst : IsPPT input wordEncoding (fun value =>
      middle value <$> choose value.1 value.2.1) :=
    hchoose.comp (f := fun value : Σ parameter, G parameter × G parameter × G parameter =>
      ⟨value.1, value.2.1⟩) (by polytime)
  unfold ddhReduction
  apply hfirst.bind_sigma
  apply (isPPT_coin (sigmaEncoding input middle)).bind_with
  have hsecond := hguess.comp (f := fun value :
      (Σ arg : Σ parameter, G parameter × G parameter × G parameter,
        G arg.1 × G arg.1 × State arg.1) × Bool =>
      ⟨value.1.1.1, value.1.2.2.2, value.1.1.2.2.1,
        (if value.2 then value.1.2.2.1 else value.1.2.1) * value.1.1.2.2.2⟩)
    (input := pairEncoding (sigmaEncoding input middle) boolEncoding) (by polytime)
  simp only [← map_eq_pure_bind]
  apply hsecond.map_with
  exact (isPolyTime_fst _ boolEncoding).snd.bool₂ (isPolyTime_snd _ boolEncoding) (· == ·)

end Cslib.Crypto.ElGamal
