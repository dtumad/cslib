/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.ElGamal.Asymptotic
public import Cslib.Foundations.Data.PFunctor.Resumption.Uniform

/-!
# ElGamal encryption over fair coins

With fair coins as the only source of randomness, the algorithms (group generators, eavesdroppers
and distinguishers) are free programs of coin flips, which always terminate. The experiments are
resumptions over the same coins: sampling an exponent exactly uniformly needs rejection sampling,
which returns almost surely but within no bound on the number of flips
(`PFunctor.Resumption.uniformFin`). Free programs lift to resumptions, and one semantics, answering
every flip with a fair coin, interprets both.

Every hypothesis of the asymptotic analysis then holds. At every security parameter, the advantage
of an eavesdropper is the advantage of its reduction (`ElGamal.eavAdvantage_eq_ddhAdvantage_coins`),
so ElGamal is secure against the eavesdroppers whose reductions are admissible, if DDH is hard
against admissible distinguishers (`ElGamal.eavSecure_of_ddhHard_coins`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory PFunctor

namespace Cslib.Crypto.ElGamal

variable (𝒢 : GroupGen coinOracle.FreeM)

/-- The advantage of an eavesdropper flipping fair coins against ElGamal, with exponents sampled by
rejection, is the advantage of its reduction at every security parameter. -/
theorem eavAdvantage_eq_ddhAdvantage_coins
    (A : (scheme 𝒢 Resumption.uniformFin).EavAdversary coinOracle.FreeM) (n : ℕ) :
    (scheme 𝒢 Resumption.uniformFin).eavAdvantage (·.toMeasure fairCoins) FreeM.coin A n =
      𝒢.ddhAdvantage (·.toMeasure fairCoins) Resumption.uniformFin (reduction FreeM.coin A) n :=
  eavAdvantage_eq_ddhAdvantage _ (Resumption.isMeasureSemantics_toMeasure fairCoins)
    Resumption.toMeasure_uniformFin (by simp) A n

/-- Over fair coins, if DDH is hard relative to `𝒢` against admissible distinguishers, ElGamal is
secure against the eavesdroppers whose reductions are admissible. -/
theorem eavSecure_of_ddhHard_coins
    {Admissible : (scheme 𝒢 Resumption.uniformFin).EavAdversary coinOracle.FreeM → Prop}
    {AdmissibleDDH : 𝒢.DDHAdversary → Prop}
    (hreduction : ∀ A, Admissible A → AdmissibleDDH (reduction FreeM.coin A))
    (hddh : 𝒢.DDHHard (·.toMeasure fairCoins) Resumption.uniformFin AdmissibleDDH) :
    (scheme 𝒢 Resumption.uniformFin).EavSecure (·.toMeasure fairCoins) FreeM.coin Admissible :=
  eavSecure_of_ddhHard _ (Resumption.isMeasureSemantics_toMeasure fairCoins)
    Resumption.toMeasure_uniformFin (by simp) hreduction hddh

end Cslib.Crypto.ElGamal
