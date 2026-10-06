/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Assumptions.DDH
public import Cslib.Crypto.Assumptions.GroupGen
public import Cslib.Foundations.Control.Monad.MeasureSemantics
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Asymptotic decisional Diffie–Hellman

A distinguisher (`GroupGen.DDHAdversary`) tests triples of elements of the groups sampled by a
group generator. The decisional Diffie–Hellman assumption relative to a generator
(`GroupGen.DDHHard`) states that every admissible distinguisher has negligible advantage in telling
Diffie–Hellman triples from triples with an independent third exponent.

Group generation and distinguishers are algorithms, programs in a monad `m₀`. The experiments are
programs in a monad `m` into which `m₀` lifts, given a sampler `uniform k` of each `Fin k`, so
that the algorithms may use fewer resources than the experiments, such as only fair coins.
Advantages are measured under a semantics `sem` of `m`. As for pseudorandom generators
(`Cslib.Crypto.PRG.Family.Secure`), admissibility is a predicate on whole distinguishers, so that a
computational model can restrict their resources.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

open MeasureTheory Filter

namespace Cslib.Crypto

namespace GroupGen

variable {m₀ : Type → Type*} (𝒢 : GroupGen m₀)

/-- A distinguisher: for each security parameter and group description, a test of a triple of
elements, a program in `m₀`. -/
abbrev DDHAdversary := ℕ → (d : 𝒢.Desc) → 𝒢.Elem d → 𝒢.Elem d → 𝒢.Elem d → m₀ Bool

variable {m : Type → Type*} [Monad m] [MonadLiftT m₀ m]
  (sem : ∀ {α : Type} [MeasurableSpace α], m α → Measure α) (uniform : (k : ℕ+) → m (Fin k))

/-- Run the distinguisher on a Diffie–Hellman triple in a sampled group. -/
def ddhReal (D : 𝒢.DDHAdversary) (n : ℕ) : m Bool := do
  let d ← monadLift (𝒢.setup n)
  DDH.realExperiment (uniform (𝒢.order d)) (𝒢.gen d) fun a b c => monadLift (D n d a b c)

/-- Run the distinguisher on a triple with an independent third exponent in a sampled group. -/
def ddhIdeal (D : 𝒢.DDHAdversary) (n : ℕ) : m Bool := do
  let d ← monadLift (𝒢.setup n)
  DDH.idealExperiment (uniform (𝒢.order d)) (𝒢.gen d) fun a b c => monadLift (D n d a b c)

/-- The advantage of the distinguisher in telling the two experiments apart at the security
parameter `n`. -/
noncomputable def ddhAdvantage (D : 𝒢.DDHAdversary) (n : ℕ) : ℝ :=
  |(sem (𝒢.ddhReal uniform D n)).real {true} - (sem (𝒢.ddhIdeal uniform D n)).real {true}|

/-- The decisional Diffie–Hellman assumption relative to `𝒢`: every admissible distinguisher has
negligible advantage. -/
def DDHHard (Admissible : 𝒢.DDHAdversary → Prop) : Prop :=
  ∀ D, Admissible D →
    Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) (𝒢.ddhAdvantage sem uniform D)

end GroupGen

end Cslib.Crypto
