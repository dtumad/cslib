/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Security
public import Cslib.Foundations.Analysis.SuperpolynomialDecay

/-!
# Asymptotic security of Schnorr signatures

A Schnorr family (`Schnorr.Family`) gives, for each security parameter, a group presented as a
module over a finite field of scalars, with a generator. Relative to it, the discrete-logarithm
assumption (`Family.DLHard`) and existential unforgeability under chosen-message attacks in the
random-oracle model (`Family.EufCmaSecure`) are stated against admissible algorithms, as for
pseudorandom generators (`Cslib.Crypto.PRG.Family.Secure`). Algorithms are free programs whose
operations, other than hash and signing queries, are answered by fixed measures `μ`.

Schnorr signatures are secure against admissible forgers (`Family.eufCmaSecure_of_dlHard`) if DL
is hard against admissible solvers, the forking reduction (`Family.reduction`) maps admissible
forgers to admissible solvers, admissible forgers make polynomially many queries
(`Family.QueryBounded`), and the inverse number of scalars is negligible. A computational model
can take admissibility to be efficiency; the hypothesis on the reduction then states that forking
an efficient forger is efficient.
-/

@[expose] public section

namespace Cslib.Crypto.Schnorr

open PFunctor MeasureTheory ProbabilityTheory Filter Asymptotics

/-- A family of groups for Schnorr signatures: for each security parameter, a group presented as
a module over a finite field of scalars, with a generator. -/
structure Family where
  /-- The scalars. -/
  Scalar : ℕ → Type
  /-- The elements of the group. -/
  Elem : ℕ → Type
  [field : ∀ n, Field (Scalar n)]
  [finite : ∀ n, Finite (Scalar n)]
  [decidableEqScalar : ∀ n, DecidableEq (Scalar n)]
  [addCommGroup : ∀ n, AddCommGroup (Elem n)]
  [module : ∀ n, Module (Scalar n) (Elem n)]
  [decidableEqElem : ∀ n, DecidableEq (Elem n)]
  /-- The generator. -/
  gen : ∀ n, Elem n
  /-- Each element is exactly one scalar multiple of the generator. -/
  bijective_smul : ∀ n, Function.Bijective fun scalar : Scalar n => scalar • gen n

namespace Family

attribute [instance] field finite decidableEqScalar addCommGroup module decidableEqElem

variable (𝒮 : Family)

instance (n : ℕ) : MeasurableSpace (𝒮.Scalar n) := ⊤

instance (n : ℕ) : DiscreteMeasurableSpace (𝒮.Scalar n) := ⟨fun _ => trivial⟩

instance (n : ℕ) : MeasurableSpace (𝒮.Elem n) := ⊤

instance (n : ℕ) : DiscreteMeasurableSpace (𝒮.Elem n) := ⟨fun _ => trivial⟩

instance (n : ℕ) : Finite (𝒮.Elem n) := .of_surjective _ (𝒮.bijective_smul n).2

/-- A discrete-logarithm solver: for each security parameter, a free program over `P` given a
public key. -/
abbrev DLAdversary (P : PFunctor.{0, 0}) := ∀ n, 𝒮.Elem n → P.FreeM (Option (𝒮.Scalar n))

/-- A forger: for each security parameter, a free program over `P` that makes hash and signing
queries and outputs a message with a signature. -/
abbrev Forger (P : PFunctor.{0, 0}) (M : Type) :=
  ∀ n, 𝒮.Elem n →
    (signatureEffects P M (𝒮.Elem n) (𝒮.Scalar n)).FreeM (M × 𝒮.Elem n × 𝒮.Scalar n)

variable {P : PFunctor.{0, 0}} {M : Type} [DecidableEq M]

/-- The forging adversary makes polynomially many signing and hash queries. -/
def QueryBounded (A : 𝒮.Forger P M) : Prop :=
  ∃ qS qH : ℕ → ℕ, PolynomiallyBounded qS ∧ PolynomiallyBounded qH ∧ ∀ n pk,
    FreeM.queryBoundP isSignQuery (A n pk) ≤ qS n ∧ FreeM.queryBoundP isHashQuery (A n pk) ≤ qH n

/-- The forking reduction at every security parameter. -/
def reduction (sample : ∀ n, P.FreeM (𝒮.Scalar n)) (A : 𝒮.Forger P M) : 𝒮.DLAdversary P :=
  fun n => dlogReduction (sample n) (𝒮.gen n) (A n)

variable [∀ op, MeasurableSpace (P.B op)] (μ : (op : P.A) → Measure (P.B op))
  (sample : ∀ n, P.FreeM (𝒮.Scalar n))

/-- The discrete-logarithm assumption relative to `𝒮`: every admissible solver finds the
logarithm of a uniform public key with negligible probability. -/
def DLHard (Admissible : 𝒮.DLAdversary P → Prop) : Prop :=
  ∀ A, Admissible A → SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) fun n =>
    (FreeM.toMeasure (DiscreteLog.experiment (sample n) (𝒮.gen n) (A n)) μ {true}).toReal

/-- Existential unforgeability of Schnorr signatures under chosen-message attacks, in the
random-oracle model: every admissible forger succeeds with negligible probability. -/
def EufCmaSecure (Admissible : 𝒮.Forger P M → Prop) : Prop :=
  ∀ A, Admissible A → SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) fun n =>
    (FreeM.toMeasure (unforgeabilityExperiment (sample n) (𝒮.gen n) (A n)) μ {true}).toReal

/-- Schnorr signatures are secure against admissible forgers making polynomially many queries,
if DL is hard against admissible solvers and forking an admissible forger is admissible. -/
theorem eufCmaSecure_of_dlHard [Countable P.A] [∀ op, MeasurableSingletonClass (P.B op)]
    [∀ op, Countable (P.B op)] [∀ op, IsProbabilityMeasure (μ op)] [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M]
    (hsample : ∀ n, FreeM.toMeasure (sample n) μ = uniformOn Set.univ)
    (hcard : SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))
      fun n => ((Nat.card (𝒮.Scalar n) : ℝ))⁻¹)
    {Admissible : 𝒮.Forger P M → Prop} {AdmissibleDL : 𝒮.DLAdversary P → Prop}
    (hreduction : ∀ A, Admissible A → AdmissibleDL (𝒮.reduction sample A))
    (hqueries : ∀ A, Admissible A → 𝒮.QueryBounded A)
    (hdl : 𝒮.DLHard μ sample AdmissibleDL) : 𝒮.EufCmaSecure μ sample Admissible := by
  intro A hA
  obtain ⟨qS, qH, hqS, hqH, hq⟩ := hqueries A hA
  have hδ := hdl _ (hreduction A hA)
  have hbound := ((hcard.mul_polynomiallyBounded (count := fun n => qS n * (qH n + qS n))
    (by fun_prop)).add (hcard.mul_polynomiallyBounded (count := fun n => qH n + 1)
      (by fun_prop))).add (hδ.mul_polynomiallyBounded (count := fun n => qH n + 1)
        (by fun_prop)).sqrt
  refine hbound.trans_abs_le fun n => ?_
  simp only [Pi.add_apply]
  rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (by positivity)]
  refine (euf_cma_bound_sqrt μ (sample n) (𝒮.gen n) (A n) (𝒮.bijective_smul n) (hsample n)
    (qS n) (qH n) (fun pk => (hq n pk).1) (fun pk => (hq n pk).2)).trans_eq ?_
  simp only [reduction]
  push_cast
  ring_nf

end Family

end Cslib.Crypto.Schnorr
