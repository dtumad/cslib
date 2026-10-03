<pre>
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
</pre>

# Computational cryptography

This directory proves that **general one-way functions imply pseudorandom generators**, against
uniform probabilistic polynomial-time (PPT) adversaries. Games use ordinary Lean `do` notation.
Efficiency is a separate, proved contract backed by CSLib's Turing machines; cryptographic
arguments compose programs without manipulating tapes or machine configurations.

Start with the checked [walkthrough](../../../CslibTests/ComputationalCryptoDemo.lean), the
[programming examples](../../../CslibTests/ComputationalCryptoPrograms.lean), and the
[reduction examples](../../../CslibTests/ComputationalCryptoReductions.lean).

## The main theorem

```lean
import Cslib.Crypto.Computational.OneWayToPRG

open Cslib.Probability Cslib.Crypto

example {f : Word → Word} (hf : OneWay f) :
    ∃ generator : Word → Word, PseudorandomGenerator generator (fun n => n + 1) :=
  hf.exists_pseudorandomGenerator
```

`OneWay f` includes deterministic polynomial-time evaluation and negligible inversion success
against every uniform PPT inverter. Any preimage counts as successful inversion. The conclusion
includes deterministic polynomial-time generation, exactly one extra bit at **every** seed length,
and computational indistinguishability from uniform. Existence of a one-way function remains an
assumption. Entropy estimates, efficient samplers, and reductions are proved internally.

The [top-level proof](OneWayToPRG.lean) is three lines: obtain a pseudoentropy pair, then apply
the pseudoentropy-to-PRG theorem with a sufficiently fine polynomial grid. The construction follows
[Holenstein's write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf), Sections 4–5,
which simplifies the [Håstad–Impagliazzo–Levin–Luby theorem](https://doi.org/10.1137/S0097539793244708).
We prove polynomial efficiency without claiming the write-up's optimized seed-length exponent
or practical cryptographic performance.

[`PseudorandomGenerator.amplify`](Stretch.lean) extends one-bit stretch to any efficiently computed
output length strictly larger than the seed length. The simpler permutation construction remains
available as [`OneWayPermutation.pseudorandomGenerator`](GoldreichLevin/HardCore.lean): its explicit
`GoldreichLevin.generator f` retains the seed's spare bit and handles odd lengths directly.

## Reading the general proof

| Stage | Entry point | What is proved |
| --- | --- | --- |
| OWF to pseudoentropy | [Pseudoentropy/OneWay](Pseudoentropy/OneWay.lean) | Output normalization, hashed parity, and a uniform prediction-to-inversion reduction give a samplable pair with gap `1 / (2 * (n + 7))`. |
| Uniform hard-core argument | [Pseudoentropy/DenseMask](Pseudoentropy/DenseMask.lean) | A bounded soft mask exists even against indexed tests, using a certified boosting and empirical-selection procedure. |
| Repetition and extraction | [Pseudoentropy/ThreeSource](Pseudoentropy/ThreeSource.lean) | Three game transitions extract the public observation, hidden labels, and retained sampler coins with a common repetition schedule. |
| Deterministic implementation | [ThreeSource/Seeded](Pseudoentropy/ThreeSource/Seeded.lean) | Saved coins and three matrix seeds realize the extractor exactly, with proved output length and polynomial runtime. |
| Entropy guesses | [EntropyGrid](Pseudoentropy/EntropyGrid.lean), [Candidates](Pseudoentropy/ThreeSource/Candidates.lean) | Polynomially many explicit integer guesses all expand; one choice is secure against every uniform indexed test. |
| Padding, amplification, XOR | [Padding](Pseudoentropy/ThreeSource/Padding.lean), [Amplification](Pseudoentropy/ThreeSource/Amplification.lean), [Combined](Pseudoentropy/ThreeSource/Combined.lean) | Every candidate gets a common seed width and enough stretch to pay for independent seed blocks. XOR yields one secure expanding family. |
| Every input length | [GeneratorReindex](GeneratorReindex.lean) | Bounded search selects a family member that fits and preserves unused seed bits; the security proof remains uniform. |
| Assembly | [Pseudoentropy/Generator](Pseudoentropy/Generator.lean), [OneWayToPRG](OneWayToPRG.lean) | The complete implication, using the same PRG contract as the permutation theorem. |

The generator computes the entire entropy grid. The mathematically successful candidate is used
only in the security proof. Its choice is never advice to the generator.

Length conversion also needs care about uniformity. A seed-length schedule can be irregular;
`GeneratorReindex.parameter` uses `Nat.findGreatest` to select the largest parameter whose seed
fits. Its next parameter supplies a polynomial bound on the original input length.
[`UniformChoice`](UniformChoice.lean) controls all possible padding tests simultaneously: sample
an index, then use fresh real-or-ideal reference data to calibrate its answer. If the indexed
advantages are `δᵢ`, the reduction has advantage `Σ δᵢ² / M`, where `M` is the dyadic sampling
range. Squaring prevents cancellation. Efficient sampling is an explicit hypothesis of this
closure theorem, and no best index or sign is supplied as advice.

For the smaller permutation proof, read [HardCore](HardCore.lean), then
[GoldreichLevin/Decoding](GoldreichLevin/Decoding.lean),
[Reduction](GoldreichLevin/Reduction.lean), [Parameters](GoldreichLevin/Parameters.lean),
[WordReduction](GoldreichLevin/WordReduction.lean), and [HardCore](GoldreichLevin/HardCore.lean).
The finite recovery bound, efficient implementation, and asymptotic security argument are separate.

## Writing and certifying programs

```lean
import Cslib.Crypto.Computational.PseudorandomGenerator
import Cslib.Tactic.PPT

open Cslib Cslib.Probability Cslib.Crypto

noncomputable def realGame (generator : Word → Word) (adversary : Distinguisher)
    (n : ℕ) : ProbComp Bool := do
  let seed ← OracleComp.sampleBits n
  adversary n (generator seed)

theorem realGame_isPPT (generator : Word → Word) (adversary : Distinguisher)
    (hgenerator : IsPolyTime wordEncoding generator)
    (hadversary : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (fun n _ => realGame generator adversary n) := by
  unfold realGame
  ppt
```

`ProbComp.eval` gives the probability distribution. `noncomputable` permits the mathematical
sampling description; `IsPPT` separately supplies its exact machine realization. The example's
efficiency proof is independent of whether the generator is secure.

The [contracts](../../Computability/Probabilistic/PPT.lean) have three entry points:

- `IsPolyTime inputEncoding f` certifies a deterministic word-valued computation.
- `IsPPTOn inputEncoding outputEncoding program` supports typed inputs and results.
- `IsPPT outputEncoding adversary` specializes to a unary security parameter and auxiliary word.

[`polytime`](../../Tactic/PolyTime.lean) and [`ppt`](../../Tactic/PPT.lean) compose proved closure
rules. Supplied algorithms need their own certificates. The tactics support tuples, maps, filters,
folds, runtime word slicing, unary arithmetic, bounded search, sampling, and Boolean postprocessing.
[`Search`](../../Computability/Probabilistic/Search.lean) reuses certified list enumeration and
search to support ordinary `Nat.findGreatest`, including predicates with captured inputs.

For loops, use the interfaces in [Iteration](../../Computability/Probabilistic/Iteration.lean),
[Fold](../../Computability/Probabilistic/Fold.lean), and
[Adaptive](../../Computability/Probabilistic/Adaptive.lean). The `iterate_spec` and `foldl_spec`
contracts use one invariant to prove the postcondition and bound intermediate sizes. Captured
inputs are supported by `_with_spec`; bounded-growth rules derive the size invariant when
possible. Polynomially many iterations still require polynomially bounded intermediate states.

[`OracleComp.replicate` and `countTrue`](../../Computability/Probabilistic/Repeat.lean) collect
independent runs and count successes. [Concentration](../../Languages/Probabilistic/Concentration.lean)
bounds empirical errors; [selection](../../Computability/Probabilistic/Selection.lean) compares
candidates with a proved accuracy guarantee. These programs use natural counters. Real-valued
probability and entropy calculations occur in their correctness proofs.

The [adaptive examples](../../../CslibTests/ComputationalCryptoIteration.lean) exercise random
state updates, stopping after failure, and input-dependent sampling precision. The size invariant
holds on every execution. Separate correctness invariants may carry per-round failure bounds;
`ProbComp.iterate_failure_toReal_le` adds them without an independence assumption.

## Security interfaces

Cryptographic notions live in `Cslib.Crypto`; efficiency predicates and encodings live in
`Cslib.Probability`.

| Interface | Purpose |
| --- | --- |
| [Game](../Game.lean), [Basic](Basic.lean) | `Negligible`, acceptance probability, advantage, and computational indistinguishability. |
| [Reduction](Reduction.lean) | Certified deterministic and randomized postprocessing. |
| [Hybrid](Hybrid.lean), [Game/Hybrid](../Game/Hybrid.lean) | Game hops, polynomial reduction losses, and reindexing negligible bounds. |
| [Statistical](Statistical.lean) | Negligible statistical distance implies computational security. |
| [OneWay](OneWay.lean), [HardCore](HardCore.lean) | Inversion and prediction games. |
| [PseudorandomGenerator](PseudorandomGenerator.lean) | Efficient generation, output length, expansion, and the shared `PRG.Family.Secure` property. |
| [PseudorandomFunction](PseudorandomFunction.lean) | Adaptive oracle games with fixed-width keys, queries, and answers. |

A closed game is a `ProbComp Bool`. Advantage is the absolute difference of acceptance
probabilities, without the factor of one half used for guessing a challenge bit. Negligibility
is Mathlib's superpolynomial decay. Each entire uniform adversary is quantified before its
negligible bound; that bound may depend on the adversary.

One-wayness, hard-core security, PRGs, and PRFs use `Game.Secure`. The semantic and computational
PRG interfaces share experiments and advantage exactly. `PseudorandomGenerator` has named
`polyTime`, `length_eq`, `stretch`, and `secure` fields. Use `.of_indistinguishable` to assemble
these obligations and `.indistinguishable` to recover program-based security.

General indistinguishability does not require efficient sampling or polynomial sample lengths.
[Ensemble](Ensemble.lean) provides the latter condition separately. For polynomial hybrid
arguments, one negligible bound must cover all relevant hops at each parameter. Negligibility
for each fixed hop alone is insufficient. Random-hop reductions and `ComputationallyIndistinguishable.uniform_bound`
provide uniform bounds under their respective hypotheses.

## What the machine certificate guarantees

`Word` is `List Bool`; finite probability arguments also use `BitString n = Fin n → Bool`.
Input encodings set the size measure, and output encodings are injective. `pairEncoding` and
`listEncoding` charge for complete encoded data. The standard adversary input is a unary
parameter, a delimiter, and an auxiliary word.

A certificate provides one finite-control machine and one polynomial clock for all inputs.
Time is strict polynomial time for every coin sequence, measured in the full encoded input
length. Sampling is implemented with fair bits and agrees exactly with the program distribution.
Arbitrary PMFs may describe games but require efficiency proofs when used by algorithms.

Start with [PPT](../../Computability/Probabilistic/PPT.lean),
[Clock](../../Computability/Probabilistic/Clock.lean), and
[CoinTape](../../Computability/Probabilistic/CoinTape.lean) for these guarantees.
[Realization](../../Computability/Probabilistic/Realization) contains the implementations, reusing
CSLib's [multi-tape architecture](../../Computability/Machines/Turing/MultiTape).

## Oracles and remaining framework work

`OracleComp Query Response α` supports adaptive queries, dependent responses, and shared hidden
state. [`IsOraclePPTOn`](../../Computability/Probabilistic/Oracle.lean) handles finitely many
operation names with word payloads; its realization preserves the joint result and final state
for every stateful handler. Local computation and query writing/reading are charged; the oracle's
internal work is external. [OracleEncoding](../../Computability/Probabilistic/OracleEncoding.lean)
connects typed interfaces to words and charges for encoding and decoding, including malformed
replies.

General stateful oracle sequencing still needs additional machine plumbing. The closed-program
composition rules cannot simply be reused: an extra call can change observable oracle state.
The [machine examples](../../../CslibTests/ComputationalCryptoMachines.lean) include a typed
multi-operation program and a shared lazy cache. A reusable random-oracle theory and an eager/lazy
equivalence theorem remain future work. The OWF-to-PRG theorem uses closed programs.

The pseudoentropy proof uses fresh soft masks. Reproducing the write-up's set-oracle presentation
would additionally require cached membership simulation; the proved uniform reduction uses its
explicit soft-mask formulation.

## Sources

- Johan Håstad, Russell Impagliazzo, Leonid Levin, and Michael Luby,
  *A Pseudorandom Generator from Any One-Way Function*, SIAM Journal on Computing 28(4), 1999.
  [Original theorem](https://doi.org/10.1137/S0097539793244708).
- Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006. [Write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
  Section 3.3 supplies the collision proof of leftover hashing; Sections 4–5 guide the construction.
- Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2.
  [Uniform hard-core argument](https://crypto.ethz.ch/publications/files/Holens05.pdf).

Individual modules cite Arora–Barak and Boneh–Shoup for security definitions, and Goldreich–Levin
with Trevisan's lecture notes for decoding. The
[probabilistic language](../../Languages/Probabilistic/Basic.lean) credits VCVio for the related
separation of oracle syntax and interpretation. The [Crypto overview](../README.md) records
machine reuse and port provenance.
