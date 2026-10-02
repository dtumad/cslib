<pre>
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
</pre>

# Computational cryptography

This directory defines security against uniform probabilistic polynomial-time (PPT) adversaries
and proves that one-way permutations imply pseudorandom generators. Games are probabilistic
programs written with ordinary Lean `do` notation. Efficiency is a separate, proved contract backed
by CSLib's Turing machines, so cryptographic arguments can compose algorithms without manipulating
tapes or machine configurations.

Start with the checked [walkthrough](../../../CslibTests/ComputationalCryptoDemo.lean). It moves
from sampling and game definitions to reductions, hybrid arguments, and the complete one-bit PRG
construction. The [programming examples](../../../CslibTests/ComputationalCryptoPrograms.lean)
show how to certify new algorithms, including folds, captured inputs, and bounded loops.

## The main theorem

```lean
import Cslib.Crypto.Computational.GoldreichLevin.HardCore

open Cslib.Probability Cslib.Crypto

example {f : Word → Word} (hf : OneWayPermutation f) :
    PseudorandomGenerator (GoldreichLevin.generator f) (fun n => n + 1) :=
  hf.pseudorandomGenerator
```

The assumption includes polynomial-time evaluation of `f`, length preservation, bijectivity, and
one-wayness against every uniform PPT inverter. The conclusion includes deterministic
polynomial-time generation, exactly one bit of stretch at every input length, and computational
indistinguishability from uniform. Goldreich–Levin supplies the hard-core predicate and the
reduction's PPT certificate; neither is an extra hypothesis. Existence of a one-way permutation
remains an assumption.

The [generator](GoldreichLevin/HardCore.lean) splits its seed into two equally sized words and
at most one spare bit. It applies `f` to the first word, retains the second word and spare bit,
and appends the inner product modulo two of the two words. The spare bit lets the construction
handle odd seed lengths as well as even ones.

## Reading the proof

Read [HardCore.lean](HardCore.lean) first for the cryptographic argument: a hard-core bit appended
to a length-preserving permutation gives a PRG. It separates the prediction reduction from the
fact that a permutation preserves the uniform distribution.

Then follow the Goldreich–Levin development in this order:

| Module | What it establishes |
| --- | --- |
| [Decoding](GoldreichLevin/Decoding.lean) | A finite decoder with an explicit candidate-list size and failure bound, using pairwise-independent masks and a majority estimate. |
| [Reduction](GoldreichLevin/Reduction.lean) | Prediction bias yields inversion success. A randomized predictor's coins are sampled once and reused throughout decoding. |
| [Parameters](GoldreichLevin/Parameters.lean) | An explicit logarithmic mask count makes the candidate list polynomial at each fixed inverse-polynomial precision; negligible inversion success implies negligible prediction bias. |
| [WordDecoder](GoldreichLevin/WordDecoder.lean) | The deterministic decoder on ordinary words, its polynomial-time certificate, and its agreement with the finite construction. |
| [WordReduction](GoldreichLevin/WordReduction.lean) | The complete probabilistic inverter, its PPT certificate, and the reduction between the word-based security games. |
| [HardCore](GoldreichLevin/HardCore.lean) | The padded hard-core construction, even and odd seed lengths, and `OneWayPermutation.pseudorandomGenerator`. |

This order keeps three obligations visible: the finite probability bound, an efficient uniform
implementation of the reduction, and the final asymptotic security argument. In particular,
`wordInverter_isPPT` and `negligible_parityPrediction` in
[WordReduction](GoldreichLevin/WordReduction.lean) connect the decoder to computational security.

## Definitions and conventions

Cryptographic definitions live in `Cslib.Crypto`; efficiency predicates and encodings live in
`Cslib.Probability`.

| Module | Main interface |
| --- | --- |
| [Basic](Basic.lean) | `Negligible`, `winProbability`, `advantage`, and `ComputationallyIndistinguishable`. |
| [Ensemble](Ensemble.lean) | Polynomial bounds on sample lengths, connecting time polynomial in parameter plus input length to time polynomial in the parameter. |
| [Hybrid](Hybrid.lean) | Polynomially many game hops with a common negligible bound on adjacent advantages. |
| [OneWay](OneWay.lean) | `OneWay`, `OneWayPermutation`, and the inversion game, which accepts any preimage. |
| [HardCore](HardCore.lean) | `HardCore`, the prediction game, and PRG security from a hard-core predicate. |
| [PseudorandomGenerator](PseudorandomGenerator.lean) | `PseudorandomGenerator`, its real and ideal games, and polynomial bounds on their sample lengths. |
| [PseudorandomFunction](PseudorandomFunction.lean) | `PseudorandomFunction` and adaptive oracle games with `n`-bit keys, queries, and answers. |

A closed game has type `ProbComp Bool`; `winProbability` is its probability of returning `true`.
Distinguishing advantage is the absolute difference of two acceptance probabilities. `Negligible`
uses Mathlib's superpolynomial decay. Security quantifies over an entire uniform adversary before
requiring its advantage to be negligible, so the negligible bound may depend on that adversary.

For polynomial hybrid arguments, one negligible bound must cover every hop at each security
parameter. Separate negligibility statements for each fixed hop do not suffice. The interface
in [Hybrid](Hybrid.lean) makes this requirement explicit.

## Writing a game and proving it efficient

Here is the real PRG experiment as a program. Its efficiency proof composes the sampler with the
generator's and adversary's certificates:

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

`ProbComp.eval` gives a program's probability distribution. The `noncomputable` declaration here
allows the mathematical description of sampling; the `IsPPT` theorem separately supplies its
machine realization. This efficiency theorem applies to any certified generator, independently
of whether it is secure. The [walkthrough](../../../CslibTests/ComputationalCryptoDemo.lean) also
proves equality with the library's real PRG experiment.

The [PPT contracts](../../Computability/Probabilistic/PPT.lean) provide three entry points:

- `IsPolyTime inputEncoding f` certifies a deterministic computation returning a binary word.
- `IsPPTOn inputEncoding outputEncoding program` supports typed inputs and results.
- `IsPPT outputEncoding adversary` specializes to a security parameter and auxiliary word input.

Use [`polytime`](../../Tactic/PolyTime.lean) for supported deterministic combinations and
[`ppt`](../../Tactic/PPT.lean) for closed probabilistic programs. Calls to supplied algorithms
need their own certificates, as in the example above. These tactics assemble proofs from the
public closure rules; a Lean function type alone supplies no efficiency bound.

The main programming interfaces are [composition](../../Computability/Probabilistic/Composition.lean),
[encodings](../../Computability/Probabilistic/Encoding.lean),
[folds](../../Computability/Probabilistic/Fold.lean), and
[list operations](../../Computability/Probabilistic/List.lean).
The `_with` combinators let callbacks capture runtime inputs. For growing loops,
[`IsPolyTime.iterate_spec`](../../Computability/Probabilistic/Iteration.lean) uses one invariant
to prove the final postcondition and bound intermediate sizes. A polynomial number of iterations
also needs this size control to yield a polynomial-time algorithm.

## What a PPT certificate means

`Word` is `List Bool`. Fixed-width strings `Fin n → Bool` are used in the finite probability
arguments, with explicit bridges to word programs. Input encodings determine the size measure;
output encodings are injective. The standard adversary input is a unary security parameter,
a delimiter, and an auxiliary word.

A certificate supplies one finite-control machine and one polynomial clock for all encoded
inputs. Time is strict polynomial time in the full encoded input length, including every choice
of random coins. Sampling uses fair bits and the realization agrees exactly with the program's
distribution. Arbitrary PMFs are available in game specifications, but need separate efficiency
proofs when used in algorithms. This is a uniform model without nonuniform advice or an
expected-time convention.

Readers checking these foundations can start at
[PPT](../../Computability/Probabilistic/PPT.lean), then follow
[Clock](../../Computability/Probabilistic/Clock.lean) for genuinely halting realizations and
[CoinTape](../../Computability/Probabilistic/CoinTape.lean) for deterministic evaluation with
a polynomial-length random tape. Machine constructions underlying the programming rules live in
[Realization](../../Computability/Probabilistic/Realization) and the shared
[multi-tape machine library](../../Computability/Machines/Turing/MultiTape).

## Oracles and the current boundary

[`OracleComp Query Response α`](../../Languages/Probabilistic/Basic.lean) supports adaptive
queries, dependent response types, stateful handlers, and replacing oracle calls by programs.
Different interfaces can share one hidden state. `IsOraclePPT` requires a machine realization
preserving the joint distribution of the result and final oracle state for every stateful handler.
Its clock counts local computation, writing queries, and reading answers; the oracle's own work
is external.

The shared machine core supports finitely many operation names with word payloads. The current
`IsOraclePPT` interface uses a single word-query interface, and `ppt` automates closed programs.
Connecting general typed oracle interfaces to these efficiency contracts remains work to do.

The [PRF ideal game](PseudorandomFunction.lean) samples one random function and reuses it, so
repeated queries agree. The [machine examples](../../../CslibTests/ComputationalCryptoMachines.lean)
also include a small lazy-sampled oracle with shared state. A reusable random-oracle theory and
an eager/lazy equivalence theorem remain future work, as do polynomial stretch amplification and
the implication from general one-way functions to PRGs.

## Sources and further reading

The module docstrings cite the underlying mathematics: Arora–Barak and Boneh–Shoup for the
security definitions, and Goldreich–Levin with Trevisan's lecture notes for the decoding argument.
[Decoding](GoldreichLevin/Decoding.lean) explains the direct-coordinate variant used here.
The [probabilistic language](../../Languages/Probabilistic/Basic.lean) credits VCVio for the related
separation of oracle syntax and interpretation. The [Crypto overview](../README.md) records
machine reuse, port provenance, and further integration work, including the bridge to the
primitive-level PRG family API.
