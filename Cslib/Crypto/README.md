<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Crypto

This directory hosts **cryptographic definitions, primitives, protocol models, and related security metatheory**. Its scope includes both basic cryptographic notions and larger developments such as security protocols.

We aim at supporting both abstract security reasoning and concrete protocol developments, while making explicit the relations between them. To this end, this part of CSLib has very important relationships with [Languages](../Languages) and [Logics](../Logics), explained in the remainder.

## Principles

### Integration with languages

Whenever appropriate, cryptographic primitives should be developed so that they compose well with CSLib's [languages](../Languages) that offer a way to integrate a computational substrate. This is common, for example, in choreographic programming languages and many process calculi.

The aim is to build end-to-end models where cryptographic operations appear inside larger communicating or computational systems.

To this end, we expect to leverage the combination of `Crypto` and [Languages](../Languages) to define and formally reason about security protocols. CSLib's common semantics APIs connecting [Languages](../Languages) and [Logics](../Logics) should enable such reasoning.

## Pseudorandom generators

[`Primitives/PRG`](Primitives/PRG) formalizes Boneh and Shoup's Attack Game 3.1 using
PMFs. `Generator.Secure G Admissible ε` bounds the distinguishing advantage of every
admissible randomized test. `Family.SecureWithError` allows a parameter-dependent error bound;
`Family.Secure` requires negligible advantage separately for each admissible family, using
Mathlib's `SuperpolynomialDecay`. A negligible error bound implies this asymptotic notion.
The caller supplies `Admissible`; these definitions do not assert computational efficiency.

The range-membership adversary has advantage exactly `1 - |range G| / |Output|`, and hence
at least `1 - |Seed| / |Output|`. Any non-negligible lower bound on the image gap rules out
asymptotic security when the range-test family is admissible. The executable `rangeTest`
requires `DecidableEq Output`. Bitstring families eventually stretching by at least one bit
are consequently insecure against any class admitting this test, with both `Fin n → Bool`
and `BitVec n` versions and nonexistence corollaries. Zero-error security against all tests
is equivalent to exactly uniform output; the identity generator is a nonexpanding example.

## Polynomial programs and measure semantics

The new experiments use `PFunctor.FreeM` for programs and Mathlib `Measure` for their
interpretation. An effect is a shape and its response type; a handler is a dependent function.
`FreeM.liftM` inlines handlers, and `FreeM.runKernel` handles shared mutable state using Mathlib
kernels. `Game` is `Measure Bool`, with explicit normalization hypotheses where needed.
`Game.Secure` quantifies over whole adversaries before the security parameter, using an explicit
admissibility predicate and Mathlib's superpolynomial decay.

[`ElGamal`](Primitives/ElGamal.lean) proves decryption correctness and gives the concrete DDH
reduction. [`ElGamal.Oracle`](Primitives/ElGamal/Oracle.lean) proves the exact advantage identity
with adaptive encryption requests in both adversary phases. The proof uses native uniform
measures, with countable adversary state, following Katz and Lindell (2007), Construction 10.19,
Theorem 10.20, and Proposition 10.5. It does not assume that arbitrary Lean functions are efficient.

`PFunctor.Resumption` permits infinitely many visible operations. Its returned-output measure
loses mass on divergence, and finite truncations retain a separate `none` outcome for timeout.
The rejection-sampling example proves exact uniform output, geometric timeout probability, and
finite expected operation count. Inlining that sampler into the small ElGamal test preserves
the security identity, including the sampler's infinite rejected paths.
The structural `Std.WP` interpretation and an explicit
expectation interpretation share the same free programs; the quantitative `vcgen` test currently
requires a local operation specification.

Machine realizability still needs encodings, a compiler that preserves the joint result and
state measure, and clocks charging local work and handler implementation. In particular, a
uniform exponent is not a unit-cost machine instruction: binary rejection sampling and efficient
group operations must be certified in the bit length of the group order. Exact sampling may be
expected polynomial time; strict polynomial time requires a cutoff and an explicit failure
budget. Computational and asymptotic ElGamal security additionally require the reduction to
preserve the chosen admissibility predicate for a parameterized group family.
Silent machine steps can be made visible by adjoining `PFunctor.y` as a deterministic tick
operation; certifying the transition compiler and its cost remains a separate obligation.

Schnorr and a forking lemma remain future work. They need a consistent random-oracle cache and
replay of the same adversary coins and shared state up to the fork, followed by fresh suffix
randomness. Equality of marginal output measures alone does not supply that replay property.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
