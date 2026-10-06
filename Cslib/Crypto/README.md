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

## ElGamal encryption

[`Primitives/ElGamal`](Primitives/ElGamal) defines ElGamal encryption and its chosen-plaintext
experiment as programs in an arbitrary monad; decryption is correct as an equation of programs.
Under any measure semantics of the monad (`Cslib.IsMeasureSemantics`), such as the output
measures of free programs and resumptions, the reduction to the decisional Diffie–Hellman
experiments of [`Assumptions/DDH`](Assumptions/DDH.lean) is exact: an adversary's advantage
equals the reduction's distinguishing advantage. Adversaries and samplers are arbitrary
computations: exponents may be selected uniformly by a primitive operation of a free program, or
drawn from fair coins alone by rejection sampling, as a resumption that returns almost surely.

Asymptotically, [`Primitives/PKE`](Primitives/PKE) defines public-key encryption over a monad
and security against eavesdroppers, [`Assumptions/GroupGen`](Assumptions/GroupGen.lean) defines
group generators, and [`Assumptions/DDH/Asymptotic`](Assumptions/DDH/Asymptotic.lean) the DDH
assumption relative to them. Adversaries and group
generators are algorithms, programs in their own monad lifted into the monad of the experiments,
so that they may use fewer resources, such as only fair coins. As for pseudorandom generators, security is relative to a predicate on
adversaries supplied by the caller: ElGamal is secure against the eavesdroppers whose reductions
are admissible, if DDH is hard against admissible distinguishers, since the two advantages are
equal at every security parameter. With fair coins as the only randomness, the algorithms are free
programs of coin flips and the experiments are resumptions that sample exponents exactly by
rejection; every hypothesis of this analysis then holds.

## Schnorr

[`Primitives/Schnorr`](Primitives/Schnorr) defines Schnorr identification and signatures over a
group that is a module over a field of scalars, as programs in an arbitrary monad. Two accepting
transcripts with distinct challenges reveal a discrete logarithm of the public key (special
soundness). Under any measure semantics with a uniform sampler of scalars, honest transcripts are
distributed as simulated ones (honest-verifier zero knowledge), and running a prover's commitment
once with two independent challenges extracts a discrete logarithm with probability at least
`ε² - ε / |F|`, where `ε` is the prover's success probability.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
