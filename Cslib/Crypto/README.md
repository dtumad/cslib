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
`program.toMeasure model` accepts an explicit `PFunctor.OutputMeasure` for either `FreeM` or
`Resumption`. The bundle chooses operation measures on the existing response measurable spaces;
it introduces no new measurable-space instances or canonical probability law.
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
The rejection sampler proves exact uniform output in every nonempty finite range, geometric
timeout probability, and expected proposal count `m / n`. `FreeM.sampleFin` implements bounded
rejection using individual fair bits. With `ceil(log₂ n)` bits per proposal and `t` attempts,
it uses at most `t * ceil(log₂ n)` coin operations and fails with probability at most `2⁻ᵗ`.
Failure is an explicit `none`, with exact probabilities for every successful output.
`ElGamal.Resumption` preserves the full oracle-DDH identity when inlining almost-surely
terminating effect implementations, including their infinite rejected paths.
The structural `Std.WP` interpretation and an explicit expectation interpretation share the same
free programs. Their operation specifications let core `vcgen` handle monadic sequencing;
probability arithmetic, couplings, and machine-runtime bounds remain separate obligations.

[`Schnorr`](Primitives/Schnorr.lean) uses Mathlib's `Module F G` for scalar multiplication.
It supplies signing, verification, special-soundness extraction, and a perfect honest-verifier
zero-knowledge proof as equality of whole transcript measures. `Schnorr.Oracle` defines EUF-CMA
with a shared cached random oracle and a signed-message log. Honest signing followed by
verification is a program equality that retains the final cache. Both honest schemes are also
tested through `OptionT` with the bounded binary sampler, including exhaustion.

[`Schnorr.Extraction`](Primitives/Schnorr/Extraction.lean) proves the concrete identification
bound `ε² - ε / |F|` for an extractor that saves the commitment and private state and samples
two independent continuations. Every successful extraction returns a discrete logarithm.
`FreeM.trace` and `FreeM.replay` record dependent operation/response pairs and prove exact replay
of both complete traces and prefixes. `FreeM.denote_liftM_stateT` connects inlined stateful
handlers to their joint result-and-state kernels; `Game.advantage_le_disagreement` gives the
native-measure coupling bound for game hops.

[`Schnorr.Simulation`](Primitives/Schnorr/Simulation.lean) simulates signing from the public key.
It proves equality of the entire signature/cache measure with honest signing restricted to
fresh hash inputs, and bounds each programming collision by `cache.length / |F|`.
[`Schnorr.Fork`](Primitives/Schnorr/Fork.lean) composes this simulator with final verification,
adaptive hash-query selection, and checked extraction. `FreeM.fork` retains the exact continuation
at the selected occurrence; its structural theorem identifies the common replay prefix, and
its measure theorem preserves the first execution's distribution. Tests exercise the full
extractor, including identity public keys, repeated challenges, and signed-message freshness.

[`Schnorr.Security`](Primitives/Schnorr/Security.lean) proves the full concrete EUF-CMA reduction.
If honest forgery succeeds with probability `ε`, set
`ε' = ε - qS * (qH + qS) / |F|`, using truncated nonnegative subtraction.
The actual discrete-logarithm reduction succeeds with probability at least
`ε' * (ε' / (qH + 1) - 1 / |F|)`. Here `qS` and `qH` bound the adversary's signing and hash
requests; ambient operations do not count toward either bound. The extra hash position comes
from final verification, which also covers forgeries whose hash was never requested by the
adversary. The proof combines the joint-cache signing law, adaptive collision accounting,
the general forking inequality, and checked special-soundness extraction. It averages over
key generation and implements all fresh hash draws with the original sampler.
The equivalent square-root upper bound on forgery probability is also available.

The runtime candidate in `Computability/PolynomialTime` recovers the deterministic machine
constructions from Samuel's branch without probabilistic dependencies. Certificates include one
finite binary machine and one polynomial clock for all encoded inputs, with a bridge to the
existing `ComputableInTimeAndSpace` predicate. Composition, bounded iteration, and encoded list
operations charge for copying and restoring scratch storage. The native `MultiTapePTM` execution
uses `FreeM`, keeps timeout separate from successful output, and preserves shared named-oracle
state through `Measure` kernels. Uniform binary-word sampling has a fixed one-state machine and
an `n + 1` transition bound. Saved-coin execution preserves the exact calls across a pause, and
pathwise halting identifies bounded execution with its unbounded `Resumption`.
Probabilistic certificates compose through a physical buffered-input machine, including efficient
deterministic pre- and postprocessing. Subroutines have separate communication buffers and share
the oracle's hidden state. Kernel correctness also identifies exactly the reachable encoded outputs,
so sequencing needs no assumed decoder. Association-list lookup has a uniform machine certificate
using the ordinary `List.lookup` API and charging for key comparisons and cache traversal.
`Realizer` retains the chosen finite machine and polynomial clock as data; its composition uses
the supplied machines. Saved-tape execution preserves the complete joint measure and every
structural postcondition. An oracle that counts requests transfers the machine's transition
bound to selected external requests in the original source program, without assuming a separate
source query budget or matching the placement of private coins.
At word interfaces, Mathlib's `Computability.Encoding` supplies decoding. Canonical validation
rejects words outside the encoding's range and preserves a certified decoder's polynomial bound.
Compound decoding and optional pairing require no arbitrary defaults for represented values.
Typed oracle adapters preserve the complete program and joint state when requests and replies
are canonical, and reject malformed messages explicitly. Word-machine clocks now bound the
original typed requests even for parameter-dependent signatures. Chosen machines also return
checked typed results, with pathwise and joint-measure guarantees for saved private tapes.
Captured continuations retain the original input and charge for its copying. Binary normalization
and comparison, and the bounded `FreeM.sampleFin` sampler, now have uniform machine certificates.
The sampler is polynomial in the range's bit length, unary proposal width, and unary attempt budget;
it preserves the exact joint kernel and distinguishes rejection failure from machine timeout.
Using the range's binary length as the proposal width still gives failure at most `2⁻ᵗ`.
Finite machine snapshots use lists around Mathlib tape heads and preserve the original machine's
entire joint result-and-handler-state computation. Saved-coin replay now has a uniform machine
certificate for certified deterministic handlers, with explicit bounds on reply lengths and
per-call state growth. Request buffers grow by at most one bit per transition; the replay bound
charges for copying complete snapshots, accumulated caches, and oracle replies.
The interpreter also certifies aborting stateful handlers: failed runs remain rejected,
and completing the machine's clock after failure performs no further handler effects.
Sampling the private tape before execution preserves the joint output-and-oracle-state measure.
Adaptive rewinding now has a uniform certificate using prefix replay. It restores both the
finite snapshot and handler state and reuses the same private-coin suffix. A restart operation can
replace the remaining oracle-answer tape while retaining the prefix cache. The private-tape
convention agrees with Bellare and Neven's general forking lemma. Recorded-prefix replay now
preserves the complete two-run program, and tracing and replay use ordinary stateful handlers
compatible with the snapshot interpreter. Forking doubles the source query budget at most.
Presampling a sufficient finite answer tape preserves the whole result measure, including the
adaptive second run; exhaustion remains explicit. Averaging over a private seed shared by both
runs preserves the forking inequality. Applying these laws to the complete typed Schnorr
simulator and its machine certificate is still required.
`ElGamal.PolynomialTime` certifies honest key generation, encryption, and decryption uniformly
across an indexed group family. It derives binary exponentiation from certified multiplication
and polynomial bounds on element encodings. The parameter data and remaining group primitives
have explicit uniform certificates; sampling exhaustion remains visible in `OptionT`.
The same module also certifies the ordinary two-phase DDH reduction from
the adversary phases' uniform certificates and group multiplication. Dependent results retain
their parameter through the compiled continuation, without a decoder or a default value.
`ElGamal.Security` applies that certificate to uniform DDH hardness and proves negligible
prediction bias. Its cutoff version derives the two-sample challenge error from local sampler
laws; it leaves no assumed admissibility obligation for the ordinary reduction.
`ElGamal.Security.Binary` completes the family theorem for the bounded binary implementation,
including adaptive encryption requests before and after the challenge. The actual reduction
has one uniform polynomial-time machine, obtained by compiling randomized oracle substitution.
Replies preserve nonce-sampling exhaustion as an optional ciphertext, allowing the adversary
to continue. The two challenge draws add at most `2 * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` to the DDH advantage;
oracle sampling is simulated identically in both worlds. An efficiently computed attempt budget
at least the parameter makes this error negligible. Group operations, canonical parsing,
encoding-size bounds, and DDH hardness remain explicit family assumptions.
`Schnorr.PolynomialTime` gives uniform certificates for key generation, response arithmetic,
transcript checking, and special-soundness extraction. Scalar decoding checks the binary range;
the algebra certificates use independently supplied group and field encodings.
The cached hash query, Schnorr signing, and hash-based verification also have uniform machine
certificates. They retain the complete cache and preserve sampling exhaustion explicitly;
an exhausted unused hash draw cannot invalidate a cache hit. Indexed sampling retains its input
in an ordinary dependent pair, so subsequent arithmetic uses the sampled scalar directly.
The signing simulator now has the same uniform guarantee, including both binary samplers,
commitment arithmetic, cache lookup, and cache update. Its output distinguishes exhaustion
from a programming collision, and its machine proof uses the same `simulateSign` definition
as the security proof.
The saved-tape simulator also has a uniform certificate for a complete clocked adversary run.
Private simulator scalars and fresh hash answers have separate cursors; its state-size bound
charges accumulated logs, caches, and retained tapes. The canonical word handler implements the
typed handler exactly, and flattening the tape state preserves an entire adaptive typed program.
Malformed requests, exhausted tapes, and programming collisions reject the execution.
Adaptive replay now composes three such aborting executions with certified selection and
restart. Skipping a saved hash-answer block preserves the prefix cache and both private
randomness sources; the correspondence with the semantic fork's selected query remains open.
The complete first run now includes checked output decoding and final forgery verification.
It rejects timeout, malformed output, failed interfaces, and previously signed messages.
Final verification shares the cache and hash tape and preserves private simulator randomness;
its typed saved-tape execution equals the original `simulatedForgery` program.
`FreeM.forkFromAnswers` implements the full fork by restarting with the recorded answer prefix
and a fresh suffix. Two source-length tapes preserve the entire two-run measure, including
adaptive selection and different paths after the fork. The general forking bound holds with
one private seed shared by both runs. A traced interpreter and selector give a uniform machine
for this replay construction, charging for both executions and prefix copying. Schnorr's
fresh-hash selector has a uniform certificate, using ordinary `List.findIdx?`, scalar
decoding, and the certified group operations. The checked machine interpreter now records its
fresh-hash transcript, including the final verifier's query. Cache hits and simulated signatures
add no positions. Forgetting the transcript recovers the original execution exactly, and every
accepted forgery has an accepting recorded hash. Recorded answers form precisely the consumed
hash-tape prefix. The uniform certificate charges for growing and copying the transcript, using
only the existing arithmetic, parser, and representation-size certificates. Rejected executions
remain `none` and expose no transcript. `FreeM.forkFromTracedAnswers` now supports this rejection
behavior: its whole-measure equality and general forking bound allow failed-run logs to be
discarded, with one private seed shared by both runs. Its machine certificate is uniform across
indexed result, operation, and answer families and needs no default result. Fixing the machine
coins and simulator scalars now gives an ordinary hash-only `FreeM` source. Its successful trace
equals the complete checked machine run pointwise in both saved tapes, including timeout,
malformed interfaces, signing collisions, cache hits, and final verification. The corresponding
two-run replay has one uniform polynomial-time certificate derived from the existing primitive
certificates and representation bounds. The shared-seed distribution argument, source tape
budget, extraction postprocessing, and final Schnorr family hardness theorem remain open.

Samuel's `polytime` and `ppt` tactics have been adapted to these native certificates. Tests cover
data-dependent sampling, captured continuations, calls to certified subprograms, and the ordinary
Schnorr key generator and response arithmetic. Dependent tuple arguments and projections now let
`polytime` prove response arithmetic and extraction uniformly across indexed scalar families.
Core `vcgen` also proves the structural correctness
of an honest Schnorr transcript, leaving its algebraic identity as the final obligation.
Reachability reflection transfers that postcondition to every completed path of a realizing machine.
The tactics do not infer efficiency for arbitrary Lean functions or supply loop-size invariants.

The remaining runtime work connects the shared-seed sampling measure to the semantic fork,
bounds the source answer tape, and certifies Schnorr's complete reduction. Group and field
primitives and family parameter data require explicit uniform certificates.
Adaptive finite-sampling programs now have a whole-experiment cutoff bound
`draws * 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` for every payoff in `[0, 1]`. Successful bounded executions are dominated
by the ideal measure. Polynomially many draws and an attempt budget at least the security
parameter give negligible error. The scheme-specific bounds now count complete games and
reductions: Schnorr uses at most `2q + 2` draws in the honest game and `4q + 3` in the
discrete-logarithm experiment, where `q` counts selected ambient, hash, and signing requests.
ElGamal pays for both adaptive phases and two or three challenge exponents. Both schemes have
concrete security theorems for the resulting cutoff implementations. A `ZMod 101` regression
instantiates Schnorr's complete bound with the actual binary rejection sampler. Security
transport supports polynomial loss, square-root loss, and separate negligible errors.
ElGamal's ordinary and binary oracle family theorems use actual uniform-machine admissibility.
The machine resumption exposes one coin per transition and an additional operation per oracle
submission; ordinary effect truncation therefore differs from a transition clock.

For Schnorr, the concrete theorem assumes a finite scalar field, countable effects and messages,
a uniform sampler, and a bijective scalar-to-public-key map. Computational and asymptotic
security still require implementing and costing the reduction and proving admissibility for
a group family. The cutoff theorem accounts for both fork executions, including simulator
randomness and the final verifier. Aborting finite sampling can only remove successful forgeries.
`DiscreteLog.Security` derives negligible inverse scalar-space size from uniform DL hardness:
the certified always-zero guess succeeds with probability exactly `1 / |F|`. Thus the eventual
Schnorr family theorem needs no separate asymptotic field-size assumption.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
