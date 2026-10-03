<pre>
Copyright (c) 2026 Fabrizio Montesi, Samuel Schlesinger. All rights reserved.
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
The seed and ideal distributions are explicit parameters, defaulting to uniform sampling on
finite types. This also supports distributions on words, where the ambient type is infinite.

[`Game`](Game.lean) supplies acceptance probability, distinguishing advantage, and negligible
security for Boolean experiments. The semantic PRG definitions and the computational definitions
share this layer. [`Computational/PseudorandomGenerator`](Computational/PseudorandomGenerator.lean)
instantiates `Family.Secure` with uniform words and `IsPPTTest`, then requires deterministic
polynomial-time evaluation and strict length expansion. `IsPPTTest` requires one uniform machine
for the entire test family. It is equivalent to the PPT restriction on programs interpreting
those tests; specifying a PMF does not itself establish efficient sampling.

[`Game/Hybrid`](Game/Hybrid.lean) supplies the common hybrid and reduction calculus.
One-wayness, hard-core security, and PRF security also instantiate `Game.Secure`.
[`Game/Statistical`](Game/Statistical.lean) identifies Boolean advantage with statistical distance
and proves contraction under arbitrary randomized tests. This applies to PMFs on infinite word
spaces as well as finite types. Its PRG and computational specializations reuse the same theorems;
statistical approximation can therefore be one hop in a computational security argument.

The range-membership adversary has advantage exactly `1 - |range G| / |Output|`, and hence
at least `1 - |Seed| / |Output|`. Any non-negligible lower bound on the image gap rules out
asymptotic security when the range-test family is admissible. The executable `rangeTest`
requires `DecidableEq Output`. Bitstring families eventually stretching by at least one bit
are consequently insecure against any class admitting this test, with both `Fin n → Bool`
and `BitVec n` versions and nonexistence corollaries. Zero-error security against all tests
is equivalent to matching the ideal distribution; with the defaults, this means exactly uniform
output. The identity generator is a nonexpanding example.

## Plans and notes

### Computational security

For a guided introduction, proof roadmap, and small Lean examples, start with the
[computational cryptography guide](Computational/README.md).

[`Computational`](Computational) provides definitions of one-way functions and permutations,
pseudorandom generators,
and pseudorandom functions, following Arora and Barak, Boneh and Shoup, and Goldreich, Goldwasser,
and Micali. References appear in the modules. The library proves that a one-way permutation yields
a uniform polynomial-time pseudorandom generator with one-bit stretch, through Goldreich–Levin.
The existence of the starting one-way permutation is an assumption.

The supporting layers are:

- [`Probabilistic/Basic`](../Languages/Probabilistic/Basic.lean): `ProbComp` and `OracleComp`, built on
  CSLib's `FreeM`, with `do` notation, PMF sampling, dependent oracle responses, stateful handlers,
  and oracle substitution. Bounded loops use ordinary Lean recursion.
- [`MultiTape/Machine`](../Computability/Machines/Turing/MultiTape/Machine.lean): shared machine
  tables, tape actions and communication channels. `MultiTapeNTM` specializes relational choice
  and an empty operation type; `MultiTapePTM` retains an action for each fair coin. `OracleTM`
  is its compact single-operation interface and uses the same bounded evaluator. A finite type
  names operations, while request payloads are arbitrary words. Different operations can share
  the interpreter's hidden state.
- [`PPT`](../Computability/Probabilistic/PPT.lean): uniform, strict polynomial-time realizability by
  a fixed finite-control machine. The security parameter is encoded in unary. Machine steps account
  for local computation, fair coins, query construction, and reading oracle answers; the oracle's
  own computation is external. Merely counting oracle queries is not a PPT certificate.
- [`Game`](Game.lean) and [`Computational/Basic`](Computational/Basic.lean): shared negligible
  security, computational indistinguishability, complementing game answers, and the two-hop
  hybrid inequality, reusing Mathlib's superpolynomial decay.
- [`Computational/OneWay`](Computational/OneWay.lean): `OneWayPermutation` combines one-wayness
  with a length-preserving bijection. Its output on a uniform seed is proved exactly uniform;
  appending an independent fair bit gives the uniform distribution at the expanded length.
- [`Computational/HardCore`](Computational/HardCore.lean): hard-core predicates are defined by
  unpredictability against uniform PPT predictors. The exact distinguishing gap is the average
  signed bias of two fixed predictors, whose input preparation and Boolean postprocessing have
  machine certificates. `OneWayPermutation.pseudorandomGenerator_of_hardCore` proves the complete
  one-bit PRG theorem under a hard-core assumption, including deterministic efficiency and stretch.
- [`Computational/GoldreichLevin/Decoding`](Computational/GoldreichLevin/Decoding.lean): a finite
  subset-sum decoder for deterministic predictors. Its output has at most `2^k` candidates and
  misses a target of prediction bias `ε` with probability at most `n / (4 ε² (2^k - 1))`.
  The proof reuses the existing bitstrings, Mathlib's Boolean ring and dot product, and its
  variance and Chebyshev inequalities. Pairwise independence of the subset sums is proved as
  an exact joint-distribution identity. This is the decoding argument, without a PPT certificate.
- [`Computational/GoldreichLevin/Reduction`](Computational/GoldreichLevin/Reduction.lean): a
  seeded randomized predictor of absolute bias at least `ε` yields an inverter of success at
  least `ε/8`, when `2^k - 1 ≥ 2n/ε²`. The inverter samples one seed, reuses it throughout decoding,
  and checks the candidates' images. An independent fair bit handles either sign of the bias.
  The finite probability bound needs no injectivity assumption.
- [`Computational/GoldreichLevin/Parameters`](Computational/GoldreichLevin/Parameters.lean): an
  explicit logarithmic mask count gives at most `4np² + 2` guesses at precision `1/p`.
  Prediction bias is bounded by `1/p + 8 * inversion_success`. If each fixed-degree inverter
  has negligible success, prediction bias is negligible; the degree is fixed before the length.
- [`Computational/GoldreichLevin/WordReduction`](Computational/GoldreichLevin/WordReduction.lean):
  the inverter is a single word-based probabilistic program drawing explicit uniform bit tapes.
  Its prediction and inversion games equal the finite experiments exactly. For a PPT predictor,
  one polynomial-time seeded evaluator works across all lengths and precision degrees.
  `wordInverter_isPPT` certifies the full inverter with `unfold wordInverter coinBudget; ppt`.
  `negligible_parityPrediction` derives negligible parity-prediction bias from one-wayness.
- [`Computational/GoldreichLevin/HardCore`](Computational/GoldreichLevin/HardCore.lean): apply the
  permutation to the first half of a seed, retain the remaining bits, and append the parity of the
  two halves. Two fixed PPT reductions handle even and odd seed lengths. The final theorem,
  `OneWayPermutation.pseudorandomGenerator`, combines the hard-core predicate, polynomial-time
  evaluation, and exact preservation of uniform seeds. It has no additional reduction hypotheses.

The checked bridges between these layers now include:

- [`Sampling`](../Computability/Probabilistic/Sampling.lean): one fixed fair-coin machine samples
  `n` uniform bits in `n + 1` transitions. It works against every stateful oracle and leaves the
  oracle state untouched.
- [`CoinTape`](../Computability/Probabilistic/CoinTape.lean): every uniform PPT witness is exactly
  a polynomial-time deterministic function of a polynomial-length uniform random tape. Sampling
  private coins in advance also preserves the shared machine's joint final configuration and
  oracle state for every stateful handler. For closed machines, the deterministic replay compiler
  starts with blank work tapes and includes parsing, input redirection, and all rewinds. Its full
  bound is `6 * coins.length + 3 * input.length + 12`. The same evaluator works for every supplied
  input and coin tape, even when the source never halts.
- [`PPT`](../Computability/Probabilistic/PPT.lean): deterministic algorithms on the encoded pair
  `(security parameter, auxiliary input)` embed into PPT. Any fixed Boolean postprocessing of a
  PPT answer is also PPT, with the same clock. Certificates can use any finite control type without
  manually enumerating its states. These are proved machine constructions.
- [`Output`](../Computability/Probabilistic/Output.lean): replacing each output bit by a fixed word
  preserves PPT and oracle PPT. Codewords may have unequal lengths, including zero. The explicit
  slowdown is `max |code false| |code true| + 2`; the oracle's private state is preserved.
- [`Clock`](../Computability/Probabilistic/Clock.lean): both `IsPPT.exists_halting_machine` and
  `IsOraclePPT.exists_halting_machine` turn an externally clocked certificate into a genuinely
  halting realization. The compiled witness has fixed finite control, starts with blank tapes,
  and has one polynomial halting bound for every input and every stateful oracle.
- [`Composition`](../Computability/Probabilistic/Composition.lean): typed `IsPPTOn` certificates
  compose with `bind`, `map`, argument preparation, and conditionals. The `_with` combinators let
  callbacks capture the caller's input. The compiler charges for copying and initializes fresh
  continuation tapes; the first program's output bound controls the second program's runtime.
  The word-based `IsPPT` combinators specialize these same realizations and retain the unary
  security parameter automatically.
- [`Input`](../Computability/Probabilistic/Input.lean): appending a fixed challenge bit to a PPT
  adversary's input preserves PPT. Its proof composes the public parameter and input projections
  with concatenation; the resulting certificate accounts for writing the full encoded input.
- [`PolynomialTime`](../Computability/Probabilistic/PolynomialTime.lean): `IsPolyTime.append`
  computes two functions on the same input and concatenates their outputs. The machine uses
  disjoint work tapes and the shared input rewind. Its time bound is the sum of the two bounds
  plus `input.length + 2`; finite control is reindexed without changing execution time.
  `IsPolyTime.exists_restoring_machine` supplies a reusable realization of any polynomial-time
  function: it appends the result, clears every scratch tape, and restores every head.
  `IsPolyTime.exists_tape_machine` makes the same function callable on a buffered argument,
  preserving that argument and the surrounding input and output.
- [`Iteration`](../Computability/Probabilistic/Iteration.lean): `IsPolyTime.iterate` certifies
  bounded loops using only word functions and size bounds. Initialization, the unary iteration
  count, and the step function must be polynomial time, and all intermediate words must have
  one polynomial length bound. The conclusion supplies one fixed machine and polynomial clock
  for the entire loop, including preparation, changing-length buffer transfers, and final output.
  A polynomial iteration count alone is insufficient because intermediate words may grow
  exponentially. The client theorem exposes no tape indices or head positions.
- [`TapeCall`](../Computability/Machines/Turing/MultiTape/Plumbing/TapeCall.lean) and
  [`TapeUpdate`](../Computability/Machines/Turing/MultiTape/Plumbing/TapeUpdate.lean): restoring
  subroutines read a buffered argument and produce either a separate result or a replacement
  argument. The replacement clears the old tail when the result is shorter; temporary buffers
  and all heads are restored before the next call. The shared tape embeddings preserve unused
  tapes. [`UnaryRepeat`](../Computability/Machines/Turing/MultiTape/Plumbing/UnaryRepeat.lean)
  composes these calls across changing word states, allowing different actual stopping times.
- [`RestoreWork`](../Computability/Machines/Turing/MultiTape/Plumbing/RestoreWork.lean): the
  restoration compiler records each work head's visited interval on a companion tape, clears
  the recorded intervals in parallel, and uses the shared input rewind. Its complete bound is
  `7 * time + input.length + 9`. The proof handles blank gaps, negative work-head positions,
  early halting, and an arbitrary previously accumulated output. The controller and number
  of work tapes remain fixed independently of the input and number of later invocations.
- [`Ensemble`](Computational/Ensemble.lean): polynomial bounds on sample lengths, preserved by
  deterministic polynomial-time maps. On these ensembles, a clock polynomial in parameter plus
  sample length is bounded by a polynomial in the parameter alone. Both PRG ensembles satisfy this.
- [`Hybrid`](Computational/Hybrid.lean): polynomially many hops have negligible total advantage
  when **one common negligible bound covers all hops at each parameter**. The bound may depend on
  the adversary. Negligibility for each fixed hop separately is insufficient.

At the machine level, execution can be paused and resumed with the entire configuration, including
the partially written query and current answer. Oracle substitution preserves the joint
distribution of the result and the oracle's private state.
[`Oracle/Simulation`](../Computability/Machines/Turing/MultiTape/Oracle/Simulation.lean) lifts a
one-transition simulation with a fixed slowdown to an entire clocked run. The output encoding
compiler instantiates this theorem, including when the source is stopped by clock exhaustion.
[`Oracle/Sequential`](../Computability/Machines/Turing/MultiTape/Oracle/Sequential.lean) proves
that halting bounds add for shared-tape sequencing, even when the first stopping time depends on
random choices or oracle answers. This retains the oracle communication tapes across the handoff.

The internal clock compiler connects these checked components:

- [`Oracle/Clock`](../Computability/Machines/Turing/MultiTape/Oracle/Clock.lean) consumes a unary
  budget on an additional work tape. A budget of `m` cells simulates exactly the first `m` source
  transitions and halts by `2m + 1` transitions. Further runtime cannot change the result or oracle
  state. This applies even if the source never halts or the cutoff occurs just after a query.
- [`PolynomialClock`](../Computability/Machines/Turing/MultiTape/Plumbing/PolynomialClock.lean)
  constructs `c * (input.length + 1)^d` unary cells from blank tapes using a fixed finite-control
  machine. Its polynomial runtime includes initializing and resetting its nested-loop counters.
  The coefficient and degree are fixed before the input is supplied.
- [`PrepareClock`](../Computability/Machines/Turing/MultiTape/Plumbing/PrepareClock.lean) reserves
  the source tapes, directs the generated budget to its own tape, and rewinds the budget head.
- [`Oracle/PolynomialClock`](../Computability/Machines/Turing/MultiTape/Oracle/PolynomialClock.lean)
  sequences preparation and simulation. For a source clock `c * (L + 1)^d`, the compiled machine
  halts within `(6^d * (c + 1) + 3c + 5) * (L + 1)^(d + 1)` transitions. Its joint output and
  oracle-state distribution equals the original clocked run. Additional runtime changes neither.

[`Oracle/Composition`](../Computability/Machines/Turing/MultiTape/Oracle/Composition.lean) now
feeds one closed machine's output to another, with separate work tapes and a buffered input.
The output buffer is rewound and its input boundary marker is installed by actual machine steps.
If the first machine takes at most `a` steps and the second at most `b` on every supported output,
the combined bound is `2a + b + 4`. Local simulation of each empty-answer oracle gives the second
machine clean communication tapes and leaves any external oracle state untouched.

Ordinary closed PPT composition now retains the original security parameter automatically.
The retention routine copies its unary encoding, restores the input head and then runs the source;
its `2n + 3` preparation steps are included in the polynomial bound.
The deterministic plumbing uses the shared `HaltsAt`, `runFrom_seq` and `rewindInput` APIs from
merged PRs [#1000](https://github.com/leanprover/cslib/pull/1000),
[#1002](https://github.com/leanprover/cslib/pull/1002) and
[#1004](https://github.com/leanprover/cslib/pull/1004).
The last-tape rewind is a specialization of Christian Reitwiessner's `rewindWork` from
[#1005](https://github.com/leanprover/cslib/pull/1005), revision
`d0305921adb0e82e79de62289229bd5d9736b4a5`; it retains the `word.length + 2` bound.
The rewind definitions are exposed locally so downstream machine evaluation and proofs can
reduce their transitions. Their execution theorems are reused directly.
Output concatenation and its fresh-tape handoff adapt the
[`concat-combinator` branch](https://github.com/crei/cslib/tree/fbd5ffb777505377f72204dc3f7ec212456fa2af),
and deterministic state relabelling adapts
[`tm_relabel`](https://github.com/crei/cslib/tree/85590b43845e5915c4e3793016c887039c1da106).
The concatenation port proves output and time correctness using the current shared APIs;
the source branch's additional space bound has not been ported. Deterministic and oracle output
prefix proofs now share the same action-level preservation lemma.
An unfinished native query cannot be cleared by making a dummy call when oracle state is
observable. General oracle composition therefore needs private buffering until query submission.
The OWP-to-PRG target can use this closed composition interface for its efficient reductions.

For example, a program can make adaptive queries without mentioning its interpreter:

```lean
def adaptive (input : List Bool) :
    OracleComp (List Bool) (fun _ => List Bool) (List Bool) := do
  let answer ← OracleComp.query input
  OracleComp.query answer
```

The PRF real game chooses a key once. Its ideal game chooses a uniformly random function once,
so repeated queries have consistent answers. The initial PRF interface uses `n`-bit keys, queries,
and answers, rejecting malformed queries identically in both games. Inversion accepts any preimage.

High-level programs are specifications: arbitrary Lean functions and arbitrary PMFs do not acquire
efficiency merely by appearing in `do` notation. `IsPPT` requires a machine realization;
`IsOraclePPT` requires one preserving the result and oracle state for every stateful handler.
There is currently no general compiler for `do` programs, unrestricted high-level PPT composition API,
expected-time model, or simulation-equivalence theorem with other machine models. Exact sampling from non-dyadic
distributions may require a different runtime convention or bounded sampling with failure.
[`IsOraclePPTOn`](../Computability/Probabilistic/Oracle.lean) connects multiple finite operation
names to the common machine core, with arbitrary word payloads and shared private state.
The single-operation `IsOraclePPT` contract is proved equivalent to its unary-parameter
specialization. [`OracleEncoding`](../Computability/Probabilistic/OracleEncoding.lean) adds typed
queries and dependent replies. Its certificate includes request construction and response
decoding against every word handler, including malformed replies. Encoding preserves the
typed program's full stateful semantics; it does not assume the operations are independent.

Deterministic word programs now have an optional
[`polytime`](../Tactic/PolyTime.lean) tactic. It synthesizes certificates for constants, copying,
concatenation, fixed maps and substitutions, filtering, Boolean folds, head/tail, and unary length.
It also handles bounded loops with length-nonincreasing bodies. A finite-state transducer compiler
justifies the primitives with a fixed machine and a linear runtime bound, including final output.
General deterministic composition uses the intermediate output-size bound to account for the
next call. These constructions reuse CSLib's `MultiTapeTM`, configurations, actions, and existing
subroutine plumbing.

[`Encoding`](../Computability/Probabilistic/Encoding.lean) supplies efficient pairing, projections,
and two-argument calls using the same binary representation as random-tape replay. The
Goldreich–Levin predictor call now combines these contracts to certify reuse of saved coins with
a freshly prepared query. Polynomial bounds on composed costs use Mathlib's `fun_prop` tactic;
these size bounds remain separate from computation certificates.

[`Fold`](../Computability/Probabilistic/Fold.lean) certifies ordinary `List.foldl` programs with
encoded elements and accumulators, including growing words and tuples. Its prefix invariant proves
both the result and the intermediate size bound. Collection `map` and `flatMap` obtain their growth
bounds from the supplied algorithm's certificate. Word folds, reversal, and `zipWith` reuse this
same implementation. `polytime` handles these collection combinators and word folds, including
supplied algorithms and simple constructor growth. The `_with` variants allow callbacks to capture
runtime data, such as saved coins or an image. The tactic handles these captures and nested maps,
charging for the environment and every generated element.
Boolean callbacks can return an ordinary word of votes. The Goldreich–Levin batch-prediction
certificate uses this interface to capture the parameter, image, and saved coins with `by polytime`.

[`Arithmetic`](../Computability/Probabilistic/Arithmetic.lean) provides unary addition,
multiplication, fixed powers, subtraction, comparison, and base-two logarithms. These certificates
compose with `polytime`; a variable exponent does not satisfy the fixed-power rule.

[`List`](../Computability/Probabilistic/List.lean) adds runtime indexing and slicing, interval
generation, captured predicates, first-match search, and word equality. All operate through the
same deterministic contracts; search retains the first matching element and has a computed default.

[`WordDecoder`](Computational/GoldreichLevin/WordDecoder.lean) uses these contracts to parse masks,
enumerate guesses, generate coordinate queries, XOR selected masks, compute parities, take majority
votes, and check candidates. Candidate generation is an ordinary nested map with a captured
predictor. Its efficiency proof uses helper certificates followed by `polytime`; no machine
configurations appear. The generated candidates and first-match search agree exactly with the
finite definitions, including order and duplicates. The logarithmic mask count is efficiently
computed at every fixed precision degree, and enumeration charges for its complete encoded output.

For growing loops, [`IsPolyTime.iterate_spec`](../Computability/Probabilistic/Iteration.lean)
combines an initialization proof, local invariant preservation, and a polynomial size bound.
It returns both the final invariant and the efficiency certificate, without requiring clients to
prove facts about machine configurations or complete execution traces. The
[`word-program examples`](../../CslibTests/ComputationalCryptoPrograms.lean) include synthesized
efficiency proofs and a growing loop whose one invariant establishes both output length and
polynomial time. Unknown algorithms still require certificates, and arbitrary unbounded
accumulators do not qualify for the finite-state fold rule.

The corresponding [adaptive probabilistic rule](../Computability/Probabilistic/Adaptive.lean)
certifies `OracleComp.iterate`: a strict PPT body and one invariant bound every reachable state
and give the final postcondition. The body can capture the original input. Separate
[error rules](../Languages/Probabilistic/Iteration.lean) add local failure probabilities across
adaptive rounds; correctness may fail with the stated probability, while the size bound must
hold on every path. The [examples](../../CslibTests/ComputationalCryptoIteration.lean) exercise
both interfaces without exposing the saved-coin implementation.

The [`ppt`](../Tactic/PPT.lean) tactic combines this deterministic interface with typed probabilistic
sequencing. It handles multiple random draws, captured inputs, runtime-dependent sampling lengths,
conditionals, and calls to certified adversaries. The full Goldreich–Levin inverter uses these
rules. It also handles fixed Boolean postprocessing of certified multi-operation and typed oracle
programs. General stateful oracle composition remains outside this automation interface.

Start with the short, checked
[`computational cryptography walkthrough`](../../CslibTests/ComputationalCryptoDemo.lean).
It writes the PRG experiment in `do` notation, certifies uniform sampling and fixed output encodings,
composes a certified parameter preparation with a random sample, constructs an efficient
answer-complementing reduction with exactly the same advantage, and applies
the polynomial hybrid theorem. It gives the finite decoder's candidate-list and recovery guarantee,
the seeded prediction-to-inversion bound, the Goldreich–Levin theorem, and the full one-bit PRG
construction from a one-way permutation.
Its proofs use the library's named lemmas without machine
bookkeeping. Efficient output encoding alone makes no claim of pseudorandomness.

The [reduction exercises](../../CslibTests/ComputationalCryptoReductions.lean) build on this
walkthrough. [`Computational/Stretch`](Computational/Stretch.lean) proves polynomial stretch
amplification through one uniform randomized hybrid reduction, with an exact dyadic loss bounded
by twice the positive iteration count. It also proves security under output truncation.
[`Computational/Reduction`](Computational/Reduction.lean) supplies the shared deterministic and
randomized postprocessing rules. The computational guide records the interface changes prompted
by these proofs: bounded-growth iteration, charged bounded-index sampling, and an averaging
hybrid theorem that does not require a separately supplied common negligible bound.

[`CslibTests/ComputationalCrypto.lean`](../../CslibTests/ComputationalCrypto.lean) exercises fair-coin
and oracle PPT witnesses, adaptive queries, persistent state, pause/resume across a query,
repeated-query behavior, and inversion. Output encoding checks cover clock exhaustion of a
nonhalting source, a bit emitted on a halting transition, and erasing output while preserving the
oracle's state change. The file also checks the diagonal counterexample to treating separate
fixed-hop negligible bounds as a uniform hybrid bound.
[`ComputationalCryptoClock`](../../CslibTests/ComputationalCryptoClock.lean) evaluates polynomial
budget generators from blank tapes, gives their uniform PPT certificate, and checks oracle cutoffs
against a handler that records the exact query transcript. It also evaluates the full tape
preparation directly and checks the complete compiler on a nonhalting source, zero budget, and
a query cutoff with additional runtime.
[`ComputationalCryptoComposition`](../../CslibTests/ComputationalCryptoComposition.lean) checks
random stopping times and pending queries, empty and nonempty buffered input, preservation of
displaced source heads, different source and continuation tape counts, and an adaptive PPT program
whose first random choice determines the length of its next sample.
[`ComputationalCryptoMachines`](../../CslibTests/ComputationalCryptoMachines.lean) compares the
shared evaluator with the original evaluator for every machine, configuration and fuel bound.
It also checks an oracle-free fair coin, PPT certificates for multiple operations, and typed game
operations sharing a lazy-sampled answer. The typed experiment has a seven-step realization
including reply decoding, and encoding preserves its lazy cache. A reusable
random-oracle theory and its lazy/eager equivalence theorem remain to be developed.
Direct transition checks also exercise workspace restoration through blank gaps and negative
positions, two successive invocations through the existing unary loop, and the zero-tape case.

### Further development

**One-way permutations imply pseudorandom generators** is proved, including strict uniform PPT
reductions, the Goldreich–Levin decoder, and one-bit expansion at every seed length. Stretch
amplification gives any efficiently computed strictly larger output length, with polynomial time
proved for the resulting generator and its reduction. The next target is **one-way functions
imply pseudorandom generators**; that implication is not yet proved.

The first steps on that route are checked: output collisions of general OWFs are negligible,
the strong leftover hash lemma applies to two-universal hashing with public seeds and side
information, and Boolean-matrix extraction has a uniform PPT implementation.
[`Computational/Extraction`](Computational/Extraction.lean) transfers computational
indistinguishability through this extractor, with an explicit high-entropy comparison-source
hypothesis. These ingredients do not yet complete the HILL generator construction.
Goldreich–Levin now handles arbitrary output lengths, and a separate uniform reduction supplies
fixed-output-length normalization. The finite entropy layer proves the chain rule and the
averaged hash-isolation bound from Lemma 3 of the write-up.
The [hashed parity pair](Computational/Pseudoentropy/HashPair.lean) now realizes that bound
with a strict PPT sampler, an exact sampling law, and an injective public encoding. Its
[finite prediction-to-inversion bound](Computational/Pseudoentropy/HashReduction.lean) handles
unequal fibers and saved predictor coins with an explicit cubic loss. The
[word reduction](Computational/Pseudoentropy/WordReduction.lean) proves the exact game
correspondences and certifies the inverter as strict PPT.
[`OneWay.exists_pseudoentropyPair`](Computational/Pseudoentropy/OneWay.lean) consequently gives
a samplable pseudoentropy pair from every general word OWF, with gap `1 / (2 * (n + 7))` below
the conditional-entropy prediction threshold. Its
[uniform seed realization](Computational/Pseudoentropy/Seed.lean) preserves the exact joint law
and accounts for unused coins in the entropy chain rule. Independent repetitions now have checked
conditional-information and conditional-mass concentration bounds, with loss measured against
the seed length. [Smoothed conditional extraction](../Probability/EntropyExtraction.lean) now
turns these bounds into statistical closeness while preserving the public marginal and hash seed.
The [hard-core boosting analysis](Computational/Pseudoentropy/Boosting/Progress.lean) proves the
potential decrease and finite round bound, following
[Holenstein's uniform hard-core proof](https://crypto.ethz.ch/publications/files/Holens05.pdf).
The [weight sampler](Computational/Pseudoentropy/Boosting/Sampling.lean) realizes dyadic soft
weights exactly with fair bits. Shared bounded repetition and success counting have strict PPT
certificates, independent product laws, and Hoeffding error bounds. A polynomial trial budget
gives inverse-polynomial accuracy with exponentially small failure. The sampled threshold
decisions now have [strict PPT programs and guard guarantees](Computational/Pseudoentropy/Boosting/Decision.lean),
including a bound on the error of the executable majority predictor. The
[clocked loop](Computational/Pseudoentropy/Boosting/Program.lean) now has a strict PPT certificate
and state-size bounds on every execution. Its [correctness theorem](Computational/Pseudoentropy/Boosting/Loop.lean)
connects the stored votes to the potential proof and bounds total error by the clock times the
sum of the two test errors and the learner error. It assumes a learner contract for the truncated
predictor descriptions. The [final clipped-vote predictor](Computational/Pseudoentropy/Boosting/Selection.lean)
now has an exact fair-bit implementation and a uniform empirical slope search. Its error bound
combines the dense-margin guarantee with explicit rounding, estimation, and selection-failure
losses. Explicit polynomial precisions preserve an inverse-polynomial prediction advantage.
The [complete training algorithm](Computational/Pseudoentropy/Boosting/Training.lean) now combines
the loop and final selection, with strict PPT training and observation-only prediction. Its
unconditional error bound includes guard errors, learner failures, and slope-selection failures.
Shared candidate selection has a strict PPT certificate and a reusable accuracy rule.
The [fresh-mask sampler](Computational/Pseudoentropy/Masking.lean) also has a strict PPT certificate
and conditional label entropy at least the soft-mask density, including weights that depend on
the hidden label. A strict PPT random-coordinate reduction now converts a sequence distinguisher
into a predictor with an exact weighted-bias identity. Its client efficiency proof is
`unfold coordinatePrediction; ppt`; the target's hidden label is never passed to the predictor.
The [saved predictor](Computational/Hybrid/SavedPrediction.lean) now has exact replay, strict PPT
sampling, and a description bound independent of the boosting state used to sample its examples.
Its total efficient evaluator accepts arbitrary word codes, and the checked size bound justifies
truncation before storage. The [concrete learner](Computational/Pseudoentropy/Boosting/Learner.lean)
samples orientations and selects descriptions by fresh weighted validation. A noticeable average
bias gives the loop's truncated-predictor contract with an explicit discovery-and-selection error;
the full learner is strict PPT. The [sequence reduction](Computational/Pseudoentropy/Learning.lean)
supplies that bias from a distinguishing gap of either sign. The
[complete sequence learner](Computational/Pseudoentropy/SequenceLearner.lean) now combines the
saved evaluator, adaptive learner, and final prediction program. A sequence gap against every
dense mask gives one prediction-error bound; its total sampling failure is negligible for
polynomial parameters and confidence at least `n`. An end-to-end test constructs the evaluator
from a certified sequence test and proves an eventual prediction advantage. The
[masked-source extraction bound](Computational/Pseudoentropy/MaskedExtraction.lean) now gives
the statistical error for every sufficiently dense vote collection, preserving all observations
and the public hash seed, including observations represented as arbitrary words. Its information
bound eventually charges only `n + 2` extra bits for any polynomial mask precision, independently
of its degree. The [dense-mask theorem](Computational/Pseudoentropy/DenseMask.lean) now applies
the uniform learner to a pseudoentropy pair. An
[explicit polynomial schedule](Computational/Pseudoentropy/ExtractionSchedule.lean) and the
[word extraction theorem](Computational/Pseudoentropy/WordExtraction.lean) give negligible
distinguishing advantage while retaining every observation and the complete matrix seed.
The client supplies efficient density and output schedules satisfying the entropy budget; all
sampling and hashing have strict PPT certificates. The three-source game argument, uniform
removal of unknown entropy parameters, and conversion into an expanding generator remain to
be proved. The [shared repeated extractor](Computational/Pseudoentropy/RepeatedExtraction.lean)
now handles arbitrary finite labels, including word seeds. The
[first and third statistical transitions](Computational/Pseudoentropy/SeedExtraction.lean)
use the same repetition schedule, preserve their public hash seeds, and permit empty outputs
when a component has no entropy. Their
[concrete word programs](Computational/Pseudoentropy/WordSeedExtraction.lean) now discharge the
hash-family premises through the shared matrix implementation. Observation padding uses a bound
derived from the sampler's PPT certificate, and the retained-seed extractor reveals every pair
output. A combined client has a strict PPT certificate; its full game argument remains to be
proved. The construction uses fresh soft masks; following the write-up's set-oracle
formulation would additionally require a cached membership simulation.
The [computational guide](Computational/README.md#toward-general-one-way-functions) records the
remaining obligations and cites
[Holenstein's write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf) and the
[original HILL theorem](https://doi.org/10.1137/S0097539793244708).

The semantic PRG family API introduced in
[#876](https://github.com/leanprover/cslib/pull/876) is integrated with the computational definition.
The real and ideal programs denote its experiments exactly, with the same advantage convention.
The one-way-permutation theorem concludes with this shared security property, and its reductions
can still use the program-based `ComputationallyIndistinguishable` interface.

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
