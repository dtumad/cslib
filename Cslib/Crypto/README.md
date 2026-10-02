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

## Plans and notes

### Computational security

[`Computational`](Computational) provides definitions of one-way functions and permutations,
pseudorandom generators,
and pseudorandom functions, following Arora and Barak, Boneh and Shoup, and Goldreich, Goldwasser,
and Micali. References appear in the modules. These are security definitions and elementary
metatheory, not constructions or existence proofs of secure primitives.

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
- [`Computational/Basic`](Computational/Basic.lean): negligible advantages, computational
  indistinguishability, complementing game answers, and the two-hop hybrid inequality, reusing
  Mathlib's superpolynomial decay.
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
  The final security lemma uses `OneWay` and explicitly requires PPT certificates for the full
  inverter at every fixed degree. These decoder and search certificates remain to be proved.

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
- [`Composition`](../Computability/Probabilistic/Composition.lean): `IsPPT.bind_parameter`
  composes a program returning an encoded `(parameter, input)` pair with a PPT continuation.
  The first program may choose the next parameter adaptively. Its output-length bound controls
  the second program's runtime, and all tape preparation is included in the polynomial bound.
  `IsPPT.bind` also composes ordinary word-valued programs at the same security parameter;
  `IsPPT.keep_parameter` certifies the machine that retains that parameter alongside the result.
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
The general machine core supports multiple operations; the current `IsOraclePPT` interface still
uses the compact single-operation presentation. Typed interface encodings and a general
multi-operation PPT interface remain to be connected to it.

Deterministic word programs now have an optional
[`polytime`](../Tactic/PolyTime.lean) tactic. It synthesizes certificates for constants, copying,
concatenation, fixed maps and substitutions, filtering, Boolean folds, head/tail, and unary length.
It also handles bounded loops with length-nonincreasing bodies. A finite-state transducer compiler
justifies the primitives with a fixed machine and a linear runtime bound, including final output.
General deterministic composition uses the intermediate output-size bound to account for the
next call. These constructions reuse CSLib's `MultiTapeTM`, configurations, actions, and existing
subroutine plumbing.

For growing loops, [`IsPolyTime.iterate_spec`](../Computability/Probabilistic/Iteration.lean)
combines an initialization proof, local invariant preservation, and a polynomial size bound.
It returns both the final invariant and the efficiency certificate, without requiring clients to
prove facts about machine configurations or complete execution traces. The
[`word-program examples`](../../CslibTests/ComputationalCryptoPrograms.lean) include synthesized
efficiency proofs and a growing loop whose one invariant establishes both output length and
polynomial time. Unknown algorithms still require certificates, and arbitrary unbounded
accumulators do not qualify for the finite-state fold rule.

The [`ppt`](../Tactic/PPT.lean) tactic combines this deterministic interface with uniform bit
sampling and word-valued probabilistic sequencing. It certifies ordinary `do` programs that sample
a word, run a certified deterministic computation, and invoke a certified adversary. Reading and
reassembling the security parameter and auxiliary input use public value-level rules. The PRG
experiment in the walkthrough now has a synthesized PPT proof from the generator and adversary
certificates. General typed continuations and stateful oracle composition remain outside this
automation interface.

Start with the short, checked
[`computational cryptography walkthrough`](../../CslibTests/ComputationalCryptoDemo.lean).
It writes the PRG experiment in `do` notation, certifies uniform sampling and fixed output encodings,
composes a certified parameter preparation with a random sample, constructs an efficient
answer-complementing reduction with exactly the same advantage, and applies
the polynomial hybrid theorem. It also gives the full one-bit PRG theorem from a permutation and
a hard-core predicate, the finite decoder's candidate-list and recovery guarantee, and the
seeded prediction-to-inversion probability bound in the word-based security game.
Its proofs use the library's named lemmas without machine
bookkeeping. Efficient output encoding alone makes no claim of pseudorandomness.

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
It also checks an oracle-free fair coin, two channels sharing one hidden state, and typed game
operations sharing a lazy-sampled answer. The latter is a small random-oracle example; a reusable
random-oracle theory and its lazy/eager equivalence theorem remain to be developed.
Direct transition checks also exercise workspace restoration through blank gaps and negative
positions, two successive invocations through the existing unary loop, and the zero-tape case.

### Further development

The next proof target is **one-way permutations imply pseudorandom generators**, using the
Goldreich–Levin hard-core predicate and a one-bit expansion. Closed PPT composition, the
ideal-distribution identity, and the hard-core-to-indistinguishability reduction are proved.
The two predictors in that reduction have uniform PPT certificates. The finite Goldreich–Levin
decoding bound, seeded randomized reduction, explicit polynomial-size parameter choice, and
word-based game correspondence are proved. Strict PPT predictors have an exact random-tape
representation with a certified polynomial-time deterministic evaluator. The asymptotic reduction
is proved with the inverter's PPT certificates as an explicit hypothesis. Certifying the decoder
and candidate search, then proving the padded permutation and efficient parity predicate, remain
before the full hard-core and OWP-to-PRG theorems can be assembled.
Polynomial-time subroutines now have workspace-restoring realizations suitable for repeated
invocations. Word primitives, deterministic composition, and an invariant rule for bounded loops
are certified; assembling the decoder's data transformations and candidate search remains.
The combined generator's deterministic
efficiency certificate is now proved using shared output concatenation. After that,
the target is **one-way functions imply pseudorandom generators**. Neither implication is proved yet.

The primitive-level PRG family API in merged
[#876](https://github.com/leanprover/cslib/pull/876) has also been reviewed. Connecting this
word-based computational interface to that semantic API remains to be done. Its admissibility
predicate applies to an entire adversary family, which allows a single uniform PPT witness to
supply the computational restriction.

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
