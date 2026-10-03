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

[`Stretch`](Stretch.lean) amplifies this one-bit generator to any efficiently computed output
length strictly greater than the seed length. `PseudorandomGenerator.amplify` takes the desired
length and its unary polynomial-time certificate. The checked
[reduction examples](../../../CslibTests/ComputationalCryptoReductions.lean) include the resulting
OWP-to-polynomial-stretch theorem, as well as two-step expansion and truncation.

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

## Toward general one-way functions

The general OWF-to-PRG theorem is not yet proved. We are following
[Holenstein's write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf), with the original
Håstad–Impagliazzo–Levin–Luby theorem credited below. A general one-way function can have an uneven
output distribution; appending a hard-core bit does not make that distribution uniform.

The first extraction ingredients are checked:

| Module | Proved result |
| --- | --- |
| [Goldreich–Levin](GoldreichLevin/WordReduction.lean) | Every OWF has the padded inner-product hard-core predicate. Output lengths may vary; the predictor's coin budget depends on its actual image. |
| [OneWay/Normalize](OneWay/Normalize.lean) | Every general word OWF yields an OWF with output length determined solely by input length, matching the write-up's fixed-width setting. |
| [OneWay/Collision](OneWay/Collision.lean) | Every OWF has negligible output collision probability. An independent uniform preimage guess is the PPT reduction; image lengths may vary. |
| [Collision](../../Probability/Collision.lean) | Collision probability on arbitrary discrete spaces, its finite sum formula, and a distance-to-uniform bound. |
| [UniversalHash](../../Probability/UniversalHash.lean) | The strong leftover hash lemma, including revealed side information and a pointwise mass-bound corollary. |
| [Conditioning](../../Probability/Conditioning.lean) and [Entropy](../../Probability/Entropy.lean) | Discrete conditional distributions, finite Shannon entropy in bits, and the deterministic entropy chain rule. |
| [HashIsolation](../../Probability/HashIsolation.lean) | Hash collisions bound the remaining predicate entropy. Averaging over hash lengths gives the logarithmic-fiber bound in Holenstein's Lemma 3. |
| [Pseudoentropy/HashPair](Pseudoentropy/HashPair.lean) | The hashed parity candidate, its complete entropy bound, and a strict PPT word sampler with exact distribution and injective public encoding. |
| [Guessing](../../Probability/Guessing.lean) and [Pseudoentropy/Reduction](Pseudoentropy/Reduction.lean) | Replacing partially uniform leakage by a uniform guess, with a concrete loss in decoder success. The unknown split point is used only in the proof. |
| [Pseudoentropy/HashReduction](Pseudoentropy/HashReduction.lean) | The finite matrix-hash prediction-to-inversion bound from Lemma 4, including unequal fibers, saved predictor coins, and an explicit cubic loss. |
| [Pseudoentropy/WordReduction](Pseudoentropy/WordReduction.lean) | A strict PPT inverter and exact agreement of both word games with the finite saved-coin experiments. |
| [Pseudoentropy/Basic](Pseudoentropy/Basic.lean) and [Pseudoentropy/OneWay](Pseudoentropy/OneWay.lean) | Every general word OWF yields a strict PPT samplable pseudoentropy pair with prediction gap `1 / (2 * (n + 7))`. |
| [Pseudoentropy/Seed](Pseudoentropy/Seed.lean) | Every such sampler has a polynomial-time deterministic evaluator driven by one uniform seed. The entropy chain rule counts all seed bits, including unused coins. |
| [Product](../../Probability/Product.lean), [Concentration](../../Probability/Concentration.lean), and [EntropyConcentration](../../Probability/EntropyConcentration.lean) | Independent finite products, their conditional laws, and Hoeffding bounds on conditional information and excessive conditional masses. |
| [EntropyExtraction](../../Probability/EntropyExtraction.lean) | Smoothed leftover hashing with public side information, followed by extraction from independent repetitions at almost their total conditional Shannon entropy. |
| [Pseudoentropy/Boosting](Pseudoentropy/Boosting/Progress.lean) | The clipped weight potential, the density invariant, per-round progress, and the finite clock bound for constructive hard-core boosting. |
| [Boosting/Sampling](Pseudoentropy/Boosting/Sampling.lean) | Exact fair-bit sampling of dyadic soft weights, a strict PPT certificate, and agreement with the density used in the potential proof. |
| [Boosting/Vote](Pseudoentropy/Boosting/Vote.lean) and [Boosting/Decision](Pseudoentropy/Boosting/Decision.lean) | Executable majority prediction, rational density and stopping tests, and their guard guarantees with exponentially small sampling error. |
| [Boosting/Program](Pseudoentropy/Boosting/Program.lean) and [Boosting/Loop](Pseudoentropy/Boosting/Loop.lean) | A strict PPT clocked loop, state bounds on every execution, and its majority-or-dense-margin guarantee with an explicit learner hypothesis and total error bound. |
| [Boosting/Clipped](Pseudoentropy/Boosting/Clipped.lean) and [Boosting/Selection](Pseudoentropy/Boosting/Selection.lean) | Exact dyadic randomized prediction, the lower-tail error bound, and uniform empirical selection of a slope with strict PPT certificates and explicit losses. |
| [Boosting/Training](Pseudoentropy/Boosting/Training.lean) | The complete training algorithm and observation-only predictor, their strict PPT certificates, and one prediction-error bound including guard, learner, and selection failures. |
| [Masking](Pseudoentropy/Masking.lean) | Fresh randomized labels with conditional entropy at least the soft-mask density, and a strict PPT sequence-to-prediction reduction with an exact weighted-bias identity. |
| [Prediction](Prediction.lean) and [Hybrid/Sequence](Hybrid/Sequence.lean) | Shared trial-bit prediction and independent-sequence hybrid combinators, with strict PPT certificates and an exact signed reduction loss. |
| [Hybrid/SavedPrediction](Hybrid/SavedPrediction.lean) | Strict PPT sampling of bounded predictor descriptions, total efficient evaluation, and exact agreement with the coordinate predictor on every bounded observation. |
| [Boosting/Learner](Pseudoentropy/Boosting/Learner.lean) and [Learning](Pseudoentropy/Learning.lean) | Uniform sampling, sign selection, and weighted validation turn a noticeable sequence gap into the boosting learner's correlation contract, with strict PPT certificates and explicit failure bounds. |
| [SequenceLearner](Pseudoentropy/SequenceLearner.lean) | One certified sequence test supplies the concrete adaptive learner and final strict PPT predictor. The complete sampling-failure bound is negligible for polynomial parameters and at least `n` confidence bits. |
| [MaskedExtraction](Pseudoentropy/MaskedExtraction.lean) | Extracting repeated soft-masked labels preserves all observations and the public hash seed. Its explicit statistical error bounds the loss in the sequence reduction; polynomial mask precision eventually adds at most `n + 2` information bits, independently of its degree. |
| [DenseMask](Pseudoentropy/DenseMask.lean) | A pseudoentropy pair's prediction bound gives every uniform sequence test a dense mask with any prescribed inverse-polynomial distinguishing bound and a lower bound on its positive probabilities. |
| [ExtractionSchedule](Pseudoentropy/ExtractionSchedule.lean) and [LabelExtraction](Pseudoentropy/LabelExtraction.lean) | An explicit polynomial repetition schedule makes label extraction computationally uniform under an admissible entropy budget, independently of the test's running-time degree. |
| [WordExtraction](Pseudoentropy/WordExtraction.lean) | Executable matrix hashing, exact agreement with the finite extraction laws, and a security theorem for ordinary strict PPT tests on observations, seed, and output. |
| [RepeatedExtraction](Pseudoentropy/RepeatedExtraction.lean) | One typed extractor and conditional-entropy bound for arbitrary finite labels, with public side information and a zero-bit case requiring no entropy. |
| [SeedExtraction](Pseudoentropy/SeedExtraction.lean) | Statistical extraction of public observations and remaining seed randomness, with every observation and label revealed in the latter experiment. Both use the label extractor's repetition schedule. |
| [MatrixExtraction](Pseudoentropy/MatrixExtraction.lean) and [WordSeedExtraction](Pseudoentropy/WordSeedExtraction.lean) | Concrete matrix extractors for all three components, with strict PPT certificates and exact finite laws. The observation and retained-seed security theorems discharge two-universality internally. |
| [ThreeSource](Pseudoentropy/ThreeSource.lean) | One strict PPT program combines the three extractors. Three game transitions prove computational indistinguishability from uniform under efficient schedules meeting the entropy budgets; every retained seed is counted in the exact output length. |
| [ThreeSource/Seeded](Pseudoentropy/ThreeSource/Seeded.lean) | A deterministic polynomial-time implementation uses exactly the original sampler coins and three matrix seeds. Its uniform-input distribution equals the sampled extractor's law, and every correctly sized input has the advertised output length. |
| [LinearHash](../../Computability/Probabilistic/LinearHash.lean) | Boolean-matrix hashing, its word implementation, its PPT sampler, and exact agreement with the finite extraction experiment. |
| [Extraction](Extraction.lean) | A source indistinguishable from a sufficiently diffuse comparison source yields computationally uniform extraction. |

`LinearHash.extract count input` draws `count * input.length` fair bits for the matrix and
returns that seed followed by `count` hash bits. Both experiments reveal the seed; all of its
randomness and output length are accounted for. The matrix family uses more seed bits than
Holenstein's field-multiplication family, but evaluation and seed length remain polynomial.
The [extraction examples](../../../CslibTests/ComputationalCryptoExtraction.lean) check this
public-seed distinction and give a complete client reduction through the computational API.
Matrix parsing, dot products, and uniform-tape laws now live in the shared
[bitstring programming module](../../Computability/Probabilistic/BitString.lean), also used by
Goldreich–Levin.

The shared [`wordDecode`](GoldreichLevin/WordDecoder.lean) accepts a predictor that captures
arbitrary runtime data. Its polynomial-time certificate, exact uniform-mask law, and
probability-of-recovery guarantee are separate reusable contracts. The existing hard-core
reduction uses this decoder; subsequent reductions can capture a public hash and digest too.

The [entropy examples](../../../CslibTests/ComputationalCryptoEntropy.lean) check the units,
conditioning direction, and null events. The isolation bound reveals the complete hash seed and
allows the hidden predicate to depend on that seed, as required when it also contains a parity
query. `HashPair.sample f n` samples a hash length, a matrix, a parity query, and an input, then
returns the encoded observation and parity bit. Its finite joint law satisfies Holenstein's
Lemma 3 bound. The hash length is exactly uniform in a power-of-two range `q = hashCount n`,
with `n + 6 ≤ q ≤ 2 * (n + 7)`. The extra lengths make the truncation threshold valid for every
fiber, and the dyadic range accounts for the sampling detail approximated in the write-up's
footnote 3.

`matrixInverter_success_ge` proves the finite Lemma 4 reduction: prediction correlation at least
`1 - H(hidden | observation) - 1/q` gives inversion probability at least
`1 / (128 * q * dyadicSize(16*q)^2)`. The inverter guesses a hash length, matrix, and digest,
then uses the shared decoder. It receives neither a fiber size nor a split point.
`matrixPrediction_entropy_le_of_coins` extends the bound to independent saved coins reused
throughout decoding. The [word reduction](Pseudoentropy/WordReduction.lean) now proves both
game correspondences and certifies the complete inverter as strict PPT. Its saved-coin evaluator
trims a common tape to each query's own budget, so varying digest lengths preserve the exact
prediction distribution.

[`OneWay.exists_pseudoentropyPair`](Pseudoentropy/OneWay.lean) combines this reduction with
output normalization and negligible inversion success. It returns a `SamplablePair` with gap
`1 / (2 * (n + 7))`. `SamplablePair.HasGap` follows Definitions 3 and 4 of the write-up:
every uniform PPT predictor eventually has signed correlation at most
`1 - H(hidden | observation) - gap`. The record includes an injective observation encoding,
the finite joint law, and an exact strict PPT sampler. The entropy examples also check that an
independent fair hidden bit cannot have a positive gap: unpredictability alone is insufficient.

`SamplablePair.exists_seedRealization` supplies the deterministic uniform-seed presentation used
by Definition 4 of the write-up. Its efficient evaluator comes from the sampler's checked machine
replay. The entropy chain rule accounts for the public observation, hidden bit, and remaining
seed. A regression example deliberately ignores one of two seed bits and proves that the ignored
bit remains in the third entropy term.

For a seed length `L`, `k` independent samples satisfy the conditional-information lower-tail bound
`Pr[sum information <= k H - t] <= exp(-2 t^2 / (k L^2))` for `t >= 0`.
The corresponding bound on excessive conditional masses is checked too, using Mathlib's
independence and Hoeffding theorems. This is a variant of the concentration step in Section 3.3:
it uses the complete seed length rather than claiming Proposition 1's sharper alphabet-size loss.
[`EntropyExtraction`](../../Probability/EntropyExtraction.lean) now supplies the smoothing and
extraction step. If conditional masses exceed `mass` only with probability `delta`, its error is
at most `2 * delta + sqrt(2 * |Output| * mass) / 2`. The bound averages over the original public
marginal, and both experiments reveal the complete independent hash seed. Conditioning is used
only in the proof; the extractor still runs on the original source.

`IsTwoUniversal.leftover_hash_pi_conditional` combines this result with concentration. Writing
`lambda = k H - t`, hashing to `m` bits has error at most
`2 exp(-2 t^2 / (k L^2)) + sqrt(2^(m + 1 - lambda)) / 2`.
This is our seed-length variant of Lemma 2. The extraction examples instantiate it for any
samplable pair through its saved-seed interface. They also check a rare fully leaked branch:
leakage on one of sixteen branches still permits a nontrivial bound, without a worst-case
conditional-entropy assumption on every branch.

The [boosting analysis](Pseudoentropy/Boosting/Progress.lean) follows Section 2.2 of Holenstein's
[uniform hard-core proof](https://crypto.ethz.ch/publications/files/Holens05.pdf).
`step_progress` proves a decrease of `gamma * delta^2 / 8` after charging for an optional
threshold increase. `dense_margin_of_iterations` gives positive average prediction advantage on
every `delta`-dense soft set after `steps * gamma^2 * delta^3 >= 4` valid rounds.
The proof handles equality at the clock boundary and permits arbitrary finite source distributions;
soft sets avoid rounding cardinalities.

The [weight sampler](Pseudoentropy/Boosting/Sampling.lean) implements this curve exactly at
dyadic rates, using vote counts, saturating natural subtraction, and a bounded fair-bit draw.
Its acceptance probability agrees with the weight in the potential proof, and averaging over
source examples gives exactly the soft density. Each call uses fresh randomness; modeling a
fixed random set would additionally require caching repeated membership answers.
The [boosting examples](../../../CslibTests/ComputationalCryptoBoosting.lean) check clipping,
weighted prediction, an exact clock boundary, and independence of repeated draws. The example
`weightTrials` counts polynomially many sampled weights; its strict PPT proof is
`unfold weightTrials; ppt`. Its cubic budget estimates the weight to tolerance `1 / (n + 1)`
with failure at most `2^(-n)`. `sampleWeight_density_deviation` supplies the analogous concentration
bound when every trial samples a fresh source example before drawing its weight coin.

The [fresh-mask sampler](Pseudoentropy/Masking.lean) instead uses each sampled weight to decide
whether to replace the label by a fresh fair bit. Its conditional label entropy is at least the
soft density, even when the weight depends on the hidden label. This follows from general
entropy concavity and the fact that revealing less information cannot reduce conditional entropy.
The [masking examples](../../../CslibTests/ComputationalCryptoMasking.lean) check hidden-label
masks, fresh randomness on repeated inputs, and a complete sampler whose efficiency proof is
`unfold maskedTraining; ppt`.

`maskedSequencePredictor` now turns a test on repeated samples into one uniform predictor. It
samples a coordinate, fills the earlier positions with fresh masked examples and the later
positions with original examples, and inserts a trial bit next to the target observation.
Its signed mask-weighted prediction bias equals the complete sequence distinguishing gap
divided by `dyadicSize count`. The target's hidden label and mask are absent from the predictor's
inputs. The shared [sequence hybrid](Hybrid/Sequence.lean) proves this exact loss even when
adjacent gaps have different signs, including zero repetitions and rejected padding indices.
The complete client certificate is `unfold coordinatePrediction; ppt`.

[`SavedPrediction`](Hybrid/SavedPrediction.lean) saves the sampled surrounding examples, trial
bit, and test coins into a word. `exists_evaluator` supplies one deterministic polynomial-time
evaluator with the same prediction distribution at every observation within the chosen width.
The description contains the sampled data; it does not recursively store the boosting state used
to generate those data. `length_sample_le` bounds every description in terms of the public test
parameter, repetition count, observation width, and fixed test clock. The checked client examples
prove that the boosting loop's truncation preserves prediction whenever its bound covers this
size. Both the decoder and evaluator are total on arbitrary words, and no efficient inverse of
the abstract parameter or observation encoding is assumed. The learning reduction requires replay
only on observations in the source's support.

The [concrete learner](Pseudoentropy/Boosting/Learner.lean) validates a saved predictor on fresh
labeled examples. It draws the example's weight coin, checks the prediction if that coin accepts,
and otherwise returns a fair bit. Its validation bias is exactly half the weighted correlation.
`learn` draws signed descriptions and selects by repeated validation; the orientation is sampled
and tested uniformly. If the average validation probability differs from `1/2` by at least `1 / r`,
then the learned predictor has weighted correlation at least `1 / (2 * r)`, except with probability
`(((confidence + 1) * (4 * r)^2) + 1) * 2^(-confidence)`.

`learn_goodPredictor_error_pow` gives the loop's actual contract, including truncation, when the
code bound covers the descriptions and `gamma ≤ 1 / (2 * r)`. The shared `sampleBest` combinator
handles discovery and empirical selection on arbitrary encoded candidate types, while preserving
description bounds on every execution. The complete learner's client certificate composes with
`ppt`. The [sequence bridge](Pseudoentropy/Learning.lean) supplies its average bias from a
distinguishing gap of either sign and the saved evaluator's replay law.

[`MaskedExtraction`](Pseudoentropy/MaskedExtraction.lean) now supplies the statistical estimate
for the fresh-mask route. If every supported source outcome has probability at least `2^(-L)`,
the dyadic mask adds at most `log₂(bound) + 2` information bits. This depends on its sampling
precision, independently of the time spent computing votes. For every polynomial precision
family, `maskedSample_weight_mass_ge_eventually` improves the bound to `L(n) + n + 2` for all
sufficiently large `n`, simultaneously for every vote collection and threshold. The starting
index may depend on the precision family; the added information bound does not depend on its
degree. Thus the concentration estimate does not force the generator's repetition exponent to
depend on the distinguisher.

`extractLabels` hashes ordinary lists of labels and retains every observation and the complete
hash seed. The shared [`RepeatedExtraction`](Pseudoentropy/RepeatedExtraction.lean) module's
`extractLabels_distance_le` transfers the conditional-entropy estimate to this program;
`maskedSample_weight_extract` instantiates it with the soft density. The client proof for repeated
sampling and matrix hashing is `unfold extractTraining; ppt`. The tests also instantiate the bound
with a mask that depends on the hidden label and a constant word observation. Public observations
may live in an infinite type: extraction first reveals the finite source draw, then forgets it
through the observation map.
`extractedSequence_learn_error_pow` then pays this extraction error before applying the learner:
advantage at least `epsilon + dyadicSize count / r` yields the stated correlation guarantee.
The asymptotic application below supplies uniform repetition and precision choices.

The [sampled decisions](Pseudoentropy/Boosting/Decision.lean) implement the overlapping density
and majority guards from Figure 2 and Claim 2.6 of the uniform hard-core write-up. With weight
rate `eta = gamma * delta`, the density comparison uses `delta * (1 + eta / 32)`; the majority
comparison uses `13 * delta / 32`. The checked contracts allow either answer in each overlap
and bound an invalid answer by `2^(-k)`. Natural inverse bounds supply polynomial precision:
`32 * inverseGamma * inverseDelta^2` for the density test and `32 * inverseDelta` for majority.
`testShift_weights_sound` connects fresh weight trials to the potential's density.
`testMajority_source_sound` certifies the actual majority predictor on a valid stopping result,
including ties and the empty collection. The examples `majorityStop` and `densityShift` compose
an arbitrary certified training sampler; both efficiency proofs close with `unfold ...; ppt`.

The shared [adaptive loop rule](../../Computability/Probabilistic/Adaptive.lean) now certifies
strict PPT iteration from a state-size invariant, including bodies that capture the original
input. Its [probability rule](../../Languages/Probabilistic/Iteration.lean) adds the sampled
guards' failure bounds across rounds without requiring independence between rounds.

The [clocked boosting program](Pseudoentropy/Boosting/Program.lean) now composes these interfaces.
Each round tests the majority, optionally shifts the threshold, and calls the supplied learner.
Predictor descriptions are truncated before storage, so `run_isPPT` covers every execution,
including incorrect tests and learner failures. Its state invariant bounds both the number of
predictors and the size of every stored description; the client proof contains no machine internals.

The [loop correctness proof](Pseudoentropy/Boosting/Loop.lean) follows the actual stored votes.
If the learner supplies weighted correlation `gamma` on each dense measure except with
probability `epsilon`, `run_sound` bounds total failure by
`clock * (2 * 2^(-confidence) + epsilon)`. The result is either a majority predictor of error
at most `7 * delta / 16` or a collection with the required margin on every dense soft set.
The learner's contract concerns its **truncated** description. A checked visible-label example
instantiates that contract with a perfect learner and gives total error at most `2^(-n)`.

The [clipped predictor](Pseudoentropy/Boosting/Clipped.lean) samples exactly the clipped affine
probability determined by an observable vote word. A fractional lower tail proves the ideal
error bound for arbitrary finite source distributions. The cutoff occurs only in the proof;
the [uniform selection program](Pseudoentropy/Boosting/Selection.lean) tries a finite dyadic
slope grid and selects by empirical correctness on fresh labeled examples.
`State.Successful.selectSlope_error` connects this program to the loop's dense-margin branch.
With grid denominator `D = dyadicSize precision` and inverse tolerance `t > 0`, it gives error
at most `delta / 2 - gamma * delta^3 / 16 + clock / (2 * D) + 2 / t`, except with probability
`(D + 1) * 2^(-confidence)`. Both the predictor and the complete grid search have strict PPT
certificates. The explicit choice `t = 128 * inverseRate * denominator^2` and grid bound
`clock * t` leaves error at most `delta / 2 - 1 / t`; the majority branch satisfies the same
bound. `State.Successful.selectSlope_advantage` proves this inverse-polynomial advantage, and a
client example certifies the configured search with `unfold ...; ppt`.

The [complete training algorithm](Pseudoentropy/Boosting/Training.lean) composes the loop and
final selection. `train_sound` bounds the probability of returning a model with error above
`delta / 2 - 1 / t` by `clock * (2 * 2^(-confidence) + epsilon) + (D + 1) * 2^(-confidence)`.
`train_predict_error` adds this failure probability to the prediction-error bound, averaging over
all training runs and prediction coins. Training and applying the resulting model have separate
strict PPT certificates; the predictor receives only the public observation. The visible-label
example checks the full program with an error bound of `1/4 - 1/1024 + 2^(-n)`.

[`SequenceLearner`](Pseudoentropy/SequenceLearner.lean) supplies the concrete learner for this
training algorithm. `exists_evaluator` obtains one fixed efficient evaluator from the sequence
test's certificate. Each round samples bounded descriptions against its current mask, chooses
their orientation by fresh validation, and stores the selected description. `predict_error`
turns a distinguishing gap against every dense masked sequence into prediction error at most
`delta / 2 - 1 / t + failureBound`. The bound covers all guards, learning, and final selection.
For polynomial parameters and confidence at least `n`, it is negligible and eventually at most
`1 / (2 * t)`.

The [sequence learner example](../../../CslibTests/ComputationalCryptoSequenceLearner.lean)
starts from a certified test on visible labels and constructs the entire strict PPT predictor.
It proves eventual error at most `1/4 - 1/32768`, including the actual sampled learner's failures.

[`HasGap.eventually_exists_mask`](Pseudoentropy/DenseMask.lean) applies the learner to a
pseudoentropy pair. Every certified sequence test eventually admits a mask of the requested
density with distinguishing advantage below `dyadicSize count / inverseGap`. Its density and
precision schedules are polynomial-time computations, and every positive mask probability has
an explicit inverse-polynomial lower bound. This is the dense-mask consequence needed for the
sequence reduction. The proof uses fresh soft masks and a clocked learner; it does not implement
the write-up's worst-dense-set stopping test or a cached set-membership oracle.

[`HasGap.extract_word_labels`](Pseudoentropy/WordExtraction.lean) now combines this consequence
with statistical extraction. If `L` is the sampler's seed length, set
`count = 32 * (n + 1) * (L + n + 2)^2 * (inverseSlack + 1)^2` and
`slack = 8 * (n + 1) * (L + n + 2)^2 * (inverseSlack + 1)`.
For an efficiently computed dyadic density `delta <= H(label | observation) + gap`, the budget
`outputBits + 2 * slack <= count * delta` suffices for negligible distinguishing advantage.
Eventually the statistical error is at most `2 * exp(-4 * (n + 1)) + 2^(-n)`, and the repetition count
does not depend on the test's running-time degree. Both experiments reveal every observation
and the full matrix seed. Sampling, hashing, and padding are charged to strict PPT through the
ordinary word interface. The [extraction examples](../../../CslibTests/ComputationalCryptoExtraction.lean)
instantiate the numerical budget at a known half-bit threshold.

The [first and third statistical transitions](Pseudoentropy/SeedExtraction.lean) now use that
same schedule. `observation_word_extraction` hashes the sampled public observations below their
Shannon entropy. `remainingSeed_word_extraction` hashes the complete original seeds below
`L - H(observation) - H(label | observation)`, retaining every observation and label. Both
preserve their independent public hash seed and allow zero output bits without a positive entropy
budget. The retained-seed sampler is strict PPT and exactly realizes the finite experiment,
including unused coins. The generic `extractLabels` accepts word labels as well as Boolean labels.
The [concrete programs](Pseudoentropy/WordSeedExtraction.lean) discharge the hash-family premises
using the shared matrix implementation. `extract_word_observations` pads variable-length
observations injectively; `SamplablePair.exists_observationBound` obtains an efficient padding
bound directly from the PPT sampler, with no bound required on impossible observations.
`extract_word_seeds` hashes concatenated fixed-width seeds while preserving all pair outputs.
[`HasGap.extract_three`](Pseudoentropy/ThreeSource.lean) proves the combined program secure by
replacing the retained-seed component, then the labels, then the observations with uniform bits.
The first and last transitions are statistical. The middle reduction is an ordinary PPT program
that computes the observation hash and supplies the independent third component before calling
the distinguisher. The extraction examples obtain efficiency certificates for both the sampled
and deterministic clients, then transfer the complete security theorem to the deterministic
output using the exact seeded law. They assume three half-bit entropy thresholds and do not yet
establish expansion; no machine internals appear in the client.

`ThreeSource.length_extract` proves the exact output length on every supported execution.
The seed ledger also proves that retaining the three matrix seeds cancels their contribution to
the expansion inequality: the three digest lengths must sum to more than `count * L`.
[`ThreeSource.Seeded`](Pseudoentropy/ThreeSource/Seeded.lean) realizes that ledger directly.
`eval_generate_of_realization` identifies its uniform-input distribution with the sampled
extractor, and `length_generate` gives the exact output length for every correctly sized seed.
Parsing reuses the shared matrix row reader; `polytime` certifies the supplied evaluator calls,
word slicing, and hashing. No additional replay-clock padding is charged to this implementation.

`ComputationallyIndistinguishable.extract_uniform` still assumes its comparison source and
negligible collision bound. Negligible collisions of the OWF output alone do not give the entropy
surplus required for expansion. The remaining route needs removal of unknown entropy parameters
by a uniform reduction and a final generator with stretch
at every seed length. In the write-up's entropy grid, each candidate must first be amplified
enough to pay for all candidates' independent seeds before their outputs are combined by XOR.
The extraction theorem above requires efficient schedules; it does not permit entropy-dependent
advice chosen separately at each input length.

## Definitions and conventions

Cryptographic definitions live in `Cslib.Crypto`; efficiency predicates and encodings live in
`Cslib.Probability`.

| Module | Main interface |
| --- | --- |
| [Game](../Game.lean) and [Basic](Basic.lean) | Shared `Negligible`, game probabilities and advantages, `IsPPTTest`, and `ComputationallyIndistinguishable`. |
| [Ensemble](Ensemble.lean) | Polynomial bounds on sample lengths, connecting time polynomial in parameter plus input length to time polynomial in the parameter. |
| [Hybrid](Hybrid.lean) | Polynomially many game hops with a common negligible bound on adjacent advantages. |
| [Statistical](Statistical.lean) | Negligible statistical distance implies computational indistinguishability, including word ensembles. |
| [Reduction](Reduction.lean) | Efficient deterministic and randomized postprocessing of indistinguishable ensembles. |
| [OneWay](OneWay.lean) | `OneWay`, `OneWayPermutation`, and the inversion game, which accepts any preimage. |
| [HardCore](HardCore.lean) | `HardCore`, the prediction game, and PRG security from a hard-core predicate. |
| [PseudorandomGenerator](PseudorandomGenerator.lean) | `PseudorandomGenerator`: efficient evaluation, length expansion, and the shared `PRG.Family.Secure` property. |
| [Stretch](Stretch.lean) | Uniform reductions for polynomial stretch amplification and output truncation. |
| [PseudorandomFunction](PseudorandomFunction.lean) | `PseudorandomFunction` and adaptive oracle games with `n`-bit keys, queries, and answers. |

A closed game has type `ProbComp Bool`; `winProbability` is its probability of returning `true`.
Distinguishing advantage is the absolute difference of two acceptance probabilities. `Negligible`
uses Mathlib's superpolynomial decay. Security quantifies over an entire uniform adversary before
requiring its advantage to be negligible, so the negligible bound may depend on that adversary.

One-wayness, hard-core security, PRG security, and PRF security all use `Game.Secure`.
For inversion the ideal game always rejects; for prediction it returns a fair coin.
The familiar success-probability and prediction-bias formulations remain available as
`OneWay.inversion_negligible` and `HardCore.unpredictable`. Security records expose named
efficiency and security fields, rather than nested conjunctions.

The [semantic game calculus](../Game/Hybrid.lean) supplies symmetry, transitivity, reductions,
polynomial losses with negligible error, and polynomial hybrid arguments independently of machines.
[Statistical security](../Game/Statistical.lean) uses the same calculus: Boolean advantage equals
statistical distance, and every randomized test contracts that distance. The metric works on
arbitrary PMFs, including infinite word spaces and families whose sample type changes with `n`.

PRG security uses the same [`PRG.Family.Secure`](../Primitives/PRG/Asymptotic.lean) definition as
finite semantic generators. Its seed and ideal distributions are `uniformBits n` and
`uniformBits (length n)`, and `IsPPTTest` supplies the uniform computational restriction.
`PseudorandomGenerator` adds named `polyTime`, `length_eq`, and `stretch` fields to this `secure`
field. A reduction can construct it with `PseudorandomGenerator.of_indistinguishable` and recover
the program-based security statement with `.indistinguishable`. The equivalence is proved for all
word ensembles, without an efficient-sampling assumption on either ensemble.

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
- `IsPPT outputEncoding adversary` is definitionally `IsPPTOn` with `parameterEncoding`.

Use [`polytime`](../../Tactic/PolyTime.lean) for supported deterministic combinations and
[`ppt`](../../Tactic/PPT.lean) for closed probabilistic programs. Calls to supplied algorithms
need their own certificates, as in the example above. These tactics assemble proofs from the
public closure rules; a Lean function type alone supplies no efficiency bound.

The main programming interfaces are [composition](../../Computability/Probabilistic/Composition.lean),
[encodings](../../Computability/Probabilistic/Encoding.lean),
[folds](../../Computability/Probabilistic/Fold.lean),
[bounded probabilistic repetition](../../Computability/Probabilistic/Repeat.lean),
[adaptive iteration](../../Computability/Probabilistic/Adaptive.lean), and
[list operations](../../Computability/Probabilistic/List.lean).
The `_with` combinators let callbacks capture runtime inputs. For growing loops,
[`IsPolyTime.iterate_spec`](../../Computability/Probabilistic/Iteration.lean) uses one invariant
to prove the final postcondition and bound intermediate sizes. A polynomial number of iterations
also needs this size control to yield a polynomial-time algorithm.

`OracleComp.iterate count step initial` feeds each random state into the next round.
`IsPPTOn.iterate_spec` proves strict PPT and the final postcondition from one invariant;
`iterate_with_spec` lets the body capture the input, and `iterate_of_bounded_growth` derives
the size bound for fixed growth per round. The [adaptive examples](../../../CslibTests/ComputationalCryptoIteration.lean)
include state-dependent word updates, a process that stops drawing after failure, and
input-dependent sampling precision. Their proofs contain no machine configurations.

The size invariant must hold on every possible execution. Correctness invariants may instead
have per-round failure bounds: `ProbComp.iterate_failure_toReal_le` adds these bounds, and
`iterate_failure_toReal_le_mul` gives `count * error` for a common bound. Each local bound is
needed only where the preceding correctness invariant holds. No independence or finite-state
assumption is required.

`OracleComp.replicate count program` collects independent runs of a closed program, and
`OracleComp.countTrue count program` counts successful Boolean runs. If the program is strict
PPT and the unary count is polynomial time, `ppt` certifies either combinator. Output types may
be infinite; the list encoding charges for the complete result. Their exact product laws are
proved separately from efficiency in [Repeat](../../Languages/Probabilistic/Repeat.lean).
The [concentration interface](../../Languages/Probabilistic/Concentration.lean) bounds the error
of `countTrue` divided by the number of trials. For tolerance `1 / t`, where `t > 0`, the budget
`(k + 1) * t^2` gives failure probability at most `2^(-k)`. The program returns a natural count;
real arithmetic belongs to its correctness statement.
`OracleComp.testProbabilityLT count numerator denominator program` compares that empirical rate
to a rational threshold using natural cross-products. Its correctness contract gives overlapping
upper and lower guards with the same error bound, so reduction proofs can use the guards without
exposing their sampling implementation.

`OracleComp.selectBest count trials test` compares empirical acceptance probabilities and returns
the best candidate index. Its [strict PPT certificate](../../Computability/Probabilistic/Selection.lean)
composes an indexed trial program and efficient unary counts; `ppt` applies it automatically.
The [correctness rule](../../Languages/Probabilistic/Selection.lean) loses twice the estimation
tolerance relative to every candidate and charges one failure term per candidate. Both the indices
and success counts are bounded on every execution. The boosting slope search uses this rule;
its entire client efficiency proof is `unfold selectSlope; ppt`.

## Writing reductions and improving the interfaces

The [reduction examples](../../../CslibTests/ComputationalCryptoReductions.lean) exercise actual
client proofs. Stretch amplification repeatedly expands an `n`-bit seed prefix, saving each new
bit in the suffix. Its reduction samples a hop, adds the earlier uniform suffix, completes the
remaining expansions, and calls the original distinguisher. Its PPT proof composes the sampler,
the certified iteration, and the supplied adversary with `ppt`.

`PRGStretch.advantage_eq` gives the exact reduction loss
`2 ^ (Nat.log 2 (count n) + 1)`. For positive counts, `advantage_le` bounds this by `2 * count n`.
The hop is sampled by one uniform algorithm; it is not selected separately at each input length.
The sampler assigns unused indices to a rejecting branch on both sides. Thus the reduction uses
a bounded number of fair bits even when the number of hops is not a power of two.

The first exercises led to these shared interfaces:

| Friction in the client proof | Framework change |
| --- | --- |
| A common negligible hop bound was an additional obligation. | `Game.advantage_hybrid_average` telescopes signed gaps for one randomized reduction. |
| Choosing a hop needed a strict fair-coin sampler with a charged unary result. | `sampleBoundedIndex` uses logarithmically many bits and saturating binary decoding; the bound itself marks rejection. |
| Repeated expansion grows its accumulator. | `IsPolyTime.iterate_encoded_of_bounded_growth` derives the loop size bound; the old shrinking-loop rule is its zero-growth specialization. |
| Truncation and fresh random padding repeated the same reduction argument. | `ComputationallyIndistinguishable.map` and `.bind` preserve security under certified postprocessing, without sampling assumptions on the original ensembles. |
| Inferring a transformation from its certificate left ambiguous function arguments. | Postprocessing maps and truncation targets are explicit arguments. |
| A certified callback with an abstract output encoding failed under nested captured inputs. | `polytime` reduces the constructed argument tuple before matching the callback; the supplied certificate remains necessary. |
| Similar implementations caused proof search to select unrelated program certificates. | `PolyTime.applyHead` and `PPT.applyHead` share dispatch by the program's syntactic head before unification. |
| Reading fields of a certified tuple-valued callback required separate field certificates. | `polytime` derives projections of explicit tuple encodings automatically and composes functions of the security parameter through its input encoding. |
| Simplifying large fixed unary parameters exhausted recursion depth. | `polytime` certifies fully specified constant outputs before expanding their representation. |
| A prediction callback returned a conditional Boolean with a captured negated bit. | Boolean postprocessing handles fixed unary operations, conditional singleton results, and constructed output encodings. |
| Repeated-sample hybrids required coordinate bookkeeping. | `sequenceTest` simulates the surrounding lists and preserves the exact signed gap; `bitPredictor` shares the prediction step with the existing hard-core proof. |
| A weak learner needed to sample candidates and select one reliably. | `sampleBest` composes discovery and empirical selection, carries support bounds through failures, and has a synthesized strict PPT certificate. |

For example, truncation is a short client proof:

```lean
example {generator : Word → Word}
    (h : PseudorandomGenerator generator (fun n => 3 * n + 1)) :
    PseudorandomGenerator (fun seed => (generator seed).take (2 * seed.length + 1))
      (fun n => 2 * n + 1) :=
  h.truncate (fun n => 2 * n + 1) (by polytime) (by intro n; lia) (by intro n; lia)
```

These exercises use the existing machine realizations. They do not extend stateful oracle
composition, which remains the next distinct programming-interface challenge.

## What a PPT certificate means

`Word` is `List Bool`. Fixed-width strings `Fin n → Bool` are used in the finite probability
arguments, with explicit bridges to word programs. Input encodings determine the size measure;
output encodings are injective. The standard adversary input is a unary security parameter,
a delimiter, and an auxiliary word.
Use `pairEncoding` for pairs and `BitString` for fixed-width words; the PRF evaluator and the
general programming interface share these representations. A checked polynomial-time equivalence
with the former PRF pair encoding ensures this change preserves the evaluator requirement.

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
Different interfaces can share one hidden state.
[`IsOraclePPTOn`](../../Computability/Probabilistic/Oracle.lean) certifies typed inputs and results
with finitely many operation names and word payloads. It requires a single finite machine preserving
the joint distribution of the result and final oracle state for every stateful handler.
Its clock counts local computation, writing queries, and reading answers; the oracle's own work
is external. The existing `IsOraclePPT` interface is proved equivalent to its single-operation,
unary-parameter specialization.

[`OracleEncoding`](../../Computability/Probabilistic/OracleEncoding.lean) handles typed queries and
dependent response types. Its `IsPPTOn` certificate covers the translated program against every
word handler, including malformed replies. Request construction and response decoding are thus
charged to the machine. A round-trip theorem recovers the typed program's result and final private
state against every typed handler. The word interface is an exact specialization.

`ppt` supports these oracle certificates for machine runs and Boolean postprocessing.
General stateful oracle sequencing still requires further machine plumbing: running an unused
branch or clearing an unfinished query with a dummy call can change observable oracle state.
The closed-program sequencing and conditional rules cannot simply be reused for these effects.

The [PRF ideal game](PseudorandomFunction.lean) samples one random function and reuses it, so
repeated queries agree. The [machine examples](../../../CslibTests/ComputationalCryptoMachines.lean)
also include a typed two-operation PPT program, a shared lazy-sampled oracle, and a check that
encoding preserves its cache. A reusable random-oracle theory and
an eager/lazy equivalence theorem remain future work, as does the implication from general
one-way functions to PRGs.

## Sources and further reading

The general OWF-to-PRG construction is the theorem of Johan Håstad, Russell Impagliazzo,
Leonid Levin, and Michael Luby, *A Pseudorandom Generator from Any One-Way Function*,
SIAM Journal on Computing 28(4), 1999,
[DOI](https://doi.org/10.1137/S0097539793244708).
Our guide for the general construction is Thomas Holenstein,
*Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness*,
TCC 2006, [write-up](https://crypto.ethz.ch/publications/files/Holens06.pdf).
Section 3.3 supplies the collision-probability proof of the leftover hash lemma; Sections 4–5
give the pseudo-entropy-pair construction and its conversion to a PRG. The general implication
is not yet formalized here: uniform removal of unknown entropy parameters and expansion at every
seed length remain. The three-source game argument and its exact deterministic implementation
are checked for efficient schedules meeting the entropy budgets. We cite individual results in the
modules that formalize them and distinguish these proved ingredients from the full theorem.
For the constructive uniform hard-core argument we also follow Thomas Holenstein,
*Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2,
[write-up](https://crypto.ethz.ch/publications/files/Holens05.pdf). The checked potential analysis
and clocked program with its concrete sequence learner are ingredients of that uniform reduction.

The module docstrings cite the underlying mathematics: Arora–Barak and Boneh–Shoup for the
security definitions, and Goldreich–Levin with Trevisan's lecture notes for the decoding argument.
[Decoding](GoldreichLevin/Decoding.lean) explains the direct-coordinate variant used here.
The [probabilistic language](../../Languages/Probabilistic/Basic.lean) credits VCVio for the related
separation of oracle syntax and interpretation. The [Crypto overview](../README.md) records
machine reuse and port provenance. The [semantic PRG API](../Primitives/PRG/Defs.lean) and this
computational development share game semantics and security definitions.
