/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Tactic.PolyTime
public import Cslib.Computability.Probabilistic.Composition
public import Cslib.Computability.Probabilistic.Sampling

/-!
# Synthesizing certificates for probabilistic polynomial-time programs

`ppt` combines proved PPT sequencing and sampling rules with deterministic `polytime` rules.
It handles supported `do` programs without exposing a machine witness. A call to an unknown
algorithm still needs a local certificate. The current sequencing rules pass word-valued results;
they do not supply a compiler for arbitrary typed continuations or stateful oracle programs.
-/

public section

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PPT])]
  Cslib.Probability.isPPT_sampleBits
  Cslib.Probability.IsPolyTime.isPPT_word
  Cslib.Probability.IsPolyTime.isPPT

attribute [aesop safe apply (rule_sets := [PPT])]
  Cslib.Probability.IsPPT.map_word
  Cslib.Probability.IsPPT.map_bool

attribute [aesop unsafe 50% apply (rule_sets := [PPT])]
  Cslib.Probability.IsPPT.bind
  Cslib.Probability.IsPPT.bind_parameter
  Cslib.Probability.IsPPT.preprocess_word

/-- Synthesize a PPT certificate using sampling, composition, and deterministic efficiency rules. -/
macro "ppt" : tactic => `(tactic| solve | aesop (rule_sets := [PPT, PolyTime]))
