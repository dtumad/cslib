/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.BitString
public import Cslib.Computability.Probabilistic.Encoding
public import Cslib.Foundations.Data.BitString
public import Cslib.Crypto.Game

/-!
# Pseudorandom functions

The first interface uses `n`-bit keys, queries and answers. A distinguisher receives the unary
security parameter and adaptive oracle access, starting with an empty auxiliary input. The real
game samples one key; the ideal game samples one entire function and reuses it for every query.
Consequently, repeated queries get the same answer. Malformed queries get the empty word in both
games. Sampling the exponentially large ideal table is a specification, with no efficiency claim.

The family must have a deterministic polynomial-time evaluator on an explicit binary encoding of
the key and query. Adversaries must satisfy `IsOraclePPT`, which measures ordinary computation and
query construction, not merely the number of oracle calls.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
* O. Goldreich, S. Goldwasser, S. Micali,
  [*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- An adaptive oracle distinguisher, with an optional auxiliary input. -/
abbrev OracleDistinguisher := ℕ → Word → OracleComp Word (fun _ => Word) Bool

/-- The keyed oracle rejects queries outside the `n`-bit domain. -/
def prfOracle (family : Word → Word → Word) (n : ℕ) (key query : Word) : Word :=
  if query.length = n then family key query else []

/-- A single fixed random table, extended to malformed queries by the same rejection convention
as the real oracle. Reading with `getD` is used only under the exact-length guard. -/
def randomFunctionOracle (n : ℕ) (table : BitString n → BitString n) (query : Word) : Word :=
  if query.length = n then List.ofFn (table (fun i => query[i.val]?.getD false)) else []

/-- Sample one key and use it for all calls made by the adversary. -/
noncomputable def prfRealGame (family : Word → Word → Word) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let key ← OracleComp.sample (uniformBits n)
  OracleComp.simulate (fun query => pure (prfOracle family n key query)) (adversary n [])

/-- Sample one uniformly random function, retaining it across adaptive and repeated calls. -/
noncomputable def prfIdealGame (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← OracleComp.uniform (BitString n → BitString n)
  OracleComp.simulate (fun query => pure (randomFunctionOracle n table query)) (adversary n [])

/-- A polynomial-time evaluable keyed family indistinguishable from a random function by every
uniform oracle PPT adversary. This interface has `n`-bit keys, inputs and outputs. -/
structure PseudorandomFunction (family : Word → Word → Word) : Prop where
  /-- The shared pair encoding supplies the key and query to one efficient evaluator. -/
  polyTime : IsPolyTime (pairEncoding wordEncoding wordEncoding) (fun pair => family pair.1 pair.2)
  /-- Valid queries receive answers of the declared length. -/
  length_eq : ∀ key query, query.length = key.length → (family key query).length = key.length
  /-- The real and ideal oracle experiments use the common game security calculus. -/
  secure : Game.Secure (fun adversary n => ProbComp.eval (prfRealGame family adversary n))
    (fun adversary n => ProbComp.eval (prfIdealGame adversary n)) (IsOraclePPT boolEncoding)

end Cslib.Crypto
