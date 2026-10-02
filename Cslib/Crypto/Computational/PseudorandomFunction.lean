/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Probability.BitString

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

/-- Fixed-width binary words, used to describe the finite ideal function space. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- An adaptive oracle distinguisher, with an optional auxiliary input. -/
abbrev OracleDistinguisher := ℕ → Word → OracleComp Word (fun _ => Word) Bool

/-- Encode a pair by prefixing the unary length of the first word. -/
def encodePair (pair : Word × Word) : Word :=
  parameterInput pair.1.length (pair.1 ++ pair.2)

/-- The evaluator's input encoding loses neither the key nor the query. -/
theorem encodePair_injective : Function.Injective encodePair := by
  intro ⟨key, query⟩ ⟨key', query'⟩ h
  obtain ⟨hlen, hwords⟩ := parameterInput_inj.mp h
  have hk : key = key' := by
    have ht := congrArg (List.take key.length) hwords
    simpa [hlen] using ht
  subst key'
  exact Prod.ext rfl (by simpa using hwords)

/-- The keyed oracle rejects queries outside the `n`-bit domain. -/
def prfOracle (family : Word → Word → Word) (n : ℕ) (key query : Word) : Word :=
  if query.length = n then family key query else []

/-- A single fixed random table, extended to malformed queries by the same rejection convention
as the real oracle. Reading with `getD` is used only under the exact-length guard. -/
def randomFunctionOracle (n : ℕ) (table : Bits n → Bits n) (query : Word) : Word :=
  if query.length = n then List.ofFn (table (fun i => query[i.val]?.getD false)) else []

/-- Sample one key and use it for all calls made by the adversary. -/
noncomputable def prfRealGame (family : Word → Word → Word) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let key ← OracleComp.sample (uniformBits n)
  OracleComp.simulate (fun query => pure (prfOracle family n key query)) (adversary n [])

/-- Sample one uniformly random function, retaining it across adaptive and repeated calls. -/
noncomputable def prfIdealGame (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← OracleComp.uniform (Bits n → Bits n)
  OracleComp.simulate (fun query => pure (randomFunctionOracle n table query)) (adversary n [])

/-- A polynomial-time evaluable keyed family indistinguishable from a random function by every
uniform oracle PPT adversary. This interface has `n`-bit keys, inputs and outputs. -/
def PseudorandomFunction (family : Word → Word → Word) : Prop :=
  IsPolyTime encodePair (fun pair => family pair.1 pair.2) ∧
  (∀ key query, query.length = key.length → (family key query).length = key.length) ∧
  ∀ adversary : OracleDistinguisher, IsOraclePPT boolEncoding adversary →
    Negligible (fun n => advantage (prfRealGame family adversary n) (prfIdealGame adversary n))

end Cslib.Crypto
