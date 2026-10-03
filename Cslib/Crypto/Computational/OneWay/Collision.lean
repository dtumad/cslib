/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.OneWay
public import Cslib.Computability.Probabilistic.Sampling
public import Cslib.Probability.Collision

/-!
# Output collisions of one-way functions

Independently guessing an `n`-bit preimage inverts `f` exactly when two independent images collide.
The guesser is a uniform PPT program. Hence the output collision probability of any one-way
function is negligible. No injectivity, regularity, or length-preservation assumption is used.

This necessary entropy condition alone does not give the entropy surplus needed by a PRG.
The general OWF-to-PRG development follows Thomas Holenstein's
[*Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness*]
(https://crypto.ethz.ch/publications/files/Holens06.pdf), TCC 2006, Sections 4–5. The elementary
guessing argument here is separate from that write-up's stronger pseudo-entropy-pair construction.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Probability.PMF

/-- A fresh independent preimage guess succeeds exactly with the output collision probability. -/
theorem output_collision_eq_inversion (f : Word → Word) (n : ℕ) :
    collisionProbability ((uniformBits n).map f) =
      winProbability (inversionGame f (fun n _ => OracleComp.sampleBits n) n) := by
  rw [collisionProbability_eq_probability]
  simp only [winProbability, Game.winProbability, inversionGame, ProbComp.eval,
    OracleComp.eval_bind, OracleComp.eval_sample, OracleComp.eval_sampleBits, OracleComp.eval_pure,
    PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply congrArg (fun game : PMF Bool => (game true).toReal)
  apply congrArg (uniformBits n).bind
  funext x
  apply congrArg (uniformBits n).bind
  funext y
  congr 1
  simp [beq_eq_decide, eq_comm]

/-- One-wayness forces negligible output collision probability, even for variable-length images. -/
theorem OneWay.output_collision_negligible {f : Word → Word} (hf : OneWay f) :
    Negligible (fun n => collisionProbability ((uniformBits n).map f)) := by
  have h := hf.inversion_negligible (fun n _ => OracleComp.sampleBits n) isPPT_sampleBits
  exact h.congr (fun n => (output_collision_eq_inversion f n).symm)

end Cslib.Crypto
