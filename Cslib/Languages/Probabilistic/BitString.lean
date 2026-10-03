/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Basic
public import Cslib.Probability.BitString

/-!
# Sampling binary strings one fair bit at a time

`sampleBits` gives an operational description of uniform binary sampling. Its semantics agrees
exactly with `uniformBits`, including in the presence of an arbitrary stateful oracle.
-/

@[expose] public section

namespace Cslib.OracleComp

open Probability

variable {Query : Type} {Response : Query → Type} {State : Type}

/-- Sample `n` independent fair bits. -/
noncomputable def sampleBits : ℕ → OracleComp Query Response (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bit ← uniform Bool
    return bit :: (← sampleBits n)

@[simp] theorem eval_sampleBits (oracle : (q : Query) → PMF (Response q)) (n : ℕ) :
    eval oracle (sampleBits n) = uniformBits n := by
  induction n with
  | zero => simp [sampleBits]
  | succ n ih => simp [sampleBits, uniformBits_succ, ih, uniform, PMF.map, Function.comp_def]

@[simp] theorem runState_sampleBits (oracle : (q : Query) → StateT State PMF (Response q))
    (n : ℕ) (s : State) :
    runState oracle (sampleBits n) s = (uniformBits n).map (fun word => (word, s)) := by
  induction n with
  | zero => simp [sampleBits, PMF.pure_map]
  | succ n ih =>
    simp [sampleBits, uniformBits_succ, ih, uniform, PMF.map, Function.comp_def]

end Cslib.OracleComp

namespace Cslib.ProbComp

/-- Closed fair-bit sampling has the uniform word distribution. -/
@[simp] theorem eval_sampleBits (n : ℕ) :
    eval (OracleComp.sampleBits n) = Probability.uniformBits n :=
  OracleComp.eval_sampleBits _ n

end Cslib.ProbComp
