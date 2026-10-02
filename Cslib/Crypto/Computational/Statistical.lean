/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.Basic
public import Cslib.Crypto.Game.Statistical

/-!
# Statistical indistinguishability implies computational indistinguishability

The common statistical-distance API applies directly to word ensembles. Sampling and randomized
testing are interpreted as PMF bind, so the implication is an instance of the semantic game theorem.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- A negligible statistical distance defeats every uniform PPT distinguisher. -/
theorem StatisticallyIndistinguishable.computationallyIndistinguishable {X Y : ℕ → PMF Word}
    (h : StatisticallyIndistinguishable X Y) : ComputationallyIndistinguishable X Y :=
  computationallyIndistinguishable_iff_tests.mpr (h.secure (fun test => test) IsPPTTest)

end Cslib.Crypto
