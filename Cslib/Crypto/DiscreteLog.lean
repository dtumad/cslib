/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init

/-! # The discrete-logarithm experiment in additive notation -/

@[expose] public section

namespace Cslib.Crypto.DiscreteLog

/-- Sample a public key and check the adversary's proposed logarithm. An explicit failure loses.
For a cyclic group of order `q`, the scalars can be `ZMod q` acting by scalar multiplication. -/
def experiment {F G : Type} [SMul F G] [DecidableEq G]
    {m : Type → Type*} [Monad m] (sample : m F) (g : G)
    (adversary : G → m (Option F)) : m Bool := do
  let secret ← sample
  let result ← adversary (secret • g)
  pure (result.any fun answer => decide (answer • g = secret • g))

end Cslib.Crypto.DiscreteLog
