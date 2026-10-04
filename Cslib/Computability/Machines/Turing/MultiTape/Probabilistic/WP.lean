/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Foundations.Data.PFunctor.Free.WP

/-! # Structural specifications for machine effects

The operation-specific statements expose the response types before `vcgen` matches the WP
instance. This avoids asking unification to infer a sum constructor from its dependent response
type. They use the same `FreeM.forallWP` reading as other native programs.
-/

public section

namespace Turing.MultiTapePTM

open PFunctor Std.WP

variable {Oracle : Type}

/-- A structural proof must hold for either private coin. -/
@[spec]
theorem forallWP_coin_spec (post : Bool → Prop) (epost : EStack⟨⟩) :
    letI : WPMonad (effects Oracle).FreeM Prop EStack⟨⟩ := FreeM.forallWP
    ⦃∀ bit, post bit⦄ coin (Oracle := Oracle) ⦃post; epost⦄ := by
  let : WPMonad (effects Oracle).FreeM Prop EStack⟨⟩ := FreeM.forallWP
  exact ⟨fun h => h⟩

/-- A structural proof must allow every reply word, including malformed or oversized replies. -/
@[spec]
theorem forallWP_query_spec (oracle : Oracle) (request : List Bool)
    (post : List Bool → Prop) (epost : EStack⟨⟩) :
    letI : WPMonad (effects Oracle).FreeM Prop EStack⟨⟩ := FreeM.forallWP
    ⦃∀ answer, post answer⦄ query oracle request ⦃post; epost⦄ := by
  let : WPMonad (effects Oracle).FreeM Prop EStack⟨⟩ := FreeM.forallWP
  exact ⟨fun h => h⟩

end Turing.MultiTapePTM
