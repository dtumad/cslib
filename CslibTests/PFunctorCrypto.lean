/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.Probabilistic.Sampling
import Cslib.Computability.Probabilistic.CoinTape
import Cslib.Crypto.Primitives.ElGamal.Oracle
import Cslib.Foundations.Control.Monad.Free.PFunctor

/-! Compatibility checks against Samuel Schlesinger's probabilistic programs and machines. -/

namespace CslibTests.PFunctorCrypto

open Cslib Cslib.Probability

abbrev coins : PFunctor := ⟨Unit, fun _ => Bool⟩

def bits : ℕ → coins.FreeM Word
  | 0 => pure []
  | n + 1 => do
    let bit ← PFunctor.FreeM.lift ()
    pure (bit :: (← bits n))

theorem compile_bits (n : ℕ) :
    (bits n).liftM (fun _ => (OracleComp.uniform Bool : ProbComp Bool)) =
      OracleComp.sampleBits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hcoin := PFunctor.FreeM.liftM_lift (P := coins)
      (fun _ => (OracleComp.uniform Bool : ProbComp Bool)) ()
    simp [bits, OracleComp.sampleBits, PFunctor.FreeM.liftM_bind, hcoin, ih]

/-- Native polynomial bit sampling inherits an actual finite-machine PPT certificate. -/
example : IsPPT wordEncoding (fun n _ =>
    (bits n).liftM (fun _ => (OracleComp.uniform Bool : ProbComp Bool))) := by
  simpa only [compile_bits] using isPPT_sampleBits

/-- The syntax conversion preserves the whole stateful interpretation, including private state. -/
example {Query : Type} {Response : Query → Type} {α State : Type}
    (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (s : State) :
    ((program.toPFunctor).liftM (fun op : (PFunctor.ofFamily (ProbEffect Query Response)).A =>
      OracleComp.stateEffect oracle op.2)) s =
      OracleComp.runState oracle program s := by
  rw [FreeM.liftM_toPFunctor (OracleComp.stateEffect oracle) program]
  rfl

/-- A saved-coin realization transports to polynomial syntax with the same machine and clock. -/
example {α β : Type} {input : α → Word} {output : β ↪ Word} {program : α → ProbComp β}
    (h : IsPPTOn input output program) :
    ∃ (k states : ℕ) (machine : Turing.OracleTM k (Fin states)) (c d : ℕ),
      ∀ a, (((program a).toPFunctor).liftM
        (fun op : (PFunctor.ofFamily (ProbEffect PEmpty (fun _ => PEmpty))).A =>
          OracleComp.evalEffect (fun q : PEmpty => q.elim) op.2)).map output =
          (uniformBits (c * ((input a).length + 1) ^ d)).map
            (fun tape => Turing.MultiTapePTM.runCoins (m := Id) machine (fun _ _ => [])
              tape (input a)) := by
  obtain ⟨k, states, machine, c, d, hmachine⟩ := h.exists_coin_machine
  refine ⟨k, states, machine, c, d, fun a => ?_⟩
  rw [FreeM.liftM_toPFunctor (OracleComp.evalEffect (fun q : PEmpty => q.elim)) (program a)]
  exact hmachine a

end CslibTests.PFunctorCrypto
