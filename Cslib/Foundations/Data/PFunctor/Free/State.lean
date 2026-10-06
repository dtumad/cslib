/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fold

/-!
# Threading state through polynomial programs

`P.withState S` pairs each operation of `P` with a state, and answers it with a response together
with a new state. Run from a state `s`, a program `x : P.FreeM α` becomes `x.withState s`, which
passes the state from each operation to the next and returns the final state with the result.
Answering the operations of `P.withState S` therefore models operations whose answers may depend
on, and update, a shared state, such as stateful oracles.
-/

@[expose] public section

universe uA uB uS u v

namespace PFunctor

/-- The operations of `P` paired with a state, answered with a response and a new state. -/
abbrev withState (P : PFunctor.{uA, uB}) (S : Type uS) : PFunctor.{max uA uS, max uB uS} :=
  ⟨P.A × S, fun a => P.B a.1 × S⟩

namespace FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type u} {β : Type v}

/-- Run `x` from the state `s`, passing the state through its operations and returning the final
state with the result. -/
def withState (x : P.FreeM α) (s : S) : (P.withState S).FreeM (α × S) :=
  x.foldFreeM (β := S → (P.withState S).FreeM (α × S)) (fun a s => pure (a, s))
    (fun a k s => (lift (P := P.withState S) (a, s)).bind fun b => k b.1 b.2) s

@[simp]
theorem withState_pure (a : α) (s : S) : (pure a : P.FreeM α).withState s = pure (a, s) := rfl

@[simp]
theorem withState_lift_bind (a : P.A) (k : P.B a → P.FreeM α) (s : S) :
    ((lift a).bind (α := no_index (P.B a)) k).withState s =
      (lift (P := P.withState S) (a, s)).bind fun b => (k b.1).withState b.2 := rfl

@[simp]
theorem withState_lift_bind' {α : Type uB} {S : Type uB} (a : P.A) (k : P.B a → P.FreeM α)
    (s : S) :
    (Bind.bind (α := no_index (P.B a)) (lift a) k).withState s =
      lift (P := P.withState S) (a, s) >>= fun b => (k b.1).withState b.2 := rfl

@[simp]
theorem withState_lift (a : P.A) (s : S) :
    withState (α := no_index (P.B a)) (lift a) s = lift (P := P.withState S) (a, s) := by
  simpa using withState_lift_bind a pure s

@[simp]
theorem withState_bind (x : P.FreeM α) (f : α → P.FreeM β) (s : S) :
    (x.bind f).withState s = (x.withState s).bind fun p => (f p.1).withState p.2 := by
  induction x generalizing s <;> simp [*, FreeM.bind_assoc]

@[simp]
theorem withState_bind' {α β : Type u} (x : P.FreeM α) (f : α → P.FreeM β) (s : S) :
    (x >>= f).withState s = x.withState s >>= fun p => (f p.1).withState p.2 :=
  withState_bind x f s

@[simp]
theorem withState_map (f : α → β) (x : P.FreeM α) (s : S) :
    (x.map f).withState s = (x.withState s).map (Prod.map f id) := by
  induction x generalizing s <;> simp [*]

@[simp]
theorem withState_map' {α β : Type u} (f : α → β) (x : P.FreeM α) (s : S) :
    (f <$> x).withState s = Prod.map f id <$> x.withState s :=
  withState_map f x s

end FreeM

end PFunctor
