/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Cslib.Foundations.Data.PFunctor.Free.Resumption

/-!
# Finite truncation of resumptions

`Resumption.truncate k computation` unfolds through at most `k` visible-query layers and
returns a bounded-depth free program with an optional result. Returning is free; a
query at zero fuel truncates to `none`; and every answered query consumes one
unit of fuel.

Adapted from `PolyFun.PFunctor.Resumption.Truncate`.
-/

@[expose] public section

universe uA uB uβ

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ}

/-- Truncate a possibly infinite resumption to at most `k` visible queries.
Returning consumes no fuel; reaching a query at zero fuel returns `none`. -/
def truncate : ℕ → Resumption p β → FreeM p (Option β)
  | 0, computation =>
      match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr _ => FreeM.pure none
  | k + 1, computation =>
      match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr ⟨position, next⟩ =>
          FreeM.liftBind position fun direction => truncate k (next direction)

theorem truncate_zero (computation : Resumption p β) :
    truncate 0 computation = match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr _ => FreeM.pure none := rfl

theorem truncate_succ (k : ℕ) (computation : Resumption p β) :
    truncate (k + 1) computation = match dest computation with
      | Sum.inl result => FreeM.pure (some result)
      | Sum.inr ⟨position, next⟩ =>
          FreeM.liftBind position fun direction => truncate k (next direction) := rfl

@[simp] theorem truncate_pure (k : ℕ) (result : β) :
    truncate k (pure (p := p) result) = FreeM.pure (some result) := by
  cases k <;> rfl

@[simp] theorem truncate_query_zero (position : p.A) (next : p.B position → Resumption p β) :
    truncate 0 (query position next) = FreeM.pure none := rfl

@[simp] theorem truncate_query_succ (k : ℕ) (position : p.A)
    (next : p.B position → Resumption p β) :
    truncate (k + 1) (query position next) =
      FreeM.liftBind position fun direction => truncate k (next direction) := rfl

end PFunctor.Resumption
