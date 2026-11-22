/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Typed paths to residual free programs

A spine records the replies selecting a residual subtree of a free program. The source and
residual are indices, so composing two spines preserves their endpoints by construction.
-/

public section

universe uA uB v

namespace PFunctor.FreeM.Cursor

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- The typed spine of a cursor, indexed by its source program and selected
residual. Keeping the residual as an index makes composition preserve it
definitionally. -/
inductive Spine : (program residual : FreeM P α) → Type (max uA uB v)
  | root (program : FreeM P α) : Spine program program
  | down {a : P.A} {next : P.B a → FreeM P α} {residual : FreeM P α}
      (answer : P.B a) (tail : Spine (next answer) residual) :
      Spine (FreeM.liftBind a next) residual

namespace Spine

variable {program middle residual suffix : FreeM P α}

/-- Compose typed cursor spines. -/
@[expose] def comp : {program middle residual : FreeM P α} →
    Spine program middle → Spine middle residual → Spine program residual
  | _, _, _, .root _, suffix => suffix
  | _, _, _, .down answer tail, suffix => .down answer (tail.comp suffix)

@[simp]
theorem root_comp (suffix : Spine program residual) :
    (Spine.root program).comp suffix = suffix :=
  rfl

@[simp]
theorem comp_root (spine : Spine program residual) :
    spine.comp (Spine.root residual) = spine := by
  induction spine with
  | root => rfl
  | down answer tail ih => rw [comp, ih]

@[simp]
theorem comp_assoc (first : Spine program middle)
    (second : Spine middle residual) (third : Spine residual suffix) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  induction first with
  | root => rfl
  | down answer tail ih => simp only [comp, ih]

end Spine

end PFunctor.FreeM.Cursor
