/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.MonadAttach
public import Mathlib.Control.Monad.Basic

/-!
# A cached random oracle

`query` is an ordinary `StateT` handler. Only previously unseen inputs draw a fresh sample.
The state is a list of input/output pairs; no oracle or probability typeclass is required.
It can be inlined with `PFunctor.FreeM.liftM` before interpreting the remaining effects.
-/

@[expose] public section

namespace Cslib.Crypto.RandomOracle

variable {X Y : Type} [DecidableEq X] {m : Type → Type*} [Monad m]

/-- Look up an input, sampling and recording its answer on the first query. -/
def query (sample : m Y) (input : X) : StateT (List (X × Y)) m Y := fun cache =>
  match cache.lookup input with
  | some answer => pure (answer, cache)
  | none => do
    let answer ← sample
    pure (answer, (input, answer) :: cache)

@[simp]
theorem query_of_lookup_eq_some (sample : m Y) (input : X) (cache : List (X × Y))
    (answer : Y) (h : cache.lookup input = some answer) :
    query sample input cache = pure (answer, cache) := by simp [query, h]

theorem query_of_lookup_eq_none (sample : m Y) (input : X) (cache : List (X × Y))
    (h : cache.lookup input = none) :
    query sample input cache = (do
      let answer ← sample
      pure (answer, (input, answer) :: cache)) := by simp [query, h]

/-- Querying the same input twice reuses its answer and consumes no additional randomness. -/
theorem query_query [LawfulMonad m] (sample : m Y) (input : X) (cache : List (X × Y)) :
    (do
      let (first, cache') ← query sample input cache
      let (second, cache'') ← query sample input cache'
      pure ((first, second), cache'')) =
    (do
      let (answer, cache') ← query sample input cache
      pure ((answer, answer), cache')) := by
  cases h : cache.lookup input with
  | some answer => simp [query, h]
  | none => simp [query, h]

variable {P : PFunctor.{0, 0}}

/-- Every reachable answer is recorded in the resulting cache. -/
theorem lookup_of_canReturn (sample : P.FreeM Y) (input : X) (cache : List (X × Y))
    {out : Y × List (X × Y)} (h : MonadAttach.CanReturn (query sample input cache) out) :
    out.2.lookup input = some out.1 := by
  cases hx : cache.lookup input with
  | some answer =>
    simp only [query, hx, PFunctor.FreeM.canReturn_pure] at h
    subst out
    exact hx
  | none =>
    rw [query, hx] at h
    obtain ⟨answer, _, rfl⟩ := (PFunctor.FreeM.canReturn_bind _ _ _).mp h
    simp

/-- A random-oracle query never changes an existing answer. -/
theorem lookup_preserved (sample : P.FreeM Y) (input : X) (cache : List (X × Y))
    {out : Y × List (X × Y)} (h : MonadAttach.CanReturn (query sample input cache) out)
    {oldInput : X} {oldAnswer : Y} (hold : cache.lookup oldInput = some oldAnswer) :
    out.2.lookup oldInput = some oldAnswer := by
  cases hx : cache.lookup input with
  | some answer =>
    simp only [query, hx, PFunctor.FreeM.canReturn_pure] at h
    subst out
    exact hold
  | none =>
    have hne : oldInput ≠ input := by rintro rfl; simp [hx] at hold
    rw [query, hx] at h
    obtain ⟨answer, _, rfl⟩ := (PFunctor.FreeM.canReturn_bind _ _ _).mp h
    simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hne, hold]

/-- Existing answers survive any adaptive sequence of random-oracle requests. -/
theorem lookup_preserved_liftM {α : Type} (sample : P.FreeM Y)
    (program : (PFunctor.mk X (fun _ => Y)).FreeM α) (cache : List (X × Y))
    {out : α × List (X × Y)}
    (h : MonadAttach.CanReturn ((program.liftM (query sample)) cache) out)
    {input : X} {answer : Y} (hold : cache.lookup input = some answer) :
    out.2.lookup input = some answer := by
  induction program generalizing cache out with
  | pure a =>
    have ho : out = (a, cache) := h
    subst out
    exact hold
  | lift_bind op cont ih =>
    change MonadAttach.CanReturn ((query sample op cache).bind
      (fun response => ((cont response.1).liftM (query sample)) response.2)) out at h
    obtain ⟨response, hresponse, hrest⟩ := (PFunctor.FreeM.canReturn_bind _ _ _).mp h
    exact ih response.1 response.2 hrest (lookup_preserved sample op cache hresponse hold)

end Cslib.Crypto.RandomOracle
