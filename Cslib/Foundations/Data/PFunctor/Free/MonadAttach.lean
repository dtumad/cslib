/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free
public import Init.Control.MonadAttach

/-!
# Attaching reachability proofs to polynomial free programs

The `MonadAttach` instance records structural reachability: a value can be returned if some
choice of responses leads to that leaf. This is independent of any probabilistic interpretation;
an interpreter may assign probability zero to a structurally possible response.

Adapted from `PolyFun.PFunctor.Free.Support`.
-/

@[expose] public section

namespace PFunctor.FreeM

universe uA uB v w

variable {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}

/-- The possible return values, allowing every response to each operation. -/
def support : P.FreeM α → Set α
  | .pure a => {a}
  | .liftBind _ cont => {a | ∃ b, a ∈ support (cont b)}

/-- Attach the path's reachability proof to each return value. -/
def attach : (x : P.FreeM α) → P.FreeM {a // a ∈ support x}
  | .pure a => pure ⟨a, rfl⟩
  | .liftBind op cont => .liftBind op fun b =>
      (attach (cont b)).map fun a => ⟨a.1, b, a.2⟩

instance : MonadAttach P.FreeM where
  CanReturn x a := a ∈ support x
  attach := attach

theorem canReturn_iff_mem_support (x : P.FreeM α) (a : α) :
    MonadAttach.CanReturn x a ↔ a ∈ support x := Iff.rfl

@[simp]
theorem canReturn_pure (a b : α) :
    MonadAttach.CanReturn (pure a : P.FreeM α) b ↔ b = a := Iff.rfl

theorem canReturn_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) (a : α) :
    MonadAttach.CanReturn ((lift op).bind cont) a ↔
      ∃ b, MonadAttach.CanReturn (cont b) a := Iff.rfl

@[simp]
theorem canReturn_lift (op : P.A) (b : P.B op) :
    MonadAttach.CanReturn (lift (P := P) op) b := ⟨b, rfl⟩

@[simp]
theorem canReturn_bind (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    MonadAttach.CanReturn (x.bind f) b ↔
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    simp only [liftBind_bind, canReturn_lift_bind, ih]
    exact ⟨fun ⟨c, a, ha, hb⟩ => ⟨a, ⟨c, ha⟩, hb⟩,
      fun ⟨a, ⟨c, ha⟩, hb⟩ => ⟨c, a, ha, hb⟩⟩

@[simp]
theorem canReturn_map (f : α → β) (x : P.FreeM α) (b : β) :
    MonadAttach.CanReturn (map f x) b ↔ ∃ a, MonadAttach.CanReturn x a ∧ f a = b := by
  rw [← bind_pure_comp, canReturn_bind]
  simp only [Function.comp_apply, canReturn_pure, eq_comm]

/-- Traversing a list preserves its length on every reachable execution. -/
theorem length_of_canReturn_mapM {X Y : Type uB} (f : X → P.FreeM Y) (input : List X)
    {output : List Y} (h : MonadAttach.CanReturn (input.mapM f) output) :
    output.length = input.length := by
  induction input generalizing output with
  | nil => simpa using congrArg List.length ((canReturn_pure [] output).mp h)
  | cons x input ih =>
    simp only [List.mapM_cons, ← FreeM.bind_eq_bind, canReturn_bind, canReturn_pure] at h
    obtain ⟨value, _, rest, hrest, rfl⟩ := h
    simpa using ih hrest

theorem canReturn_liftObj (x : P.Obj α) (a : α) :
    MonadAttach.CanReturn (liftObj x) a ↔ a ∈ Set.range x.2 := by
  simp [liftObj, Set.mem_range]

theorem map_attach (x : P.FreeM α) : map Subtype.val (attach x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change liftBind op (fun b => map Subtype.val
      (map (fun a => ⟨a.1, b, a.2⟩) (attach (cont b)))) = liftBind op cont
    congr 1
    funext b
    rw [← comp_map]
    exact ih b

instance : LawfulMonadAttach P.FreeM where
  map_attach := map_attach _
  canReturn_map_imp {α} {Q} {x} {a} h := by
    obtain ⟨b, _, rfl⟩ := (canReturn_map Subtype.val x a).mp h
    exact b.2

/-- Binds agree when their continuations agree at every structurally reachable return value. -/
theorem bind_congr_of_canReturn (x : P.FreeM α) {f g : α → P.FreeM β}
    (h : ∀ a, MonadAttach.CanReturn x a → f a = g a) : x.bind f = x.bind g := by
  induction x with
  | pure a => exact h a rfl
  | lift_bind op cont ih =>
    simp only [liftBind_bind]
    congr 1
    funext answer
    exact ih answer fun a ha => h a ⟨answer, ha⟩

/-- Inlining effects can only remove structurally reachable return values. -/
theorem canReturn_of_liftM {Q : PFunctor.{w, uB}} {α : Type uB}
    (interp : (op : P.A) → Q.FreeM (P.B op)) (x : P.FreeM α) {a : α}
    (h : MonadAttach.CanReturn (x.liftM interp) a) : MonadAttach.CanReturn x a := by
  induction x with
  | pure value => exact h
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind] at h
    obtain ⟨answer, _, h⟩ := (canReturn_bind _ _ _).mp h
    exact ⟨answer, ih answer h⟩

/-- A free program has a possible result when each operation has a response. -/
theorem exists_canReturn [∀ op, Nonempty (P.B op)] (x : P.FreeM α) :
    ∃ a, MonadAttach.CanReturn x a := by
  induction x with
  | pure a => exact ⟨a, rfl⟩
  | lift_bind op cont ih =>
    obtain ⟨b⟩ := (inferInstance : Nonempty (P.B op))
    obtain ⟨a, ha⟩ := ih b
    exact ⟨a, b, ha⟩

end PFunctor.FreeM
