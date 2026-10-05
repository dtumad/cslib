/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import Init.Control.Lawful.MonadAttach.Lemmas
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor

/-!
# Attaching reachability proofs to polynomial free programs

`possibleOutputs responses` interprets operations by the given sets of responses. It is the fold
into `SetM`, allowing independent response and result universes. `possibleOutputs_eq_liftM` gives
its monadic form when these universes agree.

The `MonadAttach` instance specializes this to all responses. Its attachment preserves the original
syntax, including every branch. For a chosen handler, `mem_possibleOutputs_of_canReturn_liftM`
relates the interpreted program's return values to the responses its operations can return.

Adapted from `PolyFun.PFunctor.Free.Support`.
-/

@[expose] public section

namespace PFunctor.FreeM

universe uA uB v w

variable {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}

/-- The return values reachable using the given sets of operation responses. -/
def possibleOutputs (responses : (op : P.A) → Set (P.B op)) : P.FreeM α → Set α :=
  foldFreeM (fun a => {a}) (fun op cont => {a | ∃ b ∈ responses op, a ∈ cont b})

/-- The possible-output interpretation is the universal monadic extension of its response sets. -/
theorem interprets_possibleOutputs {α : Type uB} (responses : (op : P.A) → Set (P.B op)) :
    Interprets (m := SetM) responses (possibleOutputs responses : P.FreeM α → SetM α) where
  apply_pure _ := rfl
  apply_lift_bind op cont := by
    apply Set.ext
    intro a
    change (∃ b ∈ responses op, a ∈ possibleOutputs responses (cont b)) ↔
      a ∈ ⋃ b ∈ responses op, possibleOutputs responses (cont b)
    simp only [Set.mem_iUnion, exists_prop]

/-- The monadic form of `possibleOutputs`. The fold definition also permits independent response
and result universes, which the `Monad` interface does not. -/
theorem possibleOutputs_eq_liftM {α : Type uB} (responses : (op : P.A) → Set (P.B op))
    (x : P.FreeM α) : possibleOutputs responses x = (x.liftM (m := SetM) responses).run :=
  congrFun (interprets_possibleOutputs responses).eq x

@[simp]
theorem possibleOutputs_pure (responses : (op : P.A) → Set (P.B op)) (a : α) :
    possibleOutputs responses (pure a : P.FreeM α) = {a} := rfl

theorem possibleOutputs_lift_bind (responses : (op : P.A) → Set (P.B op))
    (op : P.A) (cont : P.B op → P.FreeM α) :
    possibleOutputs responses ((lift op).bind cont) =
      ⋃ b ∈ responses op, possibleOutputs responses (cont b) := by
  ext a
  change (∃ b ∈ responses op, a ∈ possibleOutputs responses (cont b)) ↔ _
  simp only [Set.mem_iUnion, exists_prop]

@[simp]
theorem possibleOutputs_lift (responses : (op : P.A) → Set (P.B op)) (op : P.A) :
    possibleOutputs (α := no_index (P.B op)) responses (lift op) = responses op := by
  ext b
  change (∃ c ∈ responses op, b = c) ↔ b ∈ responses op
  simp

@[simp]
theorem mem_possibleOutputs_bind (responses : (op : P.A) → Set (P.B op))
    (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    b ∈ possibleOutputs responses (x.bind f) ↔
      ∃ a ∈ possibleOutputs responses x, b ∈ possibleOutputs responses (f a) := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    simp only [liftBind_bind, possibleOutputs_lift_bind, Set.mem_iUnion, exists_prop, ih]
    exact ⟨fun ⟨c, hc, a, ha, hb⟩ => ⟨a, ⟨c, hc, ha⟩, hb⟩,
      fun ⟨a, ⟨c, hc, ha⟩, hb⟩ => ⟨c, hc, a, ha, hb⟩⟩

@[simp]
theorem possibleOutputs_map (responses : (op : P.A) → Set (P.B op))
    (f : α → β) (x : P.FreeM α) :
    possibleOutputs responses (map f x) = f '' possibleOutputs responses x := by
  ext b
  rw [← bind_pure_comp, mem_possibleOutputs_bind]
  simp only [possibleOutputs_pure, Function.comp_apply, Set.mem_singleton_iff,
    Set.mem_image, eq_comm]

/-- Allowing more responses can only add possible results. -/
theorem possibleOutputs_mono {responses responses' : (op : P.A) → Set (P.B op)}
    (h : ∀ op, responses op ⊆ responses' op) (x : P.FreeM α) :
    possibleOutputs responses x ⊆ possibleOutputs responses' x := by
  induction x with
  | pure a => exact Set.Subset.refl _
  | lift_bind op cont ih =>
    rintro a ⟨b, hb, ha⟩
    exact ⟨b, h op hb, ih b ha⟩

/-- Countable sets of responses give a countable set of possible results. -/
theorem possibleOutputs_countable (responses : (op : P.A) → Set (P.B op))
    (h : ∀ op, (responses op).Countable) (x : P.FreeM α) :
    (possibleOutputs responses x).Countable := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [possibleOutputs_lift_bind]
    exact (h op).biUnion fun b _ => ih b

/-- Finite sets of responses give a finite set of possible results. -/
theorem possibleOutputs_finite (responses : (op : P.A) → Set (P.B op))
    (h : ∀ op, (responses op).Finite) (x : P.FreeM α) :
    (possibleOutputs responses x).Finite := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [possibleOutputs_lift_bind]
    exact (h op).biUnion fun b _ => ih b

/-- Interpret operations with proofs that their responses are allowed, and attach the induced
possible-output proof to the final result. -/
def attachWith {m : Type uB → Type w} [Monad m] {α : Type uB}
    (responses : (op : P.A) → Set (P.B op))
    (interp : (op : P.A) → m {b // b ∈ responses op}) :
    (x : P.FreeM α) → m {a // a ∈ possibleOutputs responses x}
  | .pure a => pure ⟨a, rfl⟩
  | .liftBind op cont => do
    let b ← interp op
    let a ← attachWith responses interp (cont b.1)
    pure ⟨a.1, b.1, b.2, a.2⟩

/-- Erasing the attached proofs recovers interpretation by the underlying query handler. -/
theorem map_attachWith {m : Type uB → Type w} [Monad m] [LawfulMonad m] {α : Type uB}
    (responses : (op : P.A) → Set (P.B op))
    (interp : (op : P.A) → m {b // b ∈ responses op}) (x : P.FreeM α) :
    Subtype.val <$> attachWith responses interp x =
      x.liftM (fun op => Subtype.val <$> interp op) := by
  induction x with
  | pure a =>
    change Subtype.val <$> (pure ⟨a, rfl⟩ : m {b // b = a}) = pure a
    simp
  | lift_bind op cont ih =>
    change Subtype.val <$> (interp op >>= fun b =>
      attachWith responses interp (cont b.1) >>= fun a => pure ⟨a.1, b.1, b.2, a.2⟩) =
      (Subtype.val <$> interp op) >>= fun b => (cont b).liftM _
    simp [_root_.map_bind, ih]

/-- Attach a proof of structural reachability to each return value. -/
def attach : (x : P.FreeM α) → P.FreeM {a // a ∈ possibleOutputs (fun _ => Set.univ) x}
  | .pure a => pure ⟨a, rfl⟩
  | .liftBind op cont => .liftBind op fun b =>
      (attach (cont b)).map fun a => ⟨a.1, b, Set.mem_univ b, a.2⟩

/-- Structural attachment is `attachWith` for the query handler allowing every response. -/
theorem attachWith_lift_eq_attach {α : Type uB} (x : P.FreeM α) :
    attachWith (fun _ => Set.univ)
      (fun op => map (fun b => ⟨b, Set.mem_univ b⟩) (lift (P := P) op)) x = attach x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    change liftBind op _ = liftBind op _
    congr 1
    funext b
    simp only [map_eq_map] at ih
    simp [ih]

instance : MonadAttach P.FreeM where
  CanReturn x a := a ∈ possibleOutputs (fun _ => Set.univ) x
  attach := attach

theorem canReturn_iff_mem_possibleOutputs (x : P.FreeM α) (a : α) :
    MonadAttach.CanReturn x a ↔ a ∈ possibleOutputs (fun _ => Set.univ) x := Iff.rfl

@[simp]
theorem canReturn_pure (a b : α) :
    MonadAttach.CanReturn (pure a : P.FreeM α) b ↔ b = a := Iff.rfl

theorem canReturn_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) (a : α) :
    MonadAttach.CanReturn ((lift op).bind cont) a ↔
      ∃ b, MonadAttach.CanReturn (cont b) a := by
  change (∃ b, True ∧ MonadAttach.CanReturn (cont b) a) ↔ _
  simp only [true_and]

@[simp]
theorem canReturn_lift (op : P.A) (b : P.B op) :
    MonadAttach.CanReturn (α := no_index (P.B op)) (lift (P := P) op) b :=
  ⟨b, Set.mem_univ b, rfl⟩

@[simp]
theorem canReturn_bind (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    MonadAttach.CanReturn (x.bind f) b ↔
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b := by
  exact mem_possibleOutputs_bind (fun _ => Set.univ) x f b

@[simp]
theorem canReturn_map (f : α → β) (x : P.FreeM α) (b : β) :
    MonadAttach.CanReturn (map f x) b ↔ ∃ a, MonadAttach.CanReturn x a ∧ f a = b := by
  rw [← bind_pure_comp, canReturn_bind]
  simp only [Function.comp_apply, canReturn_pure, eq_comm]

/-- A necessary postcondition for sequencing need only hold at reachable intermediate values. -/
theorem forall_canReturn_bind (x : P.FreeM α) (f : α → P.FreeM β) (post : β → Prop) :
    (∀ b, MonadAttach.CanReturn (x.bind f) b → post b) ↔
      ∀ a, MonadAttach.CanReturn x a → ∀ b, MonadAttach.CanReturn (f a) b → post b := by
  simp only [canReturn_bind, forall_exists_index, and_imp]
  exact ⟨fun h a ha b hb => h b a ha hb, fun h b a ha hb => h a ha b hb⟩

/-- A possible output of a composite computation has a possible intermediate value. -/
theorem exists_canReturn_bind (x : P.FreeM α) (f : α → P.FreeM β) (post : β → Prop) :
    (∃ b, MonadAttach.CanReturn (x.bind f) b ∧ post b) ↔
      ∃ a, MonadAttach.CanReturn x a ∧ ∃ b, MonadAttach.CanReturn (f a) b ∧ post b := by
  simp only [canReturn_bind]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hp⟩ => ⟨a, ha, b, hb, hp⟩,
    fun ⟨a, ha, b, hb, hp⟩ => ⟨b, ⟨a, ha, hb⟩, hp⟩⟩

/-- Traversing a list preserves its length on every reachable execution. -/
theorem length_of_canReturn_mapM {X : Type v} {Y : Type uB} (f : X → P.FreeM Y) (input : List X)
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
      (map (fun a => ⟨a.1, b, Set.mem_univ b, a.2⟩) (attach (cont b)))) = liftBind op cont
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
    exact ih answer fun a ha => h a ⟨answer, Set.mem_univ answer, ha⟩

/-- If each operation returns an allowed response, every result of the interpreted program
belongs to the corresponding set of possible outputs. -/
theorem mem_possibleOutputs_of_canReturn_liftM {m : Type uB → Type w}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] {α : Type uB}
    (responses : (op : P.A) → Set (P.B op)) (interp : (op : P.A) → m (P.B op))
    (hinterp : ∀ op b, MonadAttach.CanReturn (interp op) b → b ∈ responses op)
    (x : P.FreeM α) {a : α} (h : MonadAttach.CanReturn (x.liftM interp) a) :
    a ∈ possibleOutputs responses x := by
  induction x with
  | pure value => exact (LawfulMonadAttach.eq_of_canReturn_pure h).symm
  | lift_bind op cont ih =>
    rw [bind_eq_bind, liftM_lift_bind] at h
    obtain ⟨answer, hanswer, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    exact ⟨answer, hinterp op answer hanswer, ih answer h⟩

/-- Interpreting operations can only remove structurally possible return values. -/
theorem canReturn_of_liftM {m : Type uB → Type w}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] {α : Type uB}
    (interp : (op : P.A) → m (P.B op)) (x : P.FreeM α) {a : α}
    (h : MonadAttach.CanReturn (x.liftM interp) a) : MonadAttach.CanReturn x a :=
  mem_possibleOutputs_of_canReturn_liftM (fun _ => Set.univ) interp
    (fun _ _ _ => Set.mem_univ _) x h

/-- A free program has a possible result when each operation has a response. -/
theorem exists_canReturn [∀ op, Nonempty (P.B op)] (x : P.FreeM α) :
    ∃ a, MonadAttach.CanReturn x a := by
  induction x with
  | pure a => exact ⟨a, rfl⟩
  | lift_bind op cont ih =>
    obtain ⟨b⟩ := (inferInstance : Nonempty (P.B op))
    obtain ⟨a, ha⟩ := ih b
    exact ⟨a, b, Set.mem_univ b, ha⟩

end PFunctor.FreeM
