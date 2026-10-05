/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Std.WP
public import Cslib.Foundations.Order.Lean

/-!
# Exact weakest-precondition interpretations

Core's `WPMonad` gives inequalities for `pure` and `bind`. `ExactWPMonad` adds the reverse
inequalities, yielding equations and an interpretation in the order dual for upper bounds.
The predicate-transformer interpretation is then a monad morphism. Standard transformer lifts
preserve exactness. Adapted from PolyFun's `Control.Monad.ExactWP`.
-/

@[expose] public section

universe u v w w' z

open Std.WP Lean.Order

namespace Std.WP.WP

-- Follow the namespace of core's `WP` class.
set_option linter.dupNamespace false

open OrderDual

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'}
  [Assertion Pred] [Assertion EPred]

/-- Read a weakest-precondition interpretation in the order duals. -/
@[instance_reducible]
def dual (inst : WP Prog Value Pred EPred) : WP Prog Value Predᵒᵈ EPredᵒᵈ where
  wpTrans x := ⟨fun post epost => toDual (inst.wp x (fun a => ofDual (post a)) (ofDual epost))⟩
  wp_trans_monotone x _ _ _ _ hepost hpost := inst.wp_trans_monotone x _ _ _ _ hepost hpost

@[simp] theorem dual_wp (inst : WP Prog Value Pred EPred) (x : Prog)
    (post : Value → Predᵒᵈ) (epost : EPredᵒᵈ) :
    inst.dual.wp x post epost = toDual (inst.wp x (fun a => ofDual (post a)) (ofDual epost)) := rfl

@[simp] theorem dual_dual (inst : WP Prog Value Pred EPred) : inst.dual.dual = inst := rfl

end Std.WP.WP

namespace Cslib

/-- A weakest-precondition monad whose interpretation also satisfies the reverse, oplax, laws:
core's soundness laws read in the order dual. With `WPMonad.pure_le_wp_pure` and
`WPMonad.bind_le_wp_bind` they make the interpretation distribute over `pure` and `bind` with
equality (`ExactWPMonad.wp_pure`, `ExactWPMonad.wp_bind`). -/
class ExactWPMonad (m : Type u → Type v) (Pred : Type w) (EPred : Type w') [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] : Prop where
  /-- The interpretation of `pure a` is at most the postcondition at `a`. -/
  pure_wp_le {α : Type u} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost ⊑ post a
  /-- The interpretation of `x >>= f` is at most the interpretation of `x` against the
  interpretations of the continuations. -/
  wp_bind_le {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost

namespace ExactWPMonad

/-- An interpretation for which `wp_pure` and `wp_bind` hold as equations is exact. -/
theorem of_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_pure : ∀ {α : Type u} (a : α) (post : α → Pred) (epost : EPred),
      wp (pure a : m α) post epost = post a)
    (wp_bind : ∀ {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred),
      wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost) :
    ExactWPMonad m Pred EPred where
  pure_wp_le a post epost := PartialOrder.rel_of_eq (wp_pure a post epost)
  wp_bind_le x f post epost := PartialOrder.rel_of_eq (wp_bind x f post epost)

section Laws

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred] {α β : Type u}

/-- The interpretation of `pure a` applies the postcondition to `a`. -/
@[simp]
theorem wp_pure (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (pure_wp_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

/-- The interpretation of `x >>= f` is the interpretation of `x` against the interpretations of
the continuations. -/
@[simp]
theorem wp_bind (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (wp_bind_le x f post epost) (WPMonad.bind_le_wp_bind x f post epost)

/-- The interpretation of `f <$> x` is the interpretation of `x` against the postcondition
composed with `f`. -/
@[simp]
theorem wp_map (f : α → β) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <$> x) post epost = wp x (fun a => post (f a)) epost := by
  rw [← bind_pure_comp, wp_bind]
  simp only [wp_pure]

/-- The interpretation of `f <*> x` is the interpretation of `f` against, for each function `g`
that `f` returns, the interpretation of `x` against the postcondition composed with `g`. -/
@[simp]
theorem wp_seq (f : m (α → β)) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <*> x) post epost = wp f (fun g => wp x (fun a => post (g a)) epost) epost := by
  rw [← bind_map, wp_bind]
  simp only [wp_map]

/-- The interpretation of `x <* y` is the interpretation of `x` against, for each value `a` that
`x` returns, the interpretation of `y` against the postcondition at `a`. -/
@[simp]
theorem wp_seqLeft (x : m α) (y : m β) (post : α → Pred) (epost : EPred) :
    wp (x <* y) post epost = wp x (fun a => wp y (fun _ => post a) epost) epost := by
  rw [seqLeft_eq, wp_seq, wp_map]
  rfl

/-- The interpretation of `x *> y` is the interpretation of `x` against the interpretation of
`y`, whatever value `x` returns. -/
@[simp]
theorem wp_seqRight (x : m α) (y : m β) (post : β → Pred) (epost : EPred) :
    wp (x *> y) post epost = wp x (fun _ => wp y post epost) epost := by
  rw [seqRight_eq, wp_seq, wp_map]
  rfl

/-- Exactness is exactly the statement that the interpretation is a monad morphism into
core's predicate-transformer monad. -/
theorem isMonadHom :
    Cslib.IsMonadHom m (PredTrans Pred EPred) WP.wpTrans :=
  Cslib.IsMonadHom.mk' (fun a => PredTrans.ext fun post epost => wp_pure a post epost)
    (fun x f => PredTrans.ext fun post epost => wp_bind x f post epost)

end Laws

/-- An interpretation that is a monad morphism into `PredTrans Pred EPred` is exact. -/
theorem ofIsMonadHom {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (h : Cslib.IsMonadHom m (PredTrans Pred EPred) WP.wpTrans) :
    ExactWPMonad m Pred EPred :=
  of_eq (fun a post epost => congrArg (fun t => PredTrans.apply t post epost) (h.map_pure a))
    (fun x f post epost => congrArg (fun t => PredTrans.apply t post epost) (h.map_bind x f))

/-! ## Exactness as soundness on the dual -/

section Dual

open OrderDual

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred]

/-- The dual reading of an exact interpretation: the same interpretation as a core `WPMonad` over
the order duals, which is sound because the original satisfies the oplax laws. Its triples
`⦃ pre ⦄ x ⦃ post ⦄` state the upper bound `wp x post epost ⊑ pre` in the original order. It is
not an instance: core's assertion types are output parameters, so a global dual would compete
with the original interpretation of `m`. When overriding a direct `WP` instance, install
the chosen `WPMonad`'s `toWP α` locally as well. -/
@[instance_reducible]
def dual [ExactWPMonad m Pred EPred] : WPMonad m Predᵒᵈ EPredᵒᵈ where
  toLawfulMonad := inferInstance
  toWP α := (WPMonad.toWP (m := m) α).dual
  pure_le_wp_pure a post epost := pure_wp_le a (fun a => ofDual (post a)) (ofDual epost)
  bind_le_wp_bind x f post epost := wp_bind_le x f (fun a => ofDual (post a)) (ofDual epost)

/-- The dual reading is exact: its oplax laws are the original interpretation's soundness laws. -/
instance instExactWPMonadDual [ExactWPMonad m Pred EPred] :
    @ExactWPMonad m Predᵒᵈ EPredᵒᵈ _ _ _ (dual (m := m) (Pred := Pred) (EPred := EPred)) :=
  @ExactWPMonad.mk m Predᵒᵈ EPredᵒᵈ _ _ _ dual
    (fun a post epost =>
      WPMonad.pure_le_wp_pure (m := m) a (fun a => ofDual (post a)) (ofDual epost))
    (fun x f post epost =>
      WPMonad.bind_le_wp_bind (m := m) x f (fun a => ofDual (post a)) (ofDual epost))

end Dual

/-! The characterization takes both interpretations explicitly: with one of them in the local
context, instance search for the other would find it first, since core's assertion types are output
parameters. -/

section DualCharacterization

open OrderDual

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred]

/-- Exactness from soundness on the dual: an interpretation over the order duals that agrees with
`inst` and satisfies core's laws there supplies the oplax laws. -/
theorem of_dual (inst : WPMonad m Pred EPred) (d : WPMonad m Predᵒᵈ EPredᵒᵈ)
    (h : ∀ {α : Type u} (x : m α) (post : α → Predᵒᵈ) (epost : EPredᵒᵈ),
      (d.toWP α).wp x post epost = (inst.toWP α).dual.wp x post epost) :
    @ExactWPMonad m Pred EPred _ _ _ inst :=
  @ExactWPMonad.mk m Pred EPred _ _ _ inst
    (fun a post epost => by
      simpa only [h, WP.dual_wp, rel_orderDual, OrderDual.ofDual_toDual] using
        d.pure_le_wp_pure a (fun a => toDual (post a)) (toDual epost))
    (fun x f post epost => by
      simpa only [h, WP.dual_wp, rel_orderDual, OrderDual.ofDual_toDual] using
        d.bind_le_wp_bind x f (fun a => toDual (post a)) (toDual epost))

/-- An interpretation is exact exactly when it is also sound, as the same interpretation, on the
order duals. -/
theorem exactWPMonad_iff_dual (inst : WPMonad m Pred EPred) :
    @ExactWPMonad m Pred EPred _ _ _ inst ↔
      ∃ d : WPMonad m Predᵒᵈ EPredᵒᵈ,
        ∀ {α : Type u} (x : m α) (post : α → Predᵒᵈ) (epost : EPredᵒᵈ),
          (d.toWP α).wp x post epost = (inst.toWP α).dual.wp x post epost :=
  ⟨fun _ => ⟨dual, fun _ _ _ => rfl⟩, fun ⟨d, h⟩ => of_dual inst d h⟩

end DualCharacterization

end ExactWPMonad

/-! ## Core's concrete interpretations -/

instance ExactWPMonad.instId : ExactWPMonad Id.{u} Prop EStack⟨⟩ where
  pure_wp_le _ _ _ := id
  wp_bind_le _ _ _ _ := id

instance ExactWPMonad.instOption : ExactWPMonad Option.{u} Prop (Unit → Prop) where
  pure_wp_le _ _ _ := id
  wp_bind_le x _ _ _ := by cases x <;> exact id

instance ExactWPMonad.instExcept {ε : Type u} : ExactWPMonad (Except ε) Prop (ε → Prop) where
  pure_wp_le _ _ _ := id
  wp_bind_le x _ _ _ := by cases x <;> exact id

instance ExactWPMonad.instEStateM {ε σ : Type} :
    ExactWPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  pure_wp_le _ _ _ _ := id
  wp_bind_le x f post epost s := by
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases x s <;> exact id

/-! ## Core's transformer lifts preserve exactness -/

section Transformers

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

instance ExactWPMonad.instStateT {σ : Type u} : ExactWPMonad (StateT σ m) (σ → Pred) EPred where
  pure_wp_le a post epost s := pure_wp_le (a, s) (fun (a, s) => post a s) epost
  wp_bind_le x _ _ epost s := wp_bind_le (x.run s) _ _ epost

instance ExactWPMonad.instReaderT {ρ : Type u} : ExactWPMonad (ReaderT ρ m) (ρ → Pred) EPred where
  pure_wp_le a post epost r := pure_wp_le a (fun a => post a r) epost
  wp_bind_le x _ _ epost r := wp_bind_le (x.run r) _ _ epost

instance ExactWPMonad.instExceptT {ε : Type u} :
    ExactWPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred) :=
  .of_eq (fun a post epost => wp_pure (.ok a) (pushExcept post epost.1) epost.2)
    (fun x f post epost => by
      simp only [ExceptT.wp_apply_eq, ExceptT.run_bind, wp_bind]
      congr 1
      exact funext fun r => by cases r <;> simp)

end Transformers

section OptionTransformer

variable {m : Type u → Type v} {Pred : Type u} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

instance ExactWPMonad.instOptionT :
    ExactWPMonad (OptionT m) Pred ((Unit → Pred) × EPred) :=
  .of_eq (fun a post epost => wp_pure (some a) (pushOption post epost.1) epost.2)
    (fun x f post epost => by
      simp only [OptionT.wp_apply_eq, OptionT.run_bind, Option.elimM, wp_bind]
      congr 1
      exact funext fun o => by cases o <;> simp)

end OptionTransformer

end Cslib
