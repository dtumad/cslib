/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Monad morphisms through `StateT` and `OptionT`

`StateT.mapMonad F` and `OptionT.mapMonad F` change the underlying monad of a stateful or
optional computation along `F : ∀ {α}, m α → n α`. Core's `monadMap` does the same when `F` is an
endomorphism of `m` (`StateT.mapMonad_eq_monadMap`, `OptionT.mapMonad_eq_monadMap`).

If `F` is a monad morphism then so are `StateT.mapMonad F` and `OptionT.mapMonad F`
(`IsMonadHom.stateT`, `IsMonadHom.optionT`).
-/

public section

universe u v w w'

namespace StateT

variable {m : Type u → Type v} {n : Type u → Type w} {p : Type u → Type w'} {σ α : Type u}

/-- Change the underlying monad of a stateful computation along `F`. -/
@[inline, expose]
def mapMonad (F : ∀ {α}, m α → n α) (x : StateT σ m α) : StateT σ n α :=
  .mk fun s => F (x.run s)

@[simp]
theorem run_mapMonad (F : ∀ {α}, m α → n α) (x : StateT σ m α) (s : σ) :
    (mapMonad F x).run s = F (x.run s) := rfl

@[simp]
theorem mapMonad_id (x : StateT σ m α) : mapMonad id x = x := rfl

theorem mapMonad_comp (G : ∀ {α}, n α → p α) (F : ∀ {α}, m α → n α) (x : StateT σ m α) :
    mapMonad (G ∘ F) x = mapMonad G (mapMonad F x) := rfl

theorem mapMonad_eq_monadMap (F : ∀ {α}, m α → m α) (x : StateT σ m α) :
    mapMonad F x = monadMap @F x := rfl

end StateT

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w} {p : Type u → Type w'} {α : Type u}

/-- Change the underlying monad of an optional computation along `F`. -/
@[inline, expose]
def mapMonad (F : ∀ {α}, m α → n α) (x : OptionT m α) : OptionT n α :=
  .mk (F x.run)

@[simp]
theorem run_mapMonad (F : ∀ {α}, m α → n α) (x : OptionT m α) :
    (mapMonad F x).run = F x.run := rfl

@[simp]
theorem mapMonad_id (x : OptionT m α) : mapMonad id x = x := rfl

theorem mapMonad_comp (G : ∀ {α}, n α → p α) (F : ∀ {α}, m α → n α) (x : OptionT m α) :
    mapMonad (G ∘ F) x = mapMonad G (mapMonad F x) := rfl

theorem mapMonad_eq_monadMap (F : ∀ {α}, m α → m α) (x : OptionT m α) :
    mapMonad F x = monadMap @F x := rfl

end OptionT

namespace Cslib.IsMonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {F : ∀ {α}, m α → n α}

/-- A monad morphism `F` gives a monad morphism `StateT.mapMonad F` of state transformers. -/
theorem stateT (hf : IsMonadHom m n F) (σ : Type u) :
    IsMonadHom (StateT σ m) (StateT σ n) (StateT.mapMonad F) :=
  .mk' (fun a => funext fun s => hf.map_pure (a, s))
    (fun x f => funext fun s => hf.map_bind (x.run s) fun p => (f p.1).run p.2)

/-- A monad morphism `F` gives a monad morphism `OptionT.mapMonad F` of option transformers. -/
theorem optionT (hf : IsMonadHom m n F) :
    IsMonadHom (OptionT m) (OptionT n) (OptionT.mapMonad F) :=
  .mk' (fun a => hf.map_pure (some a)) fun x _ =>
    (hf.map_bind x.run _).trans (bind_congr fun | none => hf.map_pure none | some _ => rfl)

end Cslib.IsMonadHom
