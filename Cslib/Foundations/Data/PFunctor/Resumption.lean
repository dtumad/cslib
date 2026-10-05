/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Data.PFunctor.M

/-!
# Coinductive resumptions over polynomial interfaces

A `Resumption p β` is a possibly infinite, tau-free computation that either
returns a value in `β` or exposes a visible query from `p` and continues from
the selected direction. It is the M-type of the return-or-query polynomial
`p + C β`, the coinductive counterpart of `FreeM p β`.

This is the identity-monad case of the coalgebraic resumption construction
`ν X, T (β ⊕ p X)` (Goncharov, Milius, and Rauch, *Complete Elgot Monads and Coalgebraic
Resumptions*, 2016). It differs from the cofree comonad, whose one-step view is
`β × p X`: a cofree value labels every node, whereas a resumption returns a value only at a leaf.

The named `map` and `bind` operations are maximally universe-polymorphic in
their source and target result types. The `Monad` and `LawfulMonad` instances
cover the ordinary specialization in which those result types live in one
chosen universe. Adapted from `PolyFun.PFunctor.Resumption`.
-/

@[expose] public section

universe uA uB uα uβ uγ uX uY

namespace PFunctor

/-- A possibly infinite, tau-free computation that returns a `β` or performs a
visible query from `p`. -/
abbrev Resumption (p : PFunctor.{uA, uB}) (β : Type uβ) :=
  M.{max uβ uA, uB} (p + C.{uβ, uB} β)

namespace Resumption

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-! ## One-step views -/

/-- Reassociate the extension of `p + C β` into the computational
return-or-query view. -/
def unpack {X : Type uX} : (p + C.{uβ, uB} β).Obj X → β ⊕ p.Obj X
  | .mk (Sum.inl position) next => Sum.inr (.mk position next)
  | .mk (Sum.inr value) _ => Sum.inl value

/-- Repack a computational return-or-query view as an extension of `p + C β`. -/
def pack {X : Type uX} : β ⊕ p.Obj X → (p + C.{uβ, uB} β).Obj X
  | Sum.inl value => .mk (Sum.inr value) PEmpty.elim
  | Sum.inr (.mk position next) => .mk (Sum.inl position) next

/- The right-hand sides are spelled with `.mk`, the constructor Mathlib's `M`-type
API (`M.bisim`, `M.dest_mk`, …) states its equations with. -/
@[simp] theorem pack_inl {X : Type uX} (value : β) :
    pack (p := p) (X := X) (Sum.inl value) = .mk (Sum.inr value) PEmpty.elim := rfl

@[simp] theorem pack_inr {X : Type uX} (position : p.A) (next : p.B position → X) :
    pack (Sum.inr (.mk position next) : β ⊕ p.Obj X) = .mk (Sum.inl position) next := rfl

@[simp] theorem unpack_pack {X : Type uX} (step : β ⊕ p.Obj X) :
    unpack (pack step) = step := by
  cases step with
  | inl _ => rfl
  | inr step => rcases step with ⟨_, _⟩; rfl

@[simp] theorem pack_unpack {X : Type uX} (step : (p + C.{uβ, uB} β).Obj X) :
    pack (unpack step) = step := by
  rcases step with ⟨shape, next⟩
  cases shape with
  | inl position => rfl
  | inr value => exact Sigma.ext rfl (heq_of_eq (funext fun d => d.elim))

/-- The extension of `p + C β` is equivalent to the computational
return-or-query view. -/
def viewEquiv {X : Type uX} : (p + C.{uβ, uB} β).Obj X ≃ β ⊕ p.Obj X where
  toFun := unpack
  invFun := pack
  left_inv := pack_unpack
  right_inv := unpack_pack

@[simp] theorem unpack_map {X : Type uX} {Y : Type uY} (f : X → Y)
    (step : (p + C.{uβ, uB} β).Obj X) :
    unpack ((p + C.{uβ, uB} β).map f step) =
      Sum.map id (p.map f) (unpack step) := by
  rcases step with ⟨shape, next⟩
  cases shape <;> rfl

theorem pack_sum_map {X : Type uX} {Y : Type uY} (f : X → Y)
    (step : β ⊕ p.Obj X) :
    pack (Sum.map id (p.map f) step) =
      (p + C.{uβ, uB} β).map f (pack step) := by
  apply viewEquiv.injective
  simp only [viewEquiv, Equiv.coe_fn_mk, unpack_pack, unpack_map]

/-! ## Constructors, destructor, and corecursor -/

/-- A resumption that immediately returns `value`. -/
def pure (value : β) : Resumption p β :=
  M.mk (pack (Sum.inl value))

/-- A resumption that exposes `position` and continues according to the
selected direction. -/
def query (position : p.A) (next : p.B position → Resumption p β) : Resumption p β :=
  M.mk (pack (Sum.inr (.mk position next)))

/-- Observe whether a resumption returns or performs a visible query. -/
def dest (computation : Resumption p β) : β ⊕ p.Obj (Resumption p β) :=
  unpack (M.dest computation)

@[simp] theorem pack_dest (computation : Resumption p β) :
    pack (dest computation) = M.dest computation :=
  pack_unpack _

/-- The computational destructor is injective. -/
theorem dest_injective : Function.Injective (dest (p := p) (β := β)) :=
  viewEquiv.injective.comp M.dest_injective

@[simp] theorem dest_inj {left right : Resumption p β} :
    dest left = dest right ↔ left = right :=
  dest_injective.eq_iff

/-- Build a resumption from a return-or-query coalgebra. -/
def corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) : Resumption p β :=
  M.corec (fun state => pack (step state)) seed

@[simp] theorem dest_pure (value : β) : dest (pure (p := p) value) = Sum.inl value := by
  simp only [dest, pure, M.dest_mk, unpack_pack]

@[simp] theorem dest_query (position : p.A) (next : p.B position → Resumption p β) :
    dest (query position next) = Sum.inr (.mk position next) := by
  simp only [dest, query, M.dest_mk, unpack_pack]

@[simp] theorem dest_corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) :
    dest (corec step seed) =
      Sum.map id (p.map (corec step)) (step seed) := by
  unfold dest corec
  rw [M.dest_corec, unpack_map, unpack_pack]

/-- Corecursing from the destructor reconstructs the original resumption. -/
@[simp] theorem corec_dest (computation : Resumption p β) :
    corec dest computation = computation := by
  simpa only [corec, pack_dest] using M.corec_dest computation

/-! ## Coinduction and finality -/

/-- Two resumptions have matching computational heads with respect to `R`
when they return the same value, or expose the same query position and have
pointwise `R`-related continuations. -/
inductive HeadMatch (R : Resumption p β → Resumption p β → Prop) :
    Resumption p β → Resumption p β → Prop where
  | pure {left right : Resumption p β} (value : β)
      (left_dest : dest left = Sum.inl value)
      (right_dest : dest right = Sum.inl value) :
      HeadMatch R left right
  | query {left right : Resumption p β} (position : p.A)
      (left_next right_next : p.B position → Resumption p β)
      (left_dest : dest left = Sum.inr (.mk position left_next))
      (right_dest : dest right = Sum.inr (.mk position right_next))
      (next_rel : ∀ direction, R (left_next direction) (right_next direction)) :
      HeadMatch R left right

/-- Every resumption has a head matching itself. -/
theorem HeadMatch.refl (computation : Resumption p β) : HeadMatch Eq computation computation := by
  rcases h : dest computation with value | ⟨position, next⟩
  · exact .pure value h h
  · exact .query position next next h h (fun _ => rfl)

/-- Strengthen the relation used below a matching pair of resumption heads. -/
theorem HeadMatch.mono {R S : Resumption p β → Resumption p β → Prop}
    (hRS : ∀ {left right}, R left right → S left right)
    {left right : Resumption p β} (h : HeadMatch R left right) :
    HeadMatch S left right := by
  cases h with
  | pure value left_dest right_dest =>
      exact .pure value left_dest right_dest
  | query position left_next right_next left_dest right_dest next_rel =>
      exact .query position left_next right_next left_dest right_dest
        (fun direction => hRS (next_rel direction))

/-- Computational-view bisimulation principle for resumptions. Clients need
not expose the implementation polynomial `p + C β` or use raw `M.bisim`. -/
theorem bisim (R : Resumption p β → Resumption p β → Prop)
    (step : ∀ left right, R left right → HeadMatch R left right)
    {left right : Resumption p β} (h : R left right) : left = right := by
  refine M.bisim R ?_ left right h
  intro currentLeft currentRight hrel
  cases step currentLeft currentRight hrel with
  | pure value left_dest right_dest =>
      refine ⟨Sum.inr value, PEmpty.elim, PEmpty.elim, ?_, ?_, fun direction => ?_⟩
      · rw [← pack_dest, left_dest, pack_inl]
      · rw [← pack_dest, right_dest, pack_inl]
      · exact direction.elim
  | query position left_next right_next left_dest right_dest next_rel =>
      refine ⟨Sum.inl position, left_next, right_next, ?_, ?_, next_rel⟩
      · rw [← pack_dest, left_dest, pack_inr]
      · rw [← pack_dest, right_dest, pack_inr]

/-- Finality of `Resumption`: a function satisfying the computational
coalgebra equation is the computational corecursor. -/
theorem corec_unique {X : Type uX} (step : X → β ⊕ p.Obj X)
    (f : X → Resumption p β)
    (hf : ∀ state, dest (f state) =
      Sum.map id (p.map f) (step state)) :
    f = corec step := by
  unfold corec
  apply M.corec_unique (fun state => pack (step state)) f
  intro state
  rw [← pack_dest, hf]
  exact pack_sum_map f (step state)

/-- A map of coalgebra states commutes with corecursion. -/
theorem corec_comp {X : Type uX} {Y : Type uY}
    (step : X → β ⊕ p.Obj X) (step' : Y → β ⊕ p.Obj Y) (f : X → Y)
    (hf : ∀ x, step' (f x) = Sum.map id (p.map f) (step x)) :
    corec step' ∘ f = corec step :=
  M.corec_comp (pack ∘ step) (pack ∘ step') f
    (fun x => by simpa only [Function.comp_apply, hf] using pack_sum_map f (step x))

/-! ## Functorial and monadic structure -/

/-- Lift one visible query, returning the selected direction. -/
def lift (position : p.A) : Resumption p (p.B position) :=
  query position pure

@[simp] theorem dest_lift (position : p.A) :
    dest (lift position) = Sum.inr (.mk position pure) := by
  simp [lift]

/-- Step coalgebra used by `bind`. The right summand records that execution has
entered the continuation selected by a returned source value. -/
def bindStep (k : α → Resumption p β) :
    Resumption p α ⊕ Resumption p β →
      β ⊕ p.Obj (Resumption p α ⊕ Resumption p β)
  | Sum.inl computation =>
      (dest computation).elim
        (fun value => Sum.map id (p.map Sum.inr) (dest (k value)))
        (fun step => Sum.inr (p.map Sum.inl step))
  | Sum.inr computation => Sum.map id (p.map Sum.inr) (dest computation)

/-- Monadic bind on resumptions. Named bind permits source and target result
types in different universes. -/
def bind (computation : Resumption p α) (k : α → Resumption p β) : Resumption p β :=
  corec (bindStep k) (Sum.inl computation)

/-- Map a function over the returned value of a resumption. Named map permits
source and target result types in different universes. -/
def map (f : α → β) (computation : Resumption p α) : Resumption p β :=
  bind computation (fun value => pure (f value))

private theorem corec_bindStep_inr (k : α → Resumption p β)
    (computation : Resumption p β) :
    corec (bindStep k) (Sum.inr computation) = computation :=
  (congrFun (corec_comp dest (bindStep k) Sum.inr (fun _ => rfl)) computation).trans
    (corec_dest computation)

@[simp] theorem dest_bind (computation : Resumption p α) (k : α → Resumption p β) :
    dest (bind computation k) =
      match dest computation with
      | Sum.inl value => dest (k value)
      | Sum.inr (.mk position next) =>
          Sum.inr (.mk position (fun direction => bind (next direction) k)) := by
  unfold bind
  rw [dest_corec]
  rcases h : dest computation with value | ⟨position, next⟩
  · rcases hk : dest (k value) with result | ⟨position, next⟩
    <;> simp [bindStep, h, hk, PFunctor.map, Function.comp_def, corec_bindStep_inr]
  · simp only [bindStep, h]
    rfl

@[simp] theorem bind_pure_left (value : α) (k : α → Resumption p β) :
    bind (pure value) k = k value := by
  apply dest_injective
  simp

@[simp] theorem bind_query (position : p.A) (next : p.B position → Resumption p α)
    (k : α → Resumption p β) :
    bind (query position next) k = query position (fun direction => bind (next direction) k) := by
  apply dest_injective
  simp

@[simp] theorem bind_pure_right (computation : Resumption p α) :
    bind computation pure = computation := by
  refine bisim (fun left right => left = bind right pure) ?_ rfl
  rintro _ right rfl
  rcases h : dest right with value | ⟨position, next⟩
  · exact .pure value (by simp [dest_bind, h]) h
  · exact .query position (fun direction => bind (next direction) pure) next
      (by simp [dest_bind, h]) h (fun _ => rfl)

theorem bind_assoc (computation : Resumption p α) (k : α → Resumption p β)
    (k' : β → Resumption p γ) :
    bind (bind computation k) k' = bind computation (fun value => bind (k value) k') := by
  refine bisim
    (fun (left right : Resumption p γ) => left = right ∨ ∃ source : Resumption p α,
      left = bind (bind source k) k' ∧
      right = bind source (fun value => bind (k value) k')) ?_
    (Or.inr ⟨computation, rfl, rfl⟩)
  rintro left right (rfl | ⟨source, rfl, rfl⟩)
  · exact (HeadMatch.refl _).mono Or.inl
  · rcases h : dest source with value | ⟨position, next⟩
    · rw [show source = pure value by
        apply dest_injective
        simpa using h]
      simp only [bind_pure_left]
      exact (HeadMatch.refl _).mono Or.inl
    · exact .query position _ _ (by simp [h]) (by simp [h])
        (fun direction => Or.inr ⟨next direction, rfl, rfl⟩)

@[simp] theorem map_pure (f : α → β) (value : α) :
    map f (pure (p := p) value) = pure (f value) := by
  simp [map]

@[simp] theorem map_query (f : α → β) (position : p.A)
    (next : p.B position → Resumption p α) :
    map f (query position next) = query position (fun direction => map f (next direction)) := by
  simp [map]

@[simp] theorem map_id (computation : Resumption p α) :
    map id computation = computation := bind_pure_right computation

theorem map_comp (g : β → γ) (f : α → β) (computation : Resumption p α) :
    map (g ∘ f) computation = map g (map f computation) := by
  rw [map, map, map, bind_assoc]
  simp

section Instances

universe u

variable {p : PFunctor.{uA, uB}} {α β γ : Type u}

instance instMonad : Monad (Resumption p) where
  pure := pure
  bind := bind

@[simp] theorem map_eq_map (f : α → β) (computation : Resumption p α) :
    f <$> computation = map f computation := rfl

instance instLawfulMonad : LawfulMonad (Resumption p) := LawfulMonad.mk'
  (bind_pure_comp := by intros; rfl)
  (id_map := map_id)
  (pure_bind := bind_pure_left)
  (bind_assoc := bind_assoc)

end Instances

end Resumption

end PFunctor
