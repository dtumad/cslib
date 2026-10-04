/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Measure

/-!
# Binding machine ports to oracle operations

Renaming a port changes its operation name, retaining the request, response, and continuation.
Different ports may call the same operation on the same shared state. Private coins remain private.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open PFunctor MeasureTheory ProbabilityTheory

variable {Oracle Oracle' α : Type}

/-- Interpret each named request at its renamed port, leaving private coin requests unchanged. -/
def rename (name : Oracle → Oracle') (op : (effects Oracle).A) :
    (effects Oracle').FreeM ((effects Oracle).B op) :=
  match op with
  | .inl _ => coin
  | .inr (port, word) => query (name port) word

@[simp] theorem liftM_rename_coin (name : Oracle → Oracle') :
    (coin (Oracle := Oracle)).liftM (rename name) = coin :=
  FreeM.liftM_lift (rename name) (.inl ())

@[simp] theorem liftM_rename_query (name : Oracle → Oracle') (port : Oracle) (word : List Bool) :
    (query port word).liftM (rename name) = query (name port) word :=
  FreeM.liftM_lift (rename name) (.inr (port, word))

/-- Independent private bits are unchanged when communication ports are renamed. -/
@[simp] theorem liftM_rename_sampleBits (name : Oracle → Oracle') (n : ℕ) :
    ((List.replicate n ()).mapM (fun _ => coin (Oracle := Oracle))).liftM (rename name) =
      (List.replicate n ()).mapM (fun _ => coin (Oracle := Oracle')) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.mapM_cons, ih]

/-- Renaming preserves the possible return values, even if several names are identified. -/
@[simp] theorem canReturn_liftM_rename (name : Oracle → Oracle')
    (program : (effects Oracle).FreeM α) (value : α) :
    MonadAttach.CanReturn (program.liftM (rename name)) value ↔
      MonadAttach.CanReturn program value := by
  induction program with
  | pure result => rfl
  | lift_bind op cont ih =>
    cases op with
    | inl token => cases token; exact exists_congr ih
    | inr request => cases request; exact exists_congr ih

variable [MeasurableSpace (List Bool)] [DiscreteMeasurableSpace (List Bool)]
  {S : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace α]

/-- Port aliases use the original shared oracle state, including when names coincide. -/
theorem runKernel_liftM_rename (name : Oracle → Oracle')
    (oracle : Oracle' → List Bool → Kernel S (List Bool × S))
    (program : (effects Oracle).FreeM α) (state : S) :
    FreeM.runKernel (effectKernel oracle) (program.liftM (rename name)) state =
      FreeM.runKernel (effectKernel (fun port => oracle (name port))) program state := by
  rw [FreeM.runKernel_liftM]
  congr 2
  funext op
  cases op with
  | inl token =>
    ext state : 1
    exact FreeM.runKernel_lift (effectKernel oracle) (.inl ()) state
  | inr request =>
    ext state : 1
    exact FreeM.runKernel_lift (effectKernel oracle) (.inr (name request.1, request.2)) state

end Turing.MultiTapePTM
