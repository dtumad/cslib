/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.List
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape

/-!
# Polynomial overhead of forking by answer-tape replay

A certified traced interpreter and selector suffice for two executions. The compiler copies the
selected answer prefix and reruns the same interpreter; it never represents program continuations.
All visible operations are forkable, as in a hash-only program after fixing private randomness.
-/

public section

namespace Turing.MultiTapeTM

open PFunctor

variable {Input Result Operation Answer : Type}
  [Inhabited Result] [Inhabited Operation] [Inhabited Answer]
  (input : Input ↪ Word) (output : Result ↪ Word)
  (operation : Operation ↪ Word) (answer : Answer ↪ Word)

/-- Replaying at a selected hash has polynomial overhead over the supplied traced interpreter.
The input retains any fixed private tapes, so the second execution uses the very same seed.
The certificate covers arbitrary answer tapes, including exhaustion and invalid selections. -/
theorem isPolyTime_forkFromAnswers
    (program : Input → (PFunctor.mk Operation (fun _ => Answer)).FreeM Result)
    (choose : Input → Result → Option ℕ)
    (hrun : IsPolyTime (pairEncoding input (listEncoding answer))
      (fun pair => optionEncoding
        (pairEncoding output (listEncoding (sigmaEncoding operation (fun _ => answer))))
        (FreeM.runFromAnswers (FreeM.trace (program pair.1)) pair.2)))
    (hchoose : IsPolyTime (pairEncoding input output)
      (fun pair => optionEncoding unaryEncoding (choose pair.1 pair.2))) :
    IsPolyTime (pairEncoding input (pairEncoding (listEncoding answer) (listEncoding answer)))
      (fun pair => optionEncoding (pairEncoding output (optionEncoding
        (sigmaEncoding operation (fun _ => pairEncoding answer (pairEncoding answer output)))))
        (FreeM.forkFromAnswers (fun _ => true) (choose pair.1) (program pair.1)
          pair.2.1 pair.2.2)) := by
  let event := sigmaEncoding operation (fun _ => answer)
  let first := pairEncoding output (listEncoding event)
  let forked := sigmaEncoding operation (fun _ => pairEncoding answer (pairEncoding answer output))
  let args := pairEncoding input (pairEncoding (listEncoding answer) (listEncoding answer))
  have hi := isPolyTime_input args
  have hfirst := hrun.comp_encoded (hi.fst.pair hi.snd.fst)
  have hsaved := hfirst.option_getD (fallback := fun _ => (default, []))
    (isPolyTime_const args (first (default, [])))
  have hindex := hchoose.comp_encoded (hi.fst.pair hsaved.fst)
  have hn := hindex.option_getD (fallback := fun _ => 0) (isPolyTime_const args [])
  have hevent := (hsaved.snd.list_drop hn).list_head?
  have he := hevent.option_getD (fallback := fun _ => ⟨default, default⟩)
    (isPolyTime_const args (event ⟨default, default⟩))
  have hprefix := (hsaved.snd.list_take hn).list_map
    (isPolyTime_input event).sigma_snd
  have hfresh := hi.snd.snd.list_head?
  have ha := hfresh.option_getD (isPolyTime_const args (answer default))
  have hsecond := hrun.comp_encoded (hi.fst.pair (hprefix.list_append hi.snd.snd))
  have hread := hsecond.option_getD (fallback := fun _ => (default, []))
    (isPolyTime_const args (first (default, [])))
  have hout := he.sigma_fst.sigma
    (element := fun _ => pairEncoding answer (pairEncoding answer output))
    (he.sigma_snd.pair (left := answer) (right := pairEncoding answer output)
      (ha.pair hread.fst))
  have hsome := (hsaved.fst.pair (right := optionEncoding forked) hout.option_some).option_some
  have habsent := (hsaved.fst.pair (right := optionEncoding forked) (g := fun _ => none)
    (isPolyTime_const args [])).option_some
  have hsecondOk := hsecond.option_isSome.cond hsome (isPolyTime_const args [])
  have hfreshOk := hfresh.option_isSome.cond hsecondOk (isPolyTime_const args [])
  have hfocus := hevent.option_isSome.cond hfreshOk habsent
  have hselected := hindex.option_isSome.cond hfocus habsent
  convert hfirst.option_isSome.cond hselected (isPolyTime_const args []) using 1
  funext pair
  simp only [FreeM.forkFromAnswers]
  cases hfirstRun : FreeM.runFromAnswers (FreeM.trace (program pair.1)) pair.2.1 with
  | none => rfl
  | some result =>
    rcases result with ⟨value, events⟩
    have hrun : FreeM.runFromAnswers (program pair.1) = fun tape =>
        (FreeM.runFromAnswers (FreeM.trace (program pair.1)) tape).map Prod.fst := by
      funext tape
      rw [← FreeM.runFromAnswers_map, FreeM.map_fst_trace]
    dsimp +instances only [Bind.bind, Option.bind]
    simp only [Option.getD_some, Option.isSome_some, ↓reduceIte]
    cases choose pair.1 value with
    | none => simp; rfl
    | some index =>
      classical
      simp only [Option.elim_some, FreeM.restartFromAnswers, FreeM.forkPrefix_true,
        Option.getD_some, Option.isSome_some, ↓reduceIte, List.head?_drop]
      cases events[index]? with
      | none => simp; rfl
      | some focus =>
        rcases focus with ⟨op, old⟩
        simp only [Option.map_some, Option.elim_some, Option.getD_some, Option.isSome_some,
          ↓reduceIte, hrun]
        cases pair.2.2.head? with
        | none => simp
        | some fresh =>
          simp only [Option.getD_some, Option.isSome_some,
            ↓reduceIte]
          cases FreeM.runFromAnswers (FreeM.trace (program pair.1))
            ((events.take index).map (fun event => event.2) ++ pair.2.2) <;>
              simp [forked, sigmaEncoding, pairEncoding_apply]

end Turing.MultiTapeTM
