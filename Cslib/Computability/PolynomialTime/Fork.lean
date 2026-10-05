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

section Total

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

end Total

section Aborting

open PFunctor

variable {Input : Type} {Result Operation Answer : Input → Type}
  (input : Input ↪ Word) (output : ∀ i, Result i ↪ Word)
  (operation : ∀ i, Operation i ↪ Word) (answer : ∀ i, Answer i ↪ Word)

/-- Replay has uniform polynomial overhead even when the result, operation, and answer types
depend on the input. The selector handles optional executions, so no default result is needed.
Both interpreter calls retain exactly the same input, including any saved private randomness. -/
theorem isPolyTime_forkFromTracedAnswers
    (run : ∀ i, List (Answer i) →
      Option (Result i × List (Sigma (PFunctor.mk (Operation i) (fun _ => Answer i)).B)))
    (choose : ∀ i, Result i × List (Sigma (PFunctor.mk (Operation i) (fun _ => Answer i)).B) →
      Option ℕ)
    (hrun : IsPolyTime (sigmaEncoding input (fun i => listEncoding (answer i)))
      (fun pair => optionEncoding (pairEncoding (output pair.1)
        (listEncoding (sigmaEncoding (operation pair.1) (fun _ => answer pair.1))))
          (run pair.1 pair.2)))
    (hchoose : IsPolyTime (sigmaEncoding input (fun i => optionEncoding
      (pairEncoding (output i) (listEncoding (sigmaEncoding (operation i) (fun _ => answer i))))))
      (fun pair => optionEncoding unaryEncoding (pair.2.bind (choose pair.1)))) :
    IsPolyTime (sigmaEncoding input (fun i => pairEncoding
      (listEncoding (answer i)) (listEncoding (answer i))))
      (fun pair => optionEncoding (pairEncoding
        (pairEncoding (output pair.1)
          (listEncoding (sigmaEncoding (operation pair.1) (fun _ => answer pair.1))))
        (sigmaEncoding (operation pair.1) (fun _ => pairEncoding (answer pair.1)
          (pairEncoding (answer pair.1) (pairEncoding (output pair.1)
            (listEncoding (sigmaEncoding (operation pair.1) (fun _ => answer pair.1))))))))
        (FreeM.forkFromTracedAnswers (run pair.1) (choose pair.1) pair.2.1 pair.2.2)) := by
  let event i := sigmaEncoding (operation i) (fun _ => answer i)
  let args := sigmaEncoding input (fun i => pairEncoding
    (listEncoding (answer i)) (listEncoding (answer i)))
  have hi := isPolyTime_input args
  have hleft : IsPolyTime args (fun pair => listEncoding (answer pair.1) pair.2.1) := by
    simpa only [pairEncoding_apply, List.BitPair.fst_encode] using hi.sigma_snd.bitPair_fst
  have hright : IsPolyTime args (fun pair => listEncoding (answer pair.1) pair.2.2) := by
    simpa only [pairEncoding_apply, List.BitPair.snd_encode] using hi.sigma_snd.bitPair_snd
  have hfirst := hrun.comp_encoded (hi.sigma_fst.sigma hleft)
  have hindex := hchoose.comp_encoded (hi.sigma_fst.sigma hfirst)
  have hn := hindex.option_getD (fallback := fun _ => 0) (isPolyTime_const args [])
  let events (pair : Σ i, List (Answer i) × List (Answer i)) :=
    ((run pair.1 pair.2.1).map Prod.snd).getD []
  have hevents : IsPolyTime args (fun pair => listEncoding (event pair.1) (events pair)) := by
    convert hfirst.tail.bitPair_snd using 1
    funext pair
    dsimp only [events]
    cases run pair.1 pair.2.1 with
    | none => rfl
    | some out => simp [event, optionEncoding_some, pairEncoding_apply]
  have hevent := (hevents.list_drop_indexed hn).list_head?_indexed
  have hbefore := hevents.list_take_indexed hn
  have hwords : IsPolyTime args
      (fun pair => listEncoding wordEncoding
        (((events pair).take (((run pair.1 pair.2.1).bind (choose pair.1)).getD 0)).map
          (event pair.1))) := by
    simpa only [listEncoding_map (event _) wordEncoding (event _) (fun _ => rfl)] using hbefore
  have hprefix : IsPolyTime args (fun pair => listEncoding (answer pair.1)
      (((events pair).take (((run pair.1 pair.2.1).bind (choose pair.1)).getD 0)).map
        (fun event => event.2))) := by
    convert hwords.list_map (output := wordEncoding) (f := List.BitPair.snd)
      (isPolyTime_input wordEncoding).bitPair_snd using 1
    funext pair
    have heq (entry : Sigma (PFunctor.mk (Operation pair.1) (fun _ => Answer pair.1)).B) :
        List.BitPair.snd (event pair.1 entry) = answer pair.1 entry.2 := by
      simp [event, sigmaEncoding]
    simp only [List.map_map, Function.comp_def, heq]
    simpa only [List.map_map, Function.comp_def] using
      (listEncoding_map (answer pair.1) wordEncoding (answer pair.1) (fun _ => rfl)
        (((events pair).take (((run pair.1 pair.2.1).bind (choose pair.1)).getD 0)).map
          (fun event => event.2))).symm
  have happend : IsPolyTime args (fun pair => listEncoding (answer pair.1)
      ((((events pair).take (((run pair.1 pair.2.1).bind (choose pair.1)).getD 0)).map
        (fun event => event.2)) ++ pair.2.2)) := by
    simpa only [listEncoding_append] using hprefix.append hright
  have hsecond := hrun.comp_encoded (hi.sigma_fst.sigma happend)
  have hfresh := hright.list_head?_indexed
  have hout := (hfirst.tail.pair (left := wordEncoding) (right := wordEncoding)
    (hevent.tail.bitPair_fst.pair (left := wordEncoding) (right := wordEncoding)
      (hevent.tail.bitPair_snd.pair (left := wordEncoding) (right := wordEncoding)
        (hfresh.tail.pair (left := wordEncoding) (right := wordEncoding)
          hsecond.tail)))).option_some
  have hsecondOk := hsecond.option_isSome.cond hout (isPolyTime_const args [])
  have hfreshOk := hfresh.option_isSome.cond hsecondOk (isPolyTime_const args [])
  have heventOk := hevent.option_isSome.cond hfreshOk (isPolyTime_const args [])
  have hindexOk := hindex.option_isSome.cond heventOk (isPolyTime_const args [])
  convert hfirst.option_isSome.cond hindexOk (isPolyTime_const args []) using 1
  funext pair
  dsimp only [FreeM.forkFromTracedAnswers]
  cases hfirstRun : run pair.1 pair.2.1 with
  | none => rfl
  | some first =>
    dsimp +instances only [Bind.bind, Option.bind]
    simp only [events, hfirstRun, Option.map_some, Option.getD_some, Option.isSome_some,
      ↓reduceIte]
    cases choose pair.1 first with
    | none => simp
    | some index =>
      simp only [Option.elim_some, Option.getD_some, Option.isSome_some, ↓reduceIte,
        List.head?_drop]
      cases first.2[index]? with
      | none => simp
      | some focus =>
        rcases focus with ⟨op, old⟩
        simp only [Option.isSome_some, ↓reduceIte]
        cases pair.2.2.head? with
        | none => simp
        | some fresh =>
          simp only [Option.isSome_some, ↓reduceIte]
          cases run pair.1 ((first.2.take index).map (fun event => event.2) ++ pair.2.2) <;>
            simp [event, sigmaEncoding, pairEncoding_apply, wordEncoding]
          rfl

end Aborting

end Turing.MultiTapeTM
