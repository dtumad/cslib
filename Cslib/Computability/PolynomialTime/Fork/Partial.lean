/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.List
public import Cslib.Computability.PolynomialTime.Sigma
public import Cslib.Foundations.Data.PFunctor.Free.Fork.Tape.Partial

/-! # Uniform polynomial overhead for replaying a checked interpreter -/

public section

namespace Turing.MultiTapeTM

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

end Turing.MultiTapeTM
