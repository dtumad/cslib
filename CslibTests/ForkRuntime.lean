/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Fork
import Cslib.Computability.PolynomialTime.Fork.Partial
import Cslib.Tactic.PolyTime

/-! The two-run compiler constructs a machine from a checked one-query interpreter. All
input words and tape lengths remain arbitrary; the example includes exhausted tapes. -/

namespace ForkRuntime

open PFunctor Turing.MultiTapeTM

abbrev effects : PFunctor := ⟨Bool, fun _ => Bool⟩

def program (_ : Word) : effects.FreeM Bool := FreeM.lift true

example : IsPolyTime
    (pairEncoding wordEncoding
      (pairEncoding (listEncoding boolEncoding) (listEncoding boolEncoding)))
    (fun pair => optionEncoding (pairEncoding boolEncoding (optionEncoding
      (sigmaEncoding boolEncoding (fun _ =>
        pairEncoding boolEncoding (pairEncoding boolEncoding boolEncoding)))))
      (FreeM.forkFromAnswers (fun _ => true) (fun _ => some 0) (program pair.1)
        pair.2.1 pair.2.2)) := by
  apply isPolyTime_forkFromAnswers wordEncoding boolEncoding boolEncoding boolEncoding
    program (fun _ _ => some 0)
  · let input := pairEncoding wordEncoding (listEncoding boolEncoding)
    let event := sigmaEncoding boolEncoding (fun _ => boolEncoding)
    have hhead := (isPolyTime_snd wordEncoding (listEncoding boolEncoding)).list_head?
    have hbit := hhead.option_getD (fallback := fun _ => false) (isPolyTime_const input [false])
    have hevent := (isPolyTime_const input [true]).sigma
      (index := boolEncoding) (element := fun _ => boolEncoding) (parameter := fun _ => true) hbit
    have htrace := hevent.list_cons (rest := fun _ => [])
      (isPolyTime_const input (listEncoding event []))
    have hsuccess := (hbit.pair htrace).option_some
    convert hhead.option_isSome.cond hsuccess (isPolyTime_const input []) using 1
    funext pair
    cases pair.2 <;> rfl
  · exact isPolyTime_const _ [true]

example : IsPolyTime wordEncoding
    (fun word => optionEncoding unaryEncoding (word.findIdx? id)) := by
  polytime

/-- A checked interpreter may discard its log on failure. The input is a saved private seed. -/
def checkedRun (seed : Word) (answers : List Bool) : Option (Word × List (Sigma effects.B)) := do
  let bit ← answers.head?
  if bit then some (seed, [⟨true, bit⟩]) else none

example : IsPolyTime (sigmaEncoding wordEncoding (fun _ =>
    pairEncoding (listEncoding boolEncoding) (listEncoding boolEncoding)))
    (fun pair => optionEncoding (pairEncoding
      (pairEncoding wordEncoding
        (listEncoding (sigmaEncoding boolEncoding (fun _ => boolEncoding))))
      (sigmaEncoding boolEncoding (fun _ => pairEncoding boolEncoding (pairEncoding boolEncoding
        (pairEncoding wordEncoding
          (listEncoding (sigmaEncoding boolEncoding (fun _ => boolEncoding))))))))
      (FreeM.forkFromTracedAnswers (checkedRun pair.1) (fun _ => some 0) pair.2.1 pair.2.2)) := by
  apply isPolyTime_forkFromTracedAnswers wordEncoding (fun _ => wordEncoding)
    (fun _ => boolEncoding) (fun _ => boolEncoding) checkedRun (fun _ _ => some 0)
  · let input := sigmaEncoding wordEncoding (fun _ => listEncoding boolEncoding)
    let event := sigmaEncoding boolEncoding (fun _ => boolEncoding)
    have hi := isPolyTime_input input
    have hhead := hi.sigma_snd.list_head?
    have hbit := hhead.option_getD (fallback := fun _ => false) (isPolyTime_const input [false])
    have hout := (hi.sigma_fst.pair
      (isPolyTime_const input (listEncoding event [⟨true, true⟩]))).option_some
    convert hbit.cond hout (isPolyTime_const input []) using 1
    funext pair
    simp only [checkedRun]
    cases pair.2.head? with
    | none => rfl
    | some bit => cases bit <;> rfl
  · let input := sigmaEncoding wordEncoding (fun _ => optionEncoding
      (pairEncoding wordEncoding
        (listEncoding (sigmaEncoding boolEncoding (fun _ => boolEncoding)))))
    convert (isPolyTime_input input).sigma_snd.option_isSome.cond
      (isPolyTime_const input [true]) (isPolyTime_const input []) using 1
    funext pair
    cases pair.2 <;> rfl

def adaptiveCheckedRun (seed : Bool) (answers : List Bool) :
    Option (Bool × List (Sigma effects.B)) :=
  (FreeM.runFromAnswers (FreeM.trace (do
    let first ← FreeM.lift (P := effects) false
    let second ← FreeM.lift (P := effects) (first != seed)
    pure (if first && second then some seed else none))) answers).bind
      (fun out => out.1.map (fun value => (value, out.2)))

-- A one-answer fresh tape suffices: the selected prefix is copied from the first run.
example : FreeM.forkFromTracedAnswers (adaptiveCheckedRun true) (fun _ => some 1)
    [true, true] [true] = some ((true, [⟨false, true⟩, ⟨false, true⟩]),
      ⟨false, true, true, true, [⟨false, true⟩, ⟨false, true⟩]⟩) := rfl

-- Failure in either execution contributes no successful fork.
example : FreeM.forkFromTracedAnswers (adaptiveCheckedRun true) (fun _ => some 1)
    [false, true] [true] = none := rfl

example : FreeM.forkFromTracedAnswers (adaptiveCheckedRun true) (fun _ => some 1)
    [true, true] [false] = none := rfl

example : FreeM.forkFromTracedAnswers (adaptiveCheckedRun true) (fun _ => some 2)
    [true, true] [true] = none := rfl

end ForkRuntime
