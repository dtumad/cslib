/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Computability.PolynomialTime.Fork
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

end ForkRuntime
