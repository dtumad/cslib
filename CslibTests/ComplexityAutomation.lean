/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Tactic.PPT
import Cslib.Crypto.Primitives.Schnorr
import Cslib.Foundations.Data.PFunctor.Free.WP
import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.WP
import Std.WP.Triple
import Std.Tactic.Do

/-! Automation produces uniform machine certificates for the same native programs used in
semantic proofs. Unknown algorithms still require certificates. -/

open Turing.MultiTapeTM Turing.MultiTapePTM PFunctor Cslib.Crypto

namespace ComplexityAutomation

local instance : MeasurableSpace Word := ⊤

example : IsPolyTime wordEncoding (fun word => word.reverse ++ word) := by polytime

example : IsPPT (Oracle := Empty) wordEncoding boolEncoding (fun _ => coin) := by ppt

example : IsPolyTime (pairEncoding wordEncoding (listEncoding wordEncoding))
    (fun pair => pairEncoding wordEncoding (listEncoding wordEncoding)
      (pair.1, pair.1 :: pair.2)) := by polytime

-- Sampling lengths depend on the input; the final result retains both samples and that input.
example : IsPPT (Oracle := Empty) parameterEncoding wordEncoding (fun input => do
    let first ← (List.replicate input.1 ()).mapM (fun _ => coin)
    let second ← (List.replicate first.length ()).mapM (fun _ => coin)
    pure (input.2 ++ first ++ second.reverse)) := by ppt

-- Calls reuse local certificates, including tuple preparation and captured inputs.
example (program : Word → (effects Empty).FreeM Word)
    (hprogram : IsPPT wordEncoding wordEncoding program) :
    IsPPT wordEncoding wordEncoding (fun input => do
      let result ← program (input.reverse ++ input)
      pure (result.reverse ++ input)) := by ppt

-- The ordinary Schnorr key generator needs just the sampler and group primitive certificates.
example {Oracle F G : Type} [Finite Oracle] [Field F] [AddCommGroup G] [Module F G]
    (group : G ↪ Word) (scalar : F ↪ Word) (sample : G → (effects Oracle).FreeM F)
    (hsample : IsPPT group scalar sample)
    (hsmul : IsPolyTime (pairEncoding group scalar) (fun pair => group (pair.2 • pair.1))) :
    IsPPT group (pairEncoding group scalar) (fun g => Schnorr.keygen (sample g) g) := by
  unfold Schnorr.keygen
  ppt

example {F : Type} [Field F] (scalar : F ↪ Word)
    (hadd : IsPolyTime (pairEncoding scalar scalar)
      (fun pair => scalar (pair.1 + pair.2)))
    (hmul : IsPolyTime (pairEncoding scalar scalar)
      (fun pair => scalar (pair.1 * pair.2))) :
    IsPolyTime (pairEncoding scalar (pairEncoding scalar scalar))
      (fun input => scalar (Schnorr.respond input.1 input.2.1 input.2.2)) := by
  unfold Schnorr.respond
  polytime

-- Both the type and its representation vary with the security parameter. Calls must retain
-- that dependency while assembling the arguments to the two certified field operations.
example {F : ℕ → Type} [∀ n, Field (F n)] (scalar : ∀ n, F n ↪ Word)
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (scalar n)))
      (fun arg => scalar arg.1 (arg.2.1 + arg.2.2)))
    (hmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (scalar n)))
      (fun arg => scalar arg.1 (arg.2.1 * arg.2.2))) :
    IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (pairEncoding (scalar n) (scalar n))))
      (fun arg => scalar arg.1 (Schnorr.respond arg.2.1 arg.2.2.1 arg.2.2.2)) := by
  unfold Schnorr.respond
  polytime

example {F : ℕ → Type} (scalar : ∀ n, F n ↪ Word) :
    IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n) (listEncoding (scalar n))))
      (fun arg => sigmaEncoding unaryEncoding (fun n => listEncoding (scalar n))
        ⟨arg.1, arg.2.1 :: arg.2.2⟩) := by
  polytime

-- A dependent tuple may contain a conditional under an abstract encoding. Constructing the
-- tuple must not force its field types to be constant across the parameter family.
example {F : ℕ → Type} (scalar : ∀ n, F n ↪ Word) :
    IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding boolEncoding (pairEncoding (scalar n) (scalar n))))
      (fun arg => pairEncoding (scalar arg.1) (scalar arg.1)
        ((if arg.2.1 then arg.2.2.1 else arg.2.2.2), arg.2.2.2)) := by
  polytime

section Structural

open Std.WP

set_option experimental.vcgen true

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

abbrev scalarEffects (F : Type) : PFunctor := ⟨Unit, fun _ => F⟩

local instance : WPMonad (scalarEffects F).FreeM Prop EStack⟨⟩ :=
  FreeM.forallWP (fun _ => Set.univ)

-- The same native Schnorr program supports structural WP reasoning. `vcgen` handles both
-- samples and the monadic plumbing; the remaining obligation is the scheme's algebraic law.
example (g : G) (secret : F) :
    ⦃True⦄ Schnorr.realTranscript (FreeM.lift (P := scalarEffects F) ()) g secret
      ⦃fun transcript => Schnorr.Accepts g (secret • g) transcript.1
        transcript.2.1 transcript.2.2⦄ := by
  vcgen [Schnorr.realTranscript]
  exact Schnorr.accepts_respond g secret _ _

end Structural

section MachineCorrectness

open Std.WP

set_option experimental.vcgen true

variable {Oracle : Type}

local instance : WPMonad (effects Oracle).FreeM Prop EStack⟨⟩ := FreeM.forallWP (fun _ => Set.univ)

example (oracle : Oracle) (request : Word) :
    ⦃True⦄ (fun answer => request ++ answer) <$> query oracle request
      ⦃fun result => request <+: result⦄ := by
  vcgen
  exact List.prefix_append _ _

-- Structural correctness proved on the native program transfers to every completed path of
-- a realizing machine. No second implementation of Schnorr, or efficient output decoder, is used.
example {F G State Ports : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq Ports]
    {k : ℕ} (machine : Turing.MultiTapePTM k Bool State Ports) (dispatch : Ports → Oracle)
    (fuel : ℕ) (input word : Word) (encode : (G × F × F) ↪ Word) (g : G) (secret : F)
    (hrealizes : machine.Realizes dispatch fuel input encode
      (Schnorr.realTranscript ((fun bit => if bit then (1 : F) else 0) <$> coin) g secret))
    (hword : MonadAttach.CanReturn (machine.run fuel input) (some word)) :
    ∃ transcript, encode transcript = word ∧
      Schnorr.Accepts g (secret • g) transcript.1 transcript.2.1 transcript.2.2 := by
  have hspec : ⦃True⦄
      Schnorr.realTranscript ((fun bit => if bit then (1 : F) else 0) <$>
        coin (Oracle := Oracle)) g secret
        ⦃fun transcript => Schnorr.Accepts g (secret • g) transcript.1
          transcript.2.1 transcript.2.2⦄ := by
    vcgen [Schnorr.realTranscript]
    exact Schnorr.accepts_respond g secret _ _
  obtain ⟨transcript, htranscript, hencode⟩ := hrealizes.canReturn hword
  exact ⟨transcript, hencode, (FreeM.forallWP_univ_iff _ _).mp (hspec.le_wp trivial) _ htranscript⟩

end MachineCorrectness

-- No unit-cost assumption for an arbitrary Lean function, or arbitrary effectful subprogram.
example (f : Word → Word) (hf : IsPolyTime wordEncoding f) :
    IsPolyTime wordEncoding (fun input => f input.reverse) := by
  fail_if_success (clear hf; polytime)
  polytime

example (program : Word → (effects Empty).FreeM Word)
    (hprogram : IsPPT wordEncoding wordEncoding program) :
    IsPPT wordEncoding wordEncoding (fun input => program input.reverse) := by
  fail_if_success (clear hprogram; ppt)
  ppt

end ComplexityAutomation
