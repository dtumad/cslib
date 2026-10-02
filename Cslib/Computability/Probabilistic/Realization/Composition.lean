/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Clock
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.Composition
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.KeepParameter
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Machine realizations of probabilistic sequencing
When the first PPT program produces an encoded pair `(security parameter, auxiliary input)`,
its result can be passed to another PPT program. The compiler buffers that encoded word and
uses it as the continuation's input. Polynomial output length bounds the continuation's runtime.
`IsPPT.keep_parameter` certifies retaining the original security parameter beside a word-valued
result. Combining it with encoded composition gives the usual same-parameter `IsPPT.bind` rule.
The machine copies the unary parameter, buffers the intermediate word, and initializes fresh
continuation tapes; the cost of each operation is included in the polynomial bound.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.OracleTM

/-- Retain the original security parameter beside a PPT program's result. The compiler writes
the unary parameter and delimiter before running the program, with linear preparation cost. -/
theorem IsPPT.keep_parameter {program : ℕ → Word → ProbComp Word}
    (h : IsPPT wordEncoding program) :
    IsPPT parameterEncoding (fun n input => (fun word => (n, word)) <$> program n input) := by
  obtain ⟨k, states, source, c, d, hsourceHalt, hsource⟩ := h.exists_halting_machine
  have hpoly : PolynomiallyBounded (fun length => 2 * length + 3 + c * (length + 1) ^ d) :=
    (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 3)).add ⟨c, d, fun _ => le_rfl⟩
  obtain ⟨coefficient, degree, htime⟩ := hpoly
  apply isPPT_of_finite_machine source.keepParameter coefficient degree
  intro n input
  have hhalt := (hsourceHalt (parameterInput n input)).keepParameter
  have hbound : 2 * n + 3 + c * ((parameterInput n input).length + 1) ^ d ≤
      coefficient * ((parameterInput n input).length + 1) ^ degree := by
    apply le_trans _ (htime (parameterInput n input).length)
    simp only [length_parameterInput]
    omega
  refine Eq.trans ?_ (hhalt.eval_run_eq _ _ hbound).symm
  refine Eq.trans ?_
    (eval_keepParameter source _ n input _ (hsourceHalt (parameterInput n input))).symm
  simpa [ProbComp.eval_map, PMF.map_comp, parameterEncoding, wordEncoding, parameterInput,
    Function.comp_def] using
    congrArg (PMF.map (fun word => parameterInput n word)) (hsource n input)

/-- A PPT program may return the encoded parameter and input of another PPT program. -/
theorem IsPPT.bind_parameter {α : Type} {encode : α ↪ Word}
    {first : ℕ → Word → ProbComp (ℕ × Word)} {second : ℕ → Word → ProbComp α}
    (hfirst : IsPPT parameterEncoding first) (hsecond : IsPPT encode second) :
    IsPPT encode (fun n input => do
      let (nextParameter, nextInput) ← first n input
      second nextParameter nextInput) := by
  obtain ⟨k₀, states₀, source, c₀, d₀, hsourceHalt, hsource⟩ := hfirst.exists_halting_machine
  obtain ⟨k₁, states₁, target, c₁, d₁, htargetHalt, htarget⟩ := hsecond.exists_halting_machine
  let firstTime := fun length => c₀ * (length + 1) ^ d₀
  let secondTime := fun length => c₁ * (firstTime length + 1) ^ d₁
  have hpolyFirst : PolynomiallyBounded firstTime := ⟨c₀, d₀, fun _ => le_rfl⟩
  have hpolySecond : PolynomiallyBounded secondTime :=
    (show PolynomiallyBounded (fun length => c₁ * (length + 1) ^ d₁) from
      ⟨c₁, d₁, fun _ => le_rfl⟩).comp hpolyFirst
  obtain ⟨coefficient, degree, htime⟩ :=
    hpolyFirst.add ((hpolyFirst.add (PolynomiallyBounded.const 4)).add hpolySecond)
  apply isPPT_of_finite_machine (source.comp target) coefficient degree
  intro n input
  let encoded := parameterInput n input
  have hlength (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      word.length ≤ firstTime encoded.length := by
    simpa [initialConfig] using length_output_eval_runFrom_le source _ _
      (source.initialConfig encoded) word hword
  have hbound (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      c₁ * (word.length + 1) ^ d₁ ≤ secondTime encoded.length :=
    Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right (hlength word hword) 1) d₁)
  have htargetBound (word : Word)
      (hword : word ∈ (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support) :
      target.HaltsWithin (secondTime encoded.length) word :=
    (htargetHalt word).mono (hbound word hword)
  have hhalt := (hsourceHalt encoded).comp htargetBound
  rw [hhalt.eval_run_eq _ _ (htime encoded.length), eval_comp source target encoded
    (firstTime encoded.length) (secondTime encoded.length) (hsourceHalt encoded) htargetBound]
  rw [← hsource n input, PMF.bind_map]
  simp only [ProbComp.eval_bind, PMF.map_bind]
  apply PMF.bind_congr_on_support
  rintro ⟨nextParameter, nextInput⟩ hpair
  have hword : parameterInput nextParameter nextInput ∈
      (OracleComp.eval (fun _ => PMF.pure [])
        (source.run (firstTime encoded.length) encoded)).support := by
    rw [← hsource n input]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(nextParameter, nextInput), hpair, rfl⟩
  exact (htarget nextParameter nextInput).trans
    ((htargetHalt (parameterInput nextParameter nextInput)).eval_run_eq _ _
      (hbound _ hword)).symm

/-- Run a PPT word-valued program, then pass its result to another PPT program at the same
security parameter. Both programs are realized by fixed machines; all handoff costs are charged. -/
theorem IsPPT.bind {α : Type} {encode : α ↪ Word}
    {first : ℕ → Word → ProbComp Word} {second : ℕ → Word → ProbComp α}
    (hfirst : IsPPT wordEncoding first) (hsecond : IsPPT encode second) :
    IsPPT encode (fun n input => do
      let word ← first n input
      second n word) := by
  simpa only [bind_map_left] using hfirst.keep_parameter.bind_parameter hsecond

end Cslib.Probability
