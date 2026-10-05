/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.Primitives.Schnorr.Fork
public import Cslib.Crypto.Primitives.Schnorr.PolynomialTime
public import Cslib.Computability.PolynomialTime.Encoding.Decoding
import Cslib.Tactic.PolyTime

/-! # Uniform selection of Schnorr's fork point -/

public section

namespace Cslib.Crypto.Schnorr

open Turing.MultiTapeTM

variable {α : Type} {F G : ℕ → Type} [∀ n, Field (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, DecidableEq (G n)]
  {encode : α → Word} {parameter : α → ℕ}
  (element : ∀ n, G n ↪ Word) (scalar : ∀ n, Computability.Encoding (F n) Bool)
  {generator publicKey : ∀ a, G (parameter a)}
  {candidate : ∀ a, Word × G (parameter a) × F (parameter a)}
  {hashes : ∀ a, List ((Word × G (parameter a)) × F (parameter a))}

/-- Searching the fresh-hash transcript has one uniform machine, including the acceptance
test. The parameter, public key, generator, and candidate are captured by the ordinary list
search API. Its index counts fresh hashes, independently of the adversary's transitions. -/
theorem isPolyTime_findForkPoint_some
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hcandidate : IsPolyTime encode (fun a => pairEncoding wordEncoding
      (pairEncoding (element (parameter a)) (scalar (parameter a)).toEmbedding) (candidate a)))
    (hhashes : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)))
        (scalar (parameter a)).toEmbedding) (hashes a)))
    (hz : IsPolyTime unaryEncoding (fun n => (scalar n).encode 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n).toEmbedding (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding unaryEncoding
      (findForkPoint (generator a) (publicKey a) (some (candidate a)) (hashes a))) := by
  let environment := sigmaEncoding unaryEncoding (fun n => pairEncoding (element n)
    (pairEncoding (element n) (pairEncoding wordEncoding
      (pairEncoding (element n) (scalar n).toEmbedding))))
  let event n := pairEncoding (pairEncoding wordEncoding (element n)) (scalar n).toEmbedding
  let env (a : α) : Σ n, G n × G n × Word × G n × F n :=
    ⟨parameter a, generator a, publicKey a, candidate a⟩
  let predicate (ctx : Σ n, G n × G n × Word × G n × F n) (word : Word) :=
    (List.BitPair.fst word == pairEncoding wordEncoding (element ctx.1)
      (ctx.2.2.2.1, ctx.2.2.2.2.1)) &&
      decide (Accepts ctx.2.1 ctx.2.2.1 ctx.2.2.2.2.1
        (((scalar ctx.1).decode (List.BitPair.snd word)).getD 0) ctx.2.2.2.2.2)
  have henv : IsPolyTime encode (fun a => environment (env a)) :=
    hp.sigma (hg.pair (left := wordEncoding) (right := wordEncoding)
      (hpk.pair (left := wordEncoding) (right := wordEncoding) hcandidate))
  have hwords : IsPolyTime encode (fun a =>
      listEncoding wordEncoding ((hashes a).map (event (parameter a)))) := by
    simpa only [listEncoding_map (event _) wordEncoding (event _) (fun _ => rfl)] using hhashes
  have hi := isPolyTime_input (pairEncoding environment wordEncoding)
  have hn := hi.fst.sigma_fst
  have hzero := hz.comp_encoded hn
  have hchallenge := (hdecode.comp_encoded
    (f := fun pair : (Σ n, G n × G n × Word × G n × F n) × Word =>
      ⟨pair.1.1, List.BitPair.snd pair.2⟩)
    (hn.sigma hi.snd.bitPair_snd)).option_getD hzero
  have haccepts := isPolyTime_accepts (fun n => (scalar n).toEmbedding) element hsmul hadd
  have hcheck := haccepts.comp_encoded
    (encode := pairEncoding environment wordEncoding)
    (f := fun pair : (Σ n, G n × G n × Word × G n × F n) × Word =>
      ⟨pair.1.1, pair.1.2.1, pair.1.2.2.1,
      pair.1.2.2.2.2.1, ((scalar pair.1.1).decode (List.BitPair.snd pair.2)).getD 0,
      pair.1.2.2.2.2.2⟩) (by
      dsimp only [environment]
      polytime)
  have hkey : IsPolyTime (pairEncoding environment wordEncoding) (fun pair =>
      pairEncoding wordEncoding (element pair.1.1) (pair.1.2.2.2.1, pair.1.2.2.2.2.1)) := by
    dsimp only [environment]
    polytime
  have hpredicate : IsPolyTime (pairEncoding environment wordEncoding)
      (fun pair => [predicate pair.1 pair.2]) :=
    (hi.snd.bitPair_fst.beq hkey).bool₂ hcheck Bool.and
  have hfind := hwords.list_findIdx?_with henv hpredicate
  convert hfind using 1
  funext a
  congr 1
  simp only [findForkPoint, List.findIdx?_map, Function.comp_def]
  congr 1
  funext value
  rcases value with ⟨⟨message, commitment⟩, challenge⟩
  simp only [predicate, env, event, pairEncoding_apply, List.BitPair.fst_encode,
    List.BitPair.snd_encode, Computability.Encoding.toEmbedding_apply,
    Computability.Encoding.decode_encode, Option.getD_some, Bool.beq_eq_decide_eq,
    Bool.decide_and, List.BitPair.encode_inj, (element (parameter a)).injective.eq_iff,
    wordEncoding, Function.Embedding.refl_apply, Prod.mk.injEq]

/-- Optional checked output selects no fork when the first run failed. The fallback candidate
is used only inside the machine certificate; it cannot turn failure into a selected query. -/
theorem isPolyTime_findForkPoint
    {candidate : ∀ a, Option (Word × G (parameter a) × F (parameter a))}
    (hp : IsPolyTime encode (fun a => unaryEncoding (parameter a)))
    (hg : IsPolyTime encode (fun a => element (parameter a) (generator a)))
    (hpk : IsPolyTime encode (fun a => element (parameter a) (publicKey a)))
    (hcandidate : IsPolyTime encode (fun a => optionEncoding (pairEncoding wordEncoding
      (pairEncoding (element (parameter a)) (scalar (parameter a)).toEmbedding)) (candidate a)))
    (hhashes : IsPolyTime encode (fun a => listEncoding
      (pairEncoding (pairEncoding wordEncoding (element (parameter a)))
        (scalar (parameter a)).toEmbedding) (hashes a)))
    (hz : IsPolyTime unaryEncoding (fun n => (scalar n).encode 0))
    (hdecode : IsPolyTime (sigmaEncoding unaryEncoding (fun _ => wordEncoding))
      (fun arg => optionEncoding (scalar arg.1).toEmbedding ((scalar arg.1).decode arg.2)))
    (hsmul : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (scalar n).toEmbedding (element n)))
      (fun arg => element arg.1 (arg.2.1 • arg.2.2)))
    (hadd : IsPolyTime (sigmaEncoding unaryEncoding
      (fun n => pairEncoding (element n) (element n)))
      (fun arg => element arg.1 (arg.2.1 + arg.2.2))) :
    IsPolyTime encode (fun a => optionEncoding unaryEncoding
      (findForkPoint (generator a) (publicKey a) (candidate a) (hashes a))) := by
  have hread := hcandidate.option_getD (fallback := fun a => ([], generator a, 0))
    ((isPolyTime_const encode []).pair (left := wordEncoding) (right := wordEncoding)
      (hg.pair (left := wordEncoding) (right := wordEncoding) (hz.comp_encoded hp)))
  have hfind := isPolyTime_findForkPoint_some element scalar hp hg hpk hread hhashes
    hz hdecode hsmul hadd
  convert hcandidate.option_isSome.cond hfind (isPolyTime_const encode []) using 1
  funext a
  cases candidate a <;> rfl

end Cslib.Crypto.Schnorr
