/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Crypto.RandomOracle
public import Cslib.Computability.PolynomialTime.List
public import Cslib.Computability.PolynomialTime.Option
public import Cslib.Computability.PolynomialTime.Sampling.Finite

/-!
# Polynomial-time cache operations

An ordinary association list implements the random oracle's cache. The certificates account
for lookup, key comparison, and copying the resulting state, uniformly across indexed types.
On a cache hit, an exhausted candidate sample is ignored and the existing answer is retained.
-/

public section

namespace Cslib.Crypto.RandomOracle

open PFunctor Turing.MultiTapeTM Turing.MultiTapePTM

variable {α ι : Type} {X Y : ι → Type} [∀ i, DecidableEq (X i)]
  {encode : α → Word} {parameter : α → ι}
  {key : ∀ i, X i ↪ Word} {value : ∀ i, Y i ↪ Word}
  {input : ∀ a, X (parameter a)} {cache : ∀ a, List (X (parameter a) × Y (parameter a))}

/-- A seeded cache query is polynomial time, including the returned cache. -/
theorem isPolyTime_query {fresh : ∀ a, Y (parameter a)}
    (hinput : IsPolyTime encode (fun a => key (parameter a) (input a)))
    (hcache : IsPolyTime encode
      (fun a => listEncoding (pairEncoding (key (parameter a)) (value (parameter a))) (cache a)))
    (hfresh : IsPolyTime encode (fun a => value (parameter a) (fresh a))) :
    IsPolyTime encode (fun a =>
      pairEncoding (value (parameter a))
        (listEncoding (pairEncoding (key (parameter a)) (value (parameter a))))
        (query (m := Id) (pure (fresh a)) (input a) (cache a))) := by
  have hlookup := hinput.list_lookup_indexed hcache
  have hanswer := hlookup.option_getD hfresh
  have hentry := hinput.pair (left := wordEncoding) (right := wordEncoding) hfresh
  have hcons := hentry.pair (left := wordEncoding) (right := wordEncoding) hcache
  have hstate := hlookup.option_isSome.cond hcache hcons
  have h := hanswer.pair (left := wordEncoding) (right := wordEncoding) hstate
  convert h using 1
  funext a
  cases hfind : (cache a).lookup (input a) <;> simp only [query, hfind] <;> rfl

/-- A failed candidate affects only a cache miss. Both successful branches retain the full cache. -/
theorem isPolyTime_query_option {fresh : ∀ a, Option (Y (parameter a))}
    (hinput : IsPolyTime encode (fun a => key (parameter a) (input a)))
    (hcache : IsPolyTime encode
      (fun a => listEncoding (pairEncoding (key (parameter a)) (value (parameter a))) (cache a)))
    (hfresh : IsPolyTime encode (fun a => optionEncoding (value (parameter a)) (fresh a))) :
    IsPolyTime encode (fun a =>
      optionEncoding (pairEncoding (value (parameter a))
        (listEncoding (pairEncoding (key (parameter a)) (value (parameter a)))))
        (query (fresh a) (input a) (cache a))) := by
  have hlookup := hinput.list_lookup_indexed hcache
  have hentry := hinput.pair (left := wordEncoding) (right := wordEncoding) hfresh.tail
  have hcons := hentry.pair (left := wordEncoding) (right := wordEncoding) hcache
  have hmiss := hfresh.option_isSome.cond
    (hfresh.tail.pair (left := wordEncoding) (right := wordEncoding) hcons).option_some
    (isPolyTime_const encode [])
  have hhit := (hlookup.tail.pair (left := wordEncoding) (right := wordEncoding) hcache).option_some
  have h := hlookup.option_isSome.cond hhit hmiss
  convert h using 1
  funext a
  cases hfind : (cache a).lookup (input a) <;>
    cases hf : fresh a <;> simp only [query, hfind] <;> rfl

omit [∀ i, DecidableEq (X i)] in
/-- A successful query adds at most one encoded key/value pair, including its delimiter. -/
theorem length_cache_query_option_le {X Y : Type} [DecidableEq X]
    (key : X ↪ Word) (value : Y ↪ Word) (fresh : Option Y) (input : X)
    (cache : List (X × Y)) {out : Y × List (X × Y)} {bound : ℕ}
    (hquery : query fresh input cache = some out)
    (hbound : ∀ answer ∈ fresh, (value answer).length ≤ bound) :
    (listEncoding (pairEncoding key value) out.2).length ≤
      (listEncoding (pairEncoding key value) cache).length +
        2 * (2 * (key input).length + bound + 1) + 1 := by
  cases hfind : cache.lookup input with
  | some answer =>
    have hout : (answer, cache) = out := by simpa [query, hfind] using hquery
    subst out
    dsimp only
    omega
  | none =>
    cases hfresh : fresh with
    | none => simp [query, hfind, hfresh] at hquery
    | some answer =>
      have hout : (answer, (input, answer) :: cache) = out := by
        simpa [query, hfind, hfresh] using hquery
      subst out
      have hanswer := hbound answer (by simp [hfresh])
      simp only [listEncoding_cons, length_pairEncoding]
      omega

variable {Oracle : Type} [Finite Oracle]
  [MeasurableSpace Word] [DiscreteMeasurableSpace Word]

/-- A random-oracle query with bounded binary sampling has one uniform machine certificate.
Extra private randomness on a cache hit is discarded without changing any shared oracle state. -/
theorem isPPT_query {encoding : α ↪ Word} (order : ι → ℕ) (attempts : α → ℕ)
    (scalar : ∀ i, Y i ≃ Fin (order i))
    (horder : IsPolyTime encoding (fun a => binaryEncoding (order (parameter a))))
    (hattempts : IsPolyTime encoding (fun a => unaryEncoding (attempts a)))
    (hinput : IsPolyTime encoding (fun a => key (parameter a) (input a)))
    (hcache : IsPolyTime encoding (fun a =>
      listEncoding (pairEncoding (key (parameter a)) (finEquivEncoding (scalar (parameter a))))
        (cache a))) :
    IsPPT (Oracle := Oracle) encoding wordEncoding (fun a =>
      optionEncoding (pairEncoding (finEquivEncoding (scalar (parameter a)))
        (listEncoding (pairEncoding (key (parameter a))
          (finEquivEncoding (scalar (parameter a)))))) <$>
        (query (m := OptionT (effects Oracle).FreeM)
          (OptionT.mk (Option.map (scalar (parameter a)).symm <$>
            FreeM.sampleFin ((fun b => (⟨b.toNat, Bool.toNat_lt b⟩ : Fin 2)) <$> coin)
              (order (parameter a)) (order (parameter a)).size (attempts a)))
          (input a) (cache a)).run) := by
  let sampled := sigmaEncoding encoding
    (fun a => optionEncoding (finEquivEncoding (scalar (parameter a))))
  have hs := isPolyTime_input sampled
  have hpost : IsPolyTime sampled (fun arg => optionEncoding
      (pairEncoding (finEquivEncoding (scalar (parameter arg.1)))
        (listEncoding (pairEncoding (key (parameter arg.1))
          (finEquivEncoding (scalar (parameter arg.1))))))
      (query arg.2 (input arg.1) (cache arg.1))) := by
    apply isPolyTime_query_option
      (parameter := fun arg : Σ a, Option (Y (parameter a)) => parameter arg.1)
      (key := key) (value := fun i => finEquivEncoding (scalar i))
    · exact hinput.comp_encoded (f := Sigma.fst) hs.sigma_fst
    · exact hcache.comp_encoded (f := Sigma.fst) hs.sigma_fst
    · exact hs.sigma_snd
  have hsample := isPPT_sampleFin_equiv (Oracle := Oracle) (input := encoding)
    (β := fun a => Y (parameter a)) (fun a => scalar (parameter a)) horder hattempts
  have h := hsample.map (output := wordEncoding)
    (f := fun arg => optionEncoding
      (pairEncoding (finEquivEncoding (scalar (parameter arg.1)))
        (listEncoding (pairEncoding (key (parameter arg.1))
          (finEquivEncoding (scalar (parameter arg.1))))))
      (query arg.2 (input arg.1) (cache arg.1)))
    (by simpa only [wordEncoding, Function.Embedding.refl_apply] using hpost)
  apply h.congr
  intro a S _ _ _ oracle state
  simp only [← comp_map, Function.comp_def]
  cases hfind : (cache a).lookup (input a) with
  | some answer =>
    simp only [query, hfind, OptionT.run_pure, map_pure]
    rw [map_eq_pure_bind]
    exact runKernel_sampleFin_const oracle (order (parameter a)) (order (parameter a)).size
      (attempts a) (pure (optionEncoding (pairEncoding (finEquivEncoding (scalar (parameter a)))
        (listEncoding (pairEncoding (key (parameter a)) (finEquivEncoding (scalar (parameter a))))))
          (some (answer, cache a)))) state
  | none =>
    simp only [query, hfind, ← map_eq_pure_bind, OptionT.run_map]
    simp only [OptionT.run, OptionT.mk, ← comp_map, Function.comp_def]
    rfl

end Cslib.Crypto.RandomOracle
