/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GoldreichLevin.Parameters
public import Cslib.Tactic.PolyTime

/-!
# Word algorithms for Goldreich-Levin decoding

The finite decoder's operations are realized by ordinary word and collection combinators.
This module keeps algorithm certificates separate from the probabilistic game correspondence.
Unary arithmetic computes the logarithmic mask count at every fixed precision degree. Guess
enumeration charges for the full encoded output and has a polynomial-time certificate at those
parameters. Candidate generation and first-match checking use maps, folds, filtering, and captured
callbacks. Their results agree exactly with the finite decoder, including enumeration order and
duplicate candidates. `WordReduction` combines these deterministic certificates with sampling
to obtain a uniform PPT inverter.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability

/-- View a word as `n` coordinates, using false for missing bits. Valid lengths lose no data. -/
def wordBits (n : ℕ) (word : Word) : BitString n := fun i => word[i.val]?.getD false

/-- A finite bitstring survives the word representation unchanged. -/
@[simp] theorem wordBits_ofFn {n : ℕ} (bits : BitString n) :
    wordBits n (List.ofFn bits) = bits := by
  funext i
  simp [wordBits]

/-- A correctly sized word survives the finite-coordinate representation unchanged. -/
theorem ofFn_wordBits {n : ℕ} {word : Word} (hlen : word.length = n) :
    List.ofFn (wordBits n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits, List.getElem?_eq_getElem hi']

/-- The row-major bijection between a flat bitstring and a matrix of masks. -/
def maskEquiv (k n : ℕ) : BitString (k * n) ≃ (Fin k → BitString n) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin k) (Fin n) Bool)

/-- Interpret a flat sampled word as the decoder's base masks. -/
def masksFromWord (k n : ℕ) (word : Word) : Fin k → BitString n :=
  maskEquiv k n (wordBits (k * n) word)

/-- Read one row of the sampled mask tape, padding missing bits with false. -/
def maskRow (dimension row : ℕ) (word : Word) : Word :=
  (List.range dimension).map (fun column => word[row * dimension + column]?.getD false)

/-- A row reader captures the dimension and mask tape while accepting the row index. -/
theorem maskRow_isPolyTime : IsPolyTime
    (pairEncoding (pairEncoding unaryEncoding wordEncoding) unaryEncoding)
    (fun input => maskRow input.1.1 input.2 input.1.2) := by
  unfold maskRow
  polytime

/-- Read the mask tape as an ordinary list of rows, padding missing bits with false. -/
def maskRows (count dimension : ℕ) (word : Word) : List Word :=
  (List.range count).map (fun row => maskRow dimension row word)

/-- Matrix parsing charges for the dimension, every runtime index, and the complete output. -/
theorem maskRows_isPolyTime : IsPolyTime
    (pairEncoding (pairEncoding unaryEncoding unaryEncoding) wordEncoding)
    (fun input => listEncoding wordEncoding (maskRows input.1.1 input.1.2 input.2)) := by
  have hparameters := isPolyTime_fst (pairEncoding unaryEncoding unaryEncoding) wordEncoding
  exact hparameters.fst.range.list_map_with
    (environment := pairEncoding unaryEncoding wordEncoding) (output := wordEncoding)
    (f := fun env row => maskRow env.1 row env.2)
    (hparameters.snd.pair (left := unaryEncoding) (right := wordEncoding)
      (isPolyTime_snd (pairEncoding unaryEncoding unaryEncoding) wordEncoding)) maskRow_isPolyTime

/-- The nested-list program is exactly the finite matrix interpretation, also on short tapes. -/
theorem maskRows_eq_ofFn (count dimension : ℕ) (word : Word) :
    maskRows count dimension word =
      List.ofFn (fun row => List.ofFn (masksFromWord count dimension word row)) := by
  apply List.ext_getElem (by simp [maskRows])
  intro row hleft hright
  apply List.ext_getElem (by simp [maskRows, maskRow])
  intro column hleft' hright'
  simp [maskRows, maskRow, masksFromWord, maskEquiv, wordBits, Nat.mul_comm, Nat.add_comm]

/-- A fixed inverse-polynomial precision can be computed from an efficient unary parameter. -/
theorem precision_isPolyTime {α : Type} {encode : α → Word} {parameter : α → ℕ}
    (hparameter : IsPolyTime encode (fun a => List.replicate (parameter a) true)) (degree : ℕ) :
    IsPolyTime encode (fun a => List.replicate (precision degree (parameter a)) true) := by
  unfold precision
  polytime

/-- Computing the logarithmic mask count charges for the dimension and precision arithmetic. -/
theorem maskCount_isPolyTime {α : Type} {encode : α → Word} {dimension precision : α → ℕ}
    (hdimension : IsPolyTime encode (fun a => List.replicate (dimension a) true))
    (hprecision : IsPolyTime encode (fun a => List.replicate (precision a) true)) :
    IsPolyTime encode (fun a => List.replicate (maskCount (dimension a) (precision a)) true) := by
  unfold maskCount
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] precision_isPolyTime maskCount_isPolyTime

/-- Strict majority of a word of votes, choosing false on a tie. -/
def wordMajority (votes : Word) : Bool := decide (votes.length < 2 * (votes.filter id).length)

/-- The decoder's majority operation uses ordinary filtering, counting, and comparison. -/
theorem wordMajority_isPolyTime : IsPolyTime wordEncoding (fun votes => [wordMajority votes]) := by
  unfold wordMajority
  polytime

/-- Listing each voting index once gives exactly the finite decoder's majority. -/
theorem wordMajority_map {ι : Type} [DecidableEq ι] (indices : List ι) (hnodup : indices.Nodup)
    (vote : ι → Bool) : wordMajority (indices.map vote) = majority indices.toFinset vote := by
  rw [wordMajority, majority, ← List.toFinset_filter, List.toFinset_card_of_nodup hnodup,
    List.toFinset_card_of_nodup (hnodup.filter vote)]
  simp [List.filter_map]

/-- A coordinate mask, with all zeros when the index is outside the requested dimension. -/
def coordinateWord (dimension index : ℕ) : Word :=
  (List.range dimension).map (fun coordinate => decide (index = coordinate))

/-- Coordinate masks are ordinary maps over an efficiently generated interval. -/
theorem coordinateWord_isPolyTime : IsPolyTime (pairEncoding unaryEncoding unaryEncoding)
    (fun pair => coordinateWord pair.1 pair.2) := by
  unfold coordinateWord
  polytime

/-- The coordinate-mask program agrees with the basis vector used by the finite decoder. -/
theorem coordinateWord_eq_ofFn_single {n : ℕ} (index : Fin n) :
    coordinateWord n index = List.ofFn (Pi.single index true) := by
  apply List.ext_getElem (by simp [coordinateWord])
  intro coordinate hleft hright
  simp [coordinateWord, Pi.single_apply, Fin.ext_iff, Bool.zero_eq_false, eq_comm]

/-- All coordinate queries in their ordinary increasing order. -/
def coordinateWords (dimension : ℕ) : List Word :=
  (List.range dimension).map (coordinateWord dimension)

/-- Generating every coordinate mask includes the quadratic output size in its certificate. -/
theorem coordinateWords_isPolyTime : IsPolyTime unaryEncoding
    (fun dimension => listEncoding wordEncoding (coordinateWords dimension)) :=
  (isPolyTime_input unaryEncoding).range.list_map_with
    (isPolyTime_input unaryEncoding) coordinateWord_isPolyTime

/-- The generated coordinate queries have exactly the finite decoder's order. -/
theorem coordinateWords_eq_ofFn (dimension : ℕ) :
    coordinateWords dimension =
      List.ofFn (fun index : Fin dimension => List.ofFn (Pi.single index true)) := by
  apply List.ext_getElem (by simp [coordinateWords])
  intro index hleft hright
  simpa [coordinateWords] using
    coordinateWord_eq_ofFn_single (⟨index, by simpa using hright⟩ : Fin dimension)

/-- Adding finite masks is exactly coordinatewise XOR of their word representations. -/
theorem ofFn_add {n : ℕ} (left right : BitString n) :
    List.ofFn (left + right) = (List.ofFn left).zipWith Bool.xor (List.ofFn right) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getElem_zipWith, Bool.add_eq_xor]

/-- Mask addition in the decoder is uniformly efficient, including when the dimension varies
with the input. Its certificate uses the ordinary `zipWith` combinator. -/
theorem addMasks_isPolyTime {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => List.ofFn (left a + right a)) := by
  simpa only [ofFn_add] using hleft.zipWith hright Bool.xor

/-- XOR the rows selected by a word of bits. Missing selector bits are false. The accumulator
starts at the requested dimension; rows of that dimension preserve its length. -/
def xorSelected (dimension : ℕ) (selector : Word) (rows : List Word) : Word :=
  (rows.foldl (fun state row =>
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2))
    (selector, List.replicate dimension false)).2

/-- Subset-mask formation is a fold with a shrinking accumulator and an ordinary conditional. -/
theorem xorSelected_isPolyTime : IsPolyTime
    (pairEncoding unaryEncoding (pairEncoding wordEncoding (listEncoding wordEncoding)))
    (fun input => xorSelected input.1 input.2.1 input.2.2) := by
  let advance (state : Word × Word) (row : Word) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hstep : IsPolyTime (pairEncoding coinInputEncoding wordEncoding)
      (fun pair => coinInputEncoding (advance pair.1 pair.2)) := by
    unfold advance
    polytime
  have hdata := isPolyTime_snd unaryEncoding
    (pairEncoding wordEncoding (listEncoding wordEncoding))
  have hdimension := isPolyTime_fst unaryEncoding
    (pairEncoding wordEncoding (listEncoding wordEncoding))
  have hfold := hdata.snd.list_foldl_of_growth (stateEncoding := coinInputEncoding)
    (step := advance)
    (hdata.fst.pair (left := wordEncoding) (right := wordEncoding) (hdimension.replicate false))
    hstep (growth := fun _ => 0) (by fun_prop) (by
      rintro ⟨selector, value⟩ row
      simp only [coinInputEncoding, advance, length_pairEncoding, wordEncoding,
        Function.Embedding.refl_apply, List.length_tail]
      split
      · rw [List.length_zipWith]; lia
      · lia)
  exact IsPolyTime.snd (left := wordEncoding) (right := wordEncoding) hfold

/-- On finite masks, the selector fold is exactly the sum of the selected rows. -/
theorem xorSelected_eq_ofFn_sum {n k : ℕ} (selector : BitString k)
    (masks : Fin k → BitString n) :
    xorSelected n (List.ofFn selector) (List.ofFn (fun i => List.ofFn (masks i))) =
      List.ofFn (∑ i, if selector i then masks i else 0) := by
  let advance (state : Word × Word) (row : Word) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hfold (count : ℕ) (selector : BitString count) (masks : Fin count → BitString n)
      (value : BitString n) :
      (List.ofFn (fun i => List.ofFn (masks i))).foldl advance
          (List.ofFn selector, List.ofFn value) =
        ([], List.ofFn (value + ∑ i, if selector i then masks i else 0)) := by
    induction count generalizing value with
    | zero => simp
    | succ count ih =>
      cases h : selector 0 <;>
        simpa [List.ofFn_succ, advance, h, ← ofFn_add, Fin.sum_univ_succ, add_assoc] using
          ih (fun i => selector i.succ) (fun i => masks i.succ)
            (value + if selector 0 then masks 0 else 0)
  have hzero : List.ofFn (0 : BitString n) = List.replicate n false := by
    change List.ofFn (fun _ : Fin n => false) = _
    simp
  simpa [xorSelected, advance, hzero] using
    congrArg Prod.snd (hfold k selector masks 0)

/-- Selecting the characteristic word of a finite subset computes its mask sum. -/
theorem xorSelected_eq_ofFn_sum_subset {n k : ℕ} (indices : Finset (Fin k))
    (masks : Fin k → BitString n) :
    xorSelected n (List.ofFn (fun i => decide (i ∈ indices)))
        (List.ofFn (fun i => List.ofFn (masks i))) = List.ofFn (∑ i ∈ indices, masks i) := by
  simpa using xorSelected_eq_ofFn_sum (fun i => decide (i ∈ indices)) masks

/-- A Boolean dot product is a pointwise AND followed by a parity fold on words. -/
theorem dotProduct_eq_foldl {n : ℕ} (left right : BitString n) :
    left ⬝ᵥ right = ((List.ofFn left).zipWith Bool.and (List.ofFn right)).foldl Bool.xor false := by
  have hzip : (List.ofFn left).zipWith Bool.and (List.ofFn right) =
      List.ofFn (fun i => left i * right i) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getElem_zipWith, Bool.mul_eq_and]
  rw [hzip, dotProduct, ← List.sum_ofFn]
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

/-- The hard-core bit computation is uniformly efficient through word combinators. -/
theorem dotProduct_isPolyTime {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => [left a ⬝ᵥ right a]) := by
  simpa only [dotProduct_eq_foldl] using
    (hleft.zipWith hright Bool.and).foldl_bool Bool.xor false

/-- The finite decoder's ordered guesses, represented as ordinary words. -/
def guessWords (count : ℕ) : List Word := (allGuesses count).map List.ofFn

/-- The selectors for nonempty subsets of the base masks. -/
def nonzeroGuessWords (count : ℕ) : List Word :=
  (guessWords count).filter (fun word => word.any id)

/-- Removing the zero selector uses an ordinary certified collection predicate. -/
theorem nonzeroGuessWords_isPolyTime {α : Type} {encode : α → Word} {count : α → ℕ}
    (hguesses : IsPolyTime encode (fun a => listEncoding wordEncoding (guessWords (count a)))) :
    IsPolyTime encode (fun a => listEncoding wordEncoding (nonzeroGuessWords (count a))) :=
  hguesses.list_filter ((isPolyTime_input wordEncoding).any id)

private def selectorEquiv (count : ℕ) : BitString count ≃ Finset (Fin count) where
  toFun guess := Finset.univ.filter (fun i => guess i)
  invFun subset i := decide (i ∈ subset)
  left_inv guess := by funext i; simp
  right_inv subset := by ext; simp

/-- The word selectors enumerate exactly the finite decoder's voting subsets, once each. -/
theorem wordMajority_nonzeroGuessWords (count : ℕ) (vote : Word → Bool) :
    wordMajority ((nonzeroGuessWords count).map vote) =
      majority (nonemptySubsets count) (fun s => vote (List.ofFn (fun i => decide (i ∈ s)))) := by
  let indices := ((allGuesses count).map (selectorEquiv count)).filter (fun s => decide s.Nonempty)
  have hnodup : indices.Nodup :=
    ((nodup_allGuesses count).map (selectorEquiv count).injective).filter _
  have hall : ∀ s, s ∈ (allGuesses count).map (selectorEquiv count) := by
    intro s
    exact List.mem_map.mpr ⟨(selectorEquiv count).symm s, mem_allGuesses _ _, by simp⟩
  have hset : indices.toFinset = nonemptySubsets count := by
    ext s
    simp [indices, hall]
  have heq : nonzeroGuessWords count =
      indices.map (fun s => List.ofFn (fun i => decide (i ∈ s))) := by
    simp only [nonzeroGuessWords, guessWords, indices, List.filter_map, List.map_map,
      Function.comp_def, selectorEquiv, Equiv.coe_fn_mk, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.decide_coe]
    congr 2
    funext guess
    apply Bool.eq_iff_iff.mpr
    simp [Finset.Nonempty]
  rw [heq, List.map_map, wordMajority_map _ hnodup, hset]
  rfl

@[simp] theorem guessWords_zero : guessWords 0 = [[]] := rfl

/-- Extending every guess by both bits preserves the finite decoder's enumeration order. -/
theorem guessWords_succ (count : ℕ) :
    guessWords (count + 1) =
      (guessWords count).flatMap (fun word => [false :: word, true :: word]) := by
  simp [guessWords, allGuesses, List.map_flatMap, List.flatMap_map]

/-- The collection encoding charges for every bit of every guess and every delimiter. -/
theorem length_guessWords_encoding (count : ℕ) :
    (listEncoding wordEncoding (guessWords count)).length = 2 ^ count * (2 * count + 1) := by
  simp [guessWords, wordEncoding, List.map_map, Function.comp_def]

/-- Enumerate the guesses using an efficient count and a polynomial bound on their total size.
This does not assert that enumeration is polynomial in the number of guessed bits. -/
theorem guessWords_isPolyTime {α : Type} {encode : α → Word} {count : α → ℕ}
    (hcount : IsPolyTime encode (fun a => List.replicate (count a) true))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ count a * (2 * count a + 1) ≤ size (encode a).length) :
    IsPolyTime encode (fun a => listEncoding wordEncoding (guessWords (count a))) := by
  let extend (values : List Word) := values.flatMap (fun word => [false :: word, true :: word])
  have hstep : IsPolyTime (listEncoding wordEncoding)
      (fun values => listEncoding wordEncoding (extend values)) := by
    unfold extend
    polytime
  have hiterate (n : ℕ) : extend^[n] [[]] = guessWords n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, guessWords_succ]
  have h := (isPolyTime_const encode (listEncoding wordEncoding [[]])).iterate_encoded
    (stateEncoding := listEncoding wordEncoding) (initial := fun _ => [[]]) (step := extend)
    hcount hstep hsize (by
      intro a index hi
      rw [hiterate, length_guessWords_encoding]
      exact (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) hi)
        (by lia : 2 * index + 1 ≤ 2 * count a + 1)).trans (hbudget a))
  simpa only [hiterate] using h

/-- The logarithmic mask choice keeps the complete encoded guess list polynomially sized. -/
theorem guessWords_size_polynomial (degree : ℕ) :
    PolynomiallyBounded (fun n =>
      (listEncoding wordEncoding (guessWords (maskCount n (precision degree n)))).length) := by
  simp only [length_guessWords_encoding]
  have := guessCount_polynomial degree
  have := maskCount_polynomial degree
  fun_prop

/-- Enumerate all guesses at a fixed precision degree, including computing the mask count.
The caller only supplies the ordinary efficiency certificate for its security parameter. -/
theorem guessWords_maskCount_isPolyTime {α : Type} {encode : α → Word} {parameter : α → ℕ}
    (hparameter : IsPolyTime encode (fun a => List.replicate (parameter a) true)) (degree : ℕ) :
    IsPolyTime encode (fun a => listEncoding wordEncoding
      (guessWords (maskCount (parameter a) (precision degree (parameter a))))) := by
  have h : IsPolyTime unaryEncoding (fun n => listEncoding wordEncoding
      (guessWords (maskCount n (precision degree n)))) := by
    refine guessWords_isPolyTime (by polytime) (guessWords_size_polynomial degree) ?_
    intro n
    simp only [unaryEncoding_apply, List.length_replicate, length_guessWords_encoding, le_refl]
  exact h.comp_encoded (encodeArg := unaryEncoding) hparameter

/-- Decode one parity guess by mapping a corrected majority vote over the coordinates. -/
def wordCandidate (predictor : Word → Bool) (dimension : ℕ) (rows selectors : List Word)
    (guess : Word) : Word :=
  (coordinateWords dimension).map (fun coordinate => wordMajority (selectors.map (fun selector =>
    predictor (coordinate.zipWith Bool.xor (xorSelected dimension selector rows)) ^^
      (guess.zipWith Bool.and selector).foldl Bool.xor false)))

/-- Candidate decoding composes nested maps, a captured predictor, mask folds, and majority. -/
theorem wordCandidate_isPolyTime {α Environment : Type} {encode : α ↪ Word}
    {environment : Environment ↪ Word} {env : α → Environment}
    {predictor : Environment → Word → Bool} {dimension : α → ℕ}
    {rows selectors : α → List Word} {guess : α → Word}
    (hpredictor : IsPolyTime (pairEncoding environment wordEncoding)
      (fun pair => [predictor pair.1 pair.2]))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hdimension : IsPolyTime encode (fun a => List.replicate (dimension a) true))
    (hrows : IsPolyTime encode (fun a => listEncoding wordEncoding (rows a)))
    (hselectors : IsPolyTime encode (fun a => listEncoding wordEncoding (selectors a)))
    (hguess : IsPolyTime encode guess) :
    IsPolyTime encode (fun a => wordCandidate (predictor (env a)) (dimension a)
      (rows a) (selectors a) (guess a)) := by
  have hcoordinates := coordinateWords_isPolyTime.comp_encoded
    (encodeArg := unaryEncoding) hdimension
  have hxor := xorSelected_isPolyTime
  have hmajority := wordMajority_isPolyTime
  unfold wordCandidate
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] wordCandidate_isPolyTime

/-- The word program computes exactly the finite decoder's candidate for the same guess. -/
theorem wordCandidate_eq_ofFn {n k : ℕ} (predictor : Word → Bool)
    (masks : Fin k → BitString n) (guess : BitString k) :
    wordCandidate predictor n (List.ofFn (fun i => List.ofFn (masks i)))
        (nonzeroGuessWords k) (List.ofFn guess) =
      List.ofFn (candidate (fun query => predictor (List.ofFn query)) masks guess) := by
  simp only [wordCandidate, coordinateWords_eq_ofFn, List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  rw [wordMajority_nonzeroGuessWords]
  unfold candidate
  congr 1
  funext subset
  simp only [xorSelected_eq_ofFn_sum_subset, ← ofFn_add, ← dotProduct_eq_foldl, vote,
    Bool.add_eq_xor, Bool.one_eq_true]
  congr 1
  have h (j : Fin k) : guess j * decide (j ∈ subset) = if j ∈ subset then guess j else 0 := by
    by_cases hj : j ∈ subset <;> simp [hj, Bool.mul_eq_and, Bool.zero_eq_false]
  simp only [dotProduct, h, Finset.sum_ite_mem, Finset.univ_inter]

/-- Generate a candidate for every guess, reusing the nonzero selectors across candidates. -/
def wordCandidates (predictor : Word → Bool) (dimension : ℕ)
    (rows guesses : List Word) : List Word :=
  guesses.map (wordCandidate predictor dimension rows (guesses.filter (fun word => word.any id)))

/-- Candidate generation needs only the predictor and the efficiently prepared data. The guess
collection's certificate already accounts for the number and size of candidates. -/
theorem wordCandidates_isPolyTime {α Environment : Type} {encode : α ↪ Word}
    {environment : Environment ↪ Word} {env : α → Environment}
    {predictor : Environment → Word → Bool} {dimension : α → ℕ}
    {rows guesses : α → List Word}
    (hpredictor : IsPolyTime (pairEncoding environment wordEncoding)
      (fun pair => [predictor pair.1 pair.2]))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hdimension : IsPolyTime encode (fun a => List.replicate (dimension a) true))
    (hrows : IsPolyTime encode (fun a => listEncoding wordEncoding (rows a)))
    (hguesses : IsPolyTime encode (fun a => listEncoding wordEncoding (guesses a))) :
    IsPolyTime encode (fun a => listEncoding wordEncoding
      (wordCandidates (predictor (env a)) (dimension a) (rows a) (guesses a))) := by
  unfold wordCandidates
  polytime

/-- Candidate generation preserves the finite decoder's order and duplicates. -/
theorem wordCandidates_eq_map {n k : ℕ} (predictor : Word → Bool) (masks : Fin k → BitString n) :
    wordCandidates predictor n (List.ofFn (fun i => List.ofFn (masks i))) (guessWords k) =
      (candidateList (fun query => predictor (List.ofFn query)) masks).map List.ofFn := by
  rw [wordCandidates, ← nonzeroGuessWords]
  simp only [guessWords, candidateList, List.map_map, Function.comp_def, wordCandidate_eq_ofFn]

/-- Return the first candidate with the requested image, defaulting to a zero word of its length. -/
def wordCheckCandidates (f : Word → Word) (image : Word) (candidates : List Word) : Word :=
  (candidates.find? (fun candidate => f candidate == image)).getD
    (List.replicate image.length false)

/-- Candidate checking composes the supplied function, word equality, and collection search. -/
theorem wordCheckCandidates_isPolyTime {α : Type} {encode : α ↪ Word} {f : Word → Word}
    {image : α → Word} {candidates : α → List Word}
    (hf : IsPolyTime wordEncoding f) (himage : IsPolyTime encode image)
    (hcandidates : IsPolyTime encode (fun a => listEncoding wordEncoding (candidates a))) :
    IsPolyTime encode (fun a => wordCheckCandidates f (image a) (candidates a)) := by
  unfold wordCheckCandidates
  exact hcandidates.list_findD_with (environment := wordEncoding) (element := wordEncoding)
    (predicate := fun image candidate => f candidate == image) himage
    (by polytime) (himage.unaryLength.replicate false)

/-- Searching the word representation preserves the finite decoder's first-match behavior. -/
theorem wordCheckCandidates_eq_ofFn {n : ℕ} (f : Word → Word)
    (finiteFunction : BitString n → BitString n)
    (hf : ∀ bits, f (List.ofFn bits) = List.ofFn (finiteFunction bits))
    (image : BitString n) (candidates : List (BitString n)) :
    wordCheckCandidates f (List.ofFn image) (candidates.map List.ofFn) =
      List.ofFn (checkCandidates finiteFunction image candidates) := by
  have hzero : List.ofFn (0 : BitString n) = List.replicate n false := by
    change List.ofFn (fun _ : Fin n => false) = _
    simp
  simp only [wordCheckCandidates, checkCandidates, List.find?_map, List.length_ofFn, hf,
    beq_eq_decide, List.ofFn_inj, ← hzero, Option.getD_map, Function.comp_def]

end Cslib.Crypto.GoldreichLevin
