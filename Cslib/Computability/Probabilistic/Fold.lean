/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Encoding

/-!
# Polynomial-time folds with encoded accumulators

`IsPolyTime.list_foldl` certifies ordinary `List.foldl` over encoded elements and accumulators.
The prefix invariant in `IsPolyTime.list_foldl_spec` connects correctness and intermediate sizes.
Polynomial growth per element gives a reusable sufficient condition; `list_map` and `list_flatMap`
derive their size bounds from the supplied function's efficiency certificate.
Their `_with` variants capture an efficiently computed runtime environment, including its copying
cost. Nested callbacks use the same contracts.

`IsPolyTime.foldl_encoded` and `IsPolyTime.foldl_spec` specialize the general rules to words.
`IsPolyTime.foldl_of_bounded_growth` handles fixed growth per bit. Both word and collection
operations share the same fold implementation.

The proof reuses the bounded-loop compiler. There is no separate fold machine, and clients
do not reason about the loop's representation or execution.
-/

@[expose] public section

namespace Cslib.Probability

variable {α State Item : Type} {encode : α → Word} {stateEncoding : State ↪ Word}

/-- Fold an encoded list through an encoded accumulator, allowing polynomially bounded intermediate
values. The initializer may depend on the input, and the step may call certified subroutines. -/
theorem IsPolyTime.list_foldl {elementEncoding : Item ↪ Word} {input : α → List Item}
    {initial : α → State} {step : State → Item → State}
    (hinput : IsPolyTime encode (fun a => listEncoding elementEncoding (input a)))
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding elementEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hintermediate : ∀ a index, index ≤ (input a).length →
      (stateEncoding (((input a).take index).foldl step (initial a))).length ≤
        size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) := by
  cases isEmpty_or_nonempty Item with
  | inl h =>
    have hempty (a : α) : input a = [] := Subsingleton.elim _ _
    simpa only [hempty, List.foldl_nil] using hinitial
  | inr h =>
    let fallback := Classical.choice h
    let advance (state : List Item × State) :=
      (state.1.tail, step state.2 (state.1.headD fallback))
    have htrace (word : List Item) (state : State) (index : ℕ) (hi : index ≤ word.length) :
      advance^[index] (word, state) = (word.drop index, (word.take index).foldl step state) := by
      induction index generalizing word state with
      | zero => simp
      | succ index ih =>
        cases word with
        | nil => simp at hi
        | cons value word =>
          simpa [Function.iterate_succ_apply, advance] using
            ih word (step state value) (by simpa using hi)
    have hbody : IsPolyTime (pairEncoding (listEncoding elementEncoding) stateEncoding)
        (fun state => pairEncoding (listEncoding elementEncoding) stateEncoding (advance state)) :=
      (isPolyTime_fst (listEncoding elementEncoding) stateEncoding).list_tail.pair
        (left := listEncoding elementEncoding) (right := stateEncoding)
        (hstep.comp_pair (left := stateEncoding) (right := elementEncoding)
          (f := fun state value => stateEncoding (step state value))
          (isPolyTime_snd (listEncoding elementEncoding) stateEncoding)
          ((isPolyTime_fst (listEncoding elementEncoding) stateEncoding).list_headD fallback))
    obtain ⟨c, d, hlength⟩ := hinput.length_le
    have hloop := (hinput.pair hinitial).iterate_encoded
      (stateEncoding := pairEncoding (listEncoding elementEncoding) stateEncoding)
      hinput.list_unaryLength hbody
      (size := fun n => 2 * (c * (n + 1) ^ d) + size n + 1) (by fun_prop)
      (by
        intro a index hi
        rw [htrace _ _ _ hi]
        simp only [length_pairEncoding]
        have := hintermediate a index hi
        have := hlength a
        have := length_listEncoding_drop_le elementEncoding (input a) index
        lia)
    simpa only [htrace _ _ _ le_rfl, List.take_length] using hloop.snd

variable {input : α → Word} {initial : α → State} {step : State → Bool → State}

/-- Fold a word through an encoded accumulator using the general list-fold compiler. -/
theorem IsPolyTime.foldl_encoded (hinput : IsPolyTime encode input)
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding boolEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hintermediate : ∀ a index, index ≤ (input a).length →
      (stateEncoding (((input a).take index).foldl step (initial a))).length ≤
        size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) :=
  hinput.encode_list_bool.list_foldl hinitial hstep hsize hintermediate

/-- A fold invariant relates the consumed prefix to the accumulator. It gives both the final
postcondition and the intermediate size bound, without requiring a separate execution trace. -/
theorem IsPolyTime.list_foldl_spec {elementEncoding : Item ↪ Word} {input : α → List Item}
    {step : State → Item → State}
    (hinput : IsPolyTime encode (fun a => listEncoding elementEncoding (input a)))
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding elementEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    (invariant : α → List Item → State → Prop)
    (hinit : ∀ a, invariant a [] (initial a))
    (hpreserve : ∀ a consumed state value, consumed ++ [value] <+: input a →
      invariant a consumed state → invariant a (consumed ++ [value]) (step state value))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a consumed state, consumed <+: input a → invariant a consumed state →
      (stateEncoding state).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) ∧
      ∀ a, invariant a (input a) ((input a).foldl step (initial a)) := by
  have htrace (a : α) (index : ℕ) (hi : index ≤ (input a).length) :
      invariant a ((input a).take index) (((input a).take index).foldl step (initial a)) := by
    induction index with
    | zero => simpa using hinit a
    | succ index ih =>
      have hlt : index < (input a).length := by lia
      simpa only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil] using
        hpreserve a ((input a).take index) _ (input a)[index]
          (by simpa only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
            using List.take_prefix (index + 1) (input a)) (ih (by lia))
  exact ⟨hinput.list_foldl hinitial hstep hsize
    (fun a index hi => hbound a ((input a).take index) _ (List.take_prefix ..) (htrace a index hi)),
    fun a => by simpa using htrace a (input a).length le_rfl⟩

/-- A list fold is efficient when each step grows its accumulator by a polynomial in the
encoded element's size. All visited elements are charged to the original collection. -/
theorem IsPolyTime.list_foldl_of_growth {elementEncoding : Item ↪ Word}
    {input : α → List Item} {step : State → Item → State}
    (hinput : IsPolyTime encode (fun a => listEncoding elementEncoding (input a)))
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding elementEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    {growth : ℕ → ℕ} (hpoly : PolynomiallyBounded growth)
    (hgrowth : ∀ state value, (stateEncoding (step state value)).length ≤
      (stateEncoding state).length + growth (elementEncoding value).length) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) := by
  obtain ⟨c, d, hg⟩ := hpoly
  obtain ⟨ci, di, hi⟩ := hinitial.length_le
  obtain ⟨cw, dw, hw⟩ := hinput.length_le
  refine (hinput.list_foldl_spec hinitial hstep
    (fun a consumed state => (stateEncoding state).length ≤ (stateEncoding (initial a)).length +
      consumed.length * (c * ((listEncoding elementEncoding (input a)).length + 1) ^ d))
    (by simp) ?_
    (size := fun n => ci * (n + 1) ^ di +
      cw * (n + 1) ^ dw * (c * (cw * (n + 1) ^ dw + 1) ^ d)) (by fun_prop) ?_).1
  · intro a consumed state value hprefix h
    have hvalue := length_element_le_length_listEncoding elementEncoding
      (hprefix.subset (by simp : value ∈ consumed ++ [value]))
    have hcost := (hg (elementEncoding value).length).trans
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hvalue 1) d))
    have := hgrowth state value
    simp only [List.length_append, List.length_singleton]
    lia
  · intro a consumed state hprefix h
    have hcount := hprefix.length_le.trans
      (list_length_le_length_encoding elementEncoding (input a))
    exact h.trans (Nat.add_le_add (hi a) (Nat.mul_le_mul (hcount.trans (hw a))
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right (hw a) 1) d))))

/-- The prefix-invariant rule specialized to ordinary words. -/
theorem IsPolyTime.foldl_spec (hinput : IsPolyTime encode input)
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding boolEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    (invariant : α → Word → State → Prop)
    (hinit : ∀ a, invariant a [] (initial a))
    (hpreserve : ∀ a consumed state bit, consumed ++ [bit] <+: input a →
      invariant a consumed state → invariant a (consumed ++ [bit]) (step state bit))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a consumed state, consumed <+: input a → invariant a consumed state →
      (stateEncoding state).length ≤ size (encode a).length) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) ∧
      ∀ a, invariant a (input a) ((input a).foldl step (initial a)) :=
  hinput.encode_list_bool.list_foldl_spec hinitial hstep invariant hinit hpreserve hsize hbound

/-- A fold is polynomial time when each step increases the encoded accumulator length by at
most a fixed amount. This includes growing lists and structured accumulators. -/
theorem IsPolyTime.foldl_of_bounded_growth (hinput : IsPolyTime encode input)
    (hinitial : IsPolyTime encode (fun a => stateEncoding (initial a)))
    (hstep : IsPolyTime (pairEncoding stateEncoding boolEncoding)
      (fun pair => stateEncoding (step pair.1 pair.2)))
    {growth : ℕ} (hgrowth : ∀ state bit,
      (stateEncoding (step state bit)).length ≤ (stateEncoding state).length + growth) :
    IsPolyTime encode (fun a => stateEncoding ((input a).foldl step (initial a))) := by
  obtain ⟨ci, di, hi⟩ := hinitial.length_le
  obtain ⟨cw, dw, hw⟩ := hinput.length_le
  exact (hinput.foldl_spec hinitial hstep
    (fun a consumed state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + consumed.length * growth)
    (by simp)
    (by
      intro a consumed state bit _ h
      have := hgrowth state bit
      simp only [List.length_append, List.length_singleton]
      lia)
    (size := fun n => ci * (n + 1) ^ di + cw * (n + 1) ^ dw * growth) (by fun_prop)
    (fun a index state hindex h => h.trans
      (Nat.add_le_add (hi a) (Nat.mul_le_mul_right growth (hindex.length_le.trans (hw a)))))).1

/-- Reverse an efficiently computed collection using the general fold rule. -/
theorem IsPolyTime.list_reverse {element : Item ↪ Word} {values : α → List Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a))) :
    IsPolyTime encode (fun a => listEncoding element (values a).reverse) := by
  simpa using hvalues.list_foldl_of_growth (stateEncoding := listEncoding element)
    (initial := fun _ => [])
    (step := fun reversed value => value :: reversed) (isPolyTime_const encode [])
    ((isPolyTime_snd (listEncoding element) element).list_cons
      (isPolyTime_fst (listEncoding element) element))
    (growth := fun n => 2 * n + 1) (by fun_prop)
    (by intro reversed value; simp only [listEncoding_cons, length_pairEncoding]; lia)

/-- Flatten the lists produced by a certified function on each element. The function's output
size theorem supplies the growth bound automatically. -/
theorem IsPolyTime.list_flatMap {Output : Type} {element : Item ↪ Word} {output : Output ↪ Word}
    {values : α → List Item} {f : Item → List Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime element (fun value => listEncoding output (f value))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).flatMap f)) := by
  obtain ⟨c, d, hsize⟩ := hf.length_le
  simpa only [← List.flatMap_eq_foldl] using
    hvalues.list_foldl_of_growth (stateEncoding := listEncoding output)
    (initial := fun _ => [])
    (step := fun result value => result ++ f value) (isPolyTime_const encode [])
    ((isPolyTime_fst (listEncoding output) element).list_append
      (hf.comp_encoded (isPolyTime_snd (listEncoding output) element)))
    (growth := fun n => c * (n + 1) ^ d) (by fun_prop)
    (by
      intro result value
      simp only [listEncoding_append, List.length_append]
      exact Nat.add_le_add_left (hsize value) _)

/-- Flatten nested encoded collections using the shared list-producing map. -/
theorem IsPolyTime.list_flatten {element : Item ↪ Word} {values : α → List (List Item)}
    (hvalues : IsPolyTime encode (fun a => listEncoding (listEncoding element) (values a))) :
    IsPolyTime encode (fun a => listEncoding element (values a).flatten) := by
  simpa only [List.flatMap_id'] using
    hvalues.list_flatMap (isPolyTime_input (listEncoding element))

/-- Map a certified function over an efficiently computed collection. -/
theorem IsPolyTime.list_map {Output : Type} {element : Item ↪ Word} {output : Output ↪ Word}
    {values : α → List Item} {f : Item → Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (hf : IsPolyTime element (fun value => output (f value))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).map f)) := by
  simpa only [← List.map_eq_flatMap] using hvalues.list_flatMap
    (f := fun value => [f value]) (hf.list_cons (rest := fun _ => []) (isPolyTime_const element []))

/-- An encoded collection of bits can be returned as an ordinary word. -/
theorem IsPolyTime.decode_list_bool {word : α → Word}
    (hword : IsPolyTime encode (fun a => listEncoding boolEncoding (word a))) :
    IsPolyTime encode word := by
  simpa only [← List.flatMap_eq_foldl, List.flatMap_singleton', wordEncoding,
    Function.Embedding.refl_apply] using hword.list_foldl_of_growth
    (stateEncoding := wordEncoding) (initial := fun _ => [])
    (step := fun result bit => result ++ [bit]) (isPolyTime_const encode [])
    ((isPolyTime_fst wordEncoding boolEncoding).append
      (isPolyTime_snd wordEncoding boolEncoding))
    (growth := fun _ => 1) (by fun_prop) (by simp [wordEncoding])

/-- An encoded list of Boolean values can be read as an ordinary word. -/
theorem isPolyTime_decode_list_bool :
    IsPolyTime (listEncoding boolEncoding) (fun word => word) :=
  (isPolyTime_input (listEncoding boolEncoding)).decode_list_bool

/-- Concatenate an encoded collection of words into an ordinary word. -/
theorem IsPolyTime.flatten {values : α → List Word}
    (hvalues : IsPolyTime encode (fun a => listEncoding wordEncoding (values a))) :
    IsPolyTime encode (fun a => (values a).flatten) := by
  simpa only [wordEncoding, Function.Embedding.coe_refl, List.flatMap_id] using
    (hvalues.list_flatMap (isPolyTime_input wordEncoding).encode_list_bool).decode_list_bool

/-- Capture a runtime environment for every element of a collection. The complete environment
and every copy are charged to the polynomial bound. -/
private theorem IsPolyTime.list_capture {Environment : Type} {environment : Environment ↪ Word}
    {element : Item ↪ Word} {env : α → Environment} {values : α → List Item}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a))) :
    IsPolyTime encode (fun a => listEncoding (pairEncoding environment element)
      ((values a).map (fun value => (env a, value)))) := by
  let output := listEncoding (pairEncoding environment element)
  let stateCode := pairEncoding environment output
  let advance (state : Environment × List (Environment × Item)) (value : Item) :=
    (state.1, state.2 ++ [(state.1, value)])
  have htrace (items : List Item) (env : Environment) (result : List (Environment × Item)) :
      items.foldl advance (env, result) = (env, result ++ items.map (Prod.mk env)) := by
    induction items generalizing result with
    | nil => simp
    | cons value items ih => simpa [advance, List.append_assoc] using ih (result ++ [(env, value)])
  have hlength (items : List Item) (env : Environment) :
      (output (items.map (Prod.mk env))).length = (listEncoding element items).length +
        items.length * (4 * (environment env).length + 2) := by
    induction items with
    | nil => simp [output]
    | cons value items ih =>
      simp only [List.map_cons, List.length_cons, output, listEncoding_cons,
        length_pairEncoding, Nat.add_mul, Nat.one_mul] at ih ⊢
      lia
  have henvStep := (isPolyTime_fst stateCode element).fst
  have hresultStep := (isPolyTime_fst stateCode element).snd
  have hvalueStep := isPolyTime_snd stateCode element
  have hstep : IsPolyTime (pairEncoding stateCode element)
      (fun pair => stateCode (advance pair.1 pair.2)) :=
    henvStep.pair (left := environment) (right := output)
      (hresultStep.list_append ((henvStep.pair hvalueStep).list_cons
        (rest := fun _ => []) (isPolyTime_const _ [])))
  obtain ⟨ce, de, he⟩ := henv.length_le
  obtain ⟨cv, dv, hv⟩ := hvalues.length_le
  have hfold := hvalues.list_foldl (stateEncoding := stateCode) (step := advance)
    (henv.pair (left := environment) (right := output) (g := fun _ => [])
      (isPolyTime_const encode [])) hstep
    (size := fun n => 2 * (ce * (n + 1) ^ de) + cv * (n + 1) ^ dv +
      cv * (n + 1) ^ dv * (4 * (ce * (n + 1) ^ de) + 2) + 1) (by fun_prop) (by
      intro a index hi
      rw [htrace]
      simp only [List.nil_append, stateCode, length_pairEncoding, hlength]
      have htake := congrArg (fun items => (listEncoding element items).length)
        (List.take_append_drop index (values a))
      simp only [listEncoding_append, List.length_append] at htake
      have hprefix : (listEncoding element ((values a).take index)).length ≤
          cv * ((encode a).length + 1) ^ dv := by have := hv a; lia
      have hcount := (list_length_le_length_encoding element ((values a).take index)).trans hprefix
      have hproduct := Nat.mul_le_mul hcount
        (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (he a)) 2)
      have := he a
      lia)
  simpa only [htrace, List.nil_append] using hfold.snd

/-- Map a certified function that captures efficiently computed runtime data. -/
theorem IsPolyTime.list_map_with {Environment Output : Type}
    {environment : Environment ↪ Word} {element : Item ↪ Word} {output : Output ↪ Word}
    {env : α → Environment} {values : α → List Item} {f : Environment → Item → Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hf : IsPolyTime (pairEncoding environment element) (fun pair => output (f pair.1 pair.2))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).map (f (env a)))) := by
  simpa only [List.map_map, Function.comp_def] using (hvalues.list_capture henv).list_map hf

/-- Flatten a certified function's lists while retaining a captured runtime environment. -/
theorem IsPolyTime.list_flatMap_with {Environment Output : Type}
    {environment : Environment ↪ Word} {element : Item ↪ Word} {output : Output ↪ Word}
    {env : α → Environment} {values : α → List Item} {f : Environment → Item → List Output}
    (hvalues : IsPolyTime encode (fun a => listEncoding element (values a)))
    (henv : IsPolyTime encode (fun a => environment (env a)))
    (hf : IsPolyTime (pairEncoding environment element)
      (fun pair => listEncoding output (f pair.1 pair.2))) :
    IsPolyTime encode (fun a => listEncoding output ((values a).flatMap (f (env a)))) := by
  simpa only [List.flatMap_map] using (hvalues.list_capture henv).list_flatMap hf

/-- Reverse an efficiently computed word, using a list accumulator in the general fold rule. -/
theorem IsPolyTime.reverse {word : α → Word} (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => (word a).reverse) := by
  simpa [wordEncoding] using hword.foldl_of_bounded_growth (stateEncoding := wordEncoding)
    (step := fun reversed bit => bit :: reversed)
    (isPolyTime_const encode [])
    ((isPolyTime_snd wordEncoding boolEncoding).cons (isPolyTime_fst wordEncoding boolEncoding))
    (growth := 1) (by simp [wordEncoding])

/-- Zip two efficient words with a fixed Boolean operation, stopping at the shorter word.
The implementation is an ordinary fold with a pair of word accumulators. -/
theorem IsPolyTime.zipWith {left right : α → Word}
    (hleft : IsPolyTime encode left) (hright : IsPolyTime encode right)
    (op : Bool → Bool → Bool) :
    IsPolyTime encode (fun a => (left a).zipWith op (right a)) := by
  let advance (state : Word × Word) (bit : Bool) :=
    (state.1.tail, (state.1.take 1).map (op bit) ++ state.2)
  have hresult (left right result : Word) :
      (left.foldl advance (right, result)).2 = (left.zipWith op right).reverse ++ result := by
    induction left generalizing right result with
    | nil => simp
    | cons bit left ih =>
      cases right with
      | nil => simpa [advance] using ih [] result
      | cons other right =>
        change (left.foldl advance (right, op bit other :: result)).2 = _
        rw [ih]
        simp [List.reverse_cons, List.append_assoc]
  let stateCode := pairEncoding wordEncoding wordEncoding
  have hfirst := (isPolyTime_fst stateCode boolEncoding).fst
  have hsecond := (isPolyTime_fst stateCode boolEncoding).snd
  have hbit := isPolyTime_snd stateCode boolEncoding
  have hstep : IsPolyTime (pairEncoding stateCode boolEncoding)
      (fun pair => stateCode (advance pair.1 pair.2)) :=
    hfirst.tail.pair (left := wordEncoding) (right := wordEncoding)
      ((hfirst.head.map_with_bit hbit op).append hsecond)
  have hfold := hleft.foldl_of_bounded_growth (stateEncoding := stateCode) (step := advance)
    (hright.pair (left := wordEncoding) (right := wordEncoding) (isPolyTime_const encode []))
    hstep (growth := 1) (by
      rintro ⟨remaining, result⟩ bit
      simp only [stateCode, advance, length_pairEncoding, wordEncoding,
        Function.Embedding.refl_apply, List.length_tail, List.length_append, List.length_map,
        List.length_take]
      lia)
  simpa only [hresult, List.append_nil, wordEncoding, Function.Embedding.refl_apply,
    List.reverse_reverse] using hfold.snd.reverse

end Cslib.Probability
