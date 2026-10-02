/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Oracle

/-!
# Typed oracle interfaces with charged encodings

`OracleEncoding` represents a typed query by an operation name and a request word, and represents
its dependent response by a word. `encodeProgram` performs response decoding inside the program.
Its `IsPPTOn` contract certifies the translated program against every word oracle, including ones
that return malformed encodings. Thus request construction and response decoding receive no free
computation. The decoder is total, with a specified round trip on valid replies.

`encodeOracle` is a semantic interpreter, not an efficiency claim about the oracle. The stateful
round-trip theorem preserves the entire joint result and private-state distribution, including
when several operation names use one random-oracle table.
-/

@[expose] public section

namespace Cslib.Probability

/-- Word representations for typed requests and their dependent replies. -/
structure OracleEncoding (Operation Query : Type) (Response : Query → Type) where
  /-- An operation name and a word identify the complete request. -/
  request : Query ↪ (Operation × Word)
  /-- A reply is represented on the selected operation's answer tape. -/
  response : (q : Query) → Response q ↪ Word
  /-- Decode replies inside the program; malformed words receive a total interpretation. -/
  decode : (q : Query) → Word → Response q
  /-- Valid replies round-trip exactly. -/
  decode_response : ∀ q answer, decode q (response q answer) = answer

namespace OracleEncoding

variable {Operation Query α β State : Type} {Response : Query → Type}

/-- Named word requests and replies already have the machine representation. -/
def word (Operation : Type) : OracleEncoding Operation (Operation × Word) (fun _ => Word) where
  request := Function.Embedding.refl _
  response _ := wordEncoding
  decode _ := id
  decode_response _ _ := rfl

/-- Translate typed calls to named word calls, retaining all local decoding in the program. -/
def encodeProgram (encoding : OracleEncoding Operation Query Response)
    (program : OracleComp Query Response α) : WordOracleComp Operation α :=
  OracleComp.simulate (fun q => encoding.decode q <$> OracleComp.query (encoding.request q)) program

/-- The word interface needs no translation. -/
@[simp] theorem word_encodeProgram (program : WordOracleComp Operation α) :
    (word Operation).encodeProgram program = program := by
  simp [encodeProgram, word]

@[simp] theorem encodeProgram_pure (encoding : OracleEncoding Operation Query Response) (a : α) :
    encoding.encodeProgram (pure a) = pure a := rfl

@[simp] theorem encodeProgram_bind (encoding : OracleEncoding Operation Query Response)
    (program : OracleComp Query Response α) (next : α → OracleComp Query Response β) :
    encoding.encodeProgram (program >>= next) =
      (encoding.encodeProgram program >>= fun a => encoding.encodeProgram (next a)) :=
  OracleComp.simulate_bind _ _ _

@[simp] theorem encodeProgram_map (encoding : OracleEncoding Operation Query Response)
    (f : α → β) (program : OracleComp Query Response α) :
    encoding.encodeProgram (f <$> program) = f <$> encoding.encodeProgram program :=
  OracleComp.simulate_map _ _ _

/-- The translated program interacts with the decoded word handler, sharing its state throughout. -/
theorem runState_encodeProgram (encoding : OracleEncoding Operation Query Response)
    (oracle : Operation × Word → StateT State PMF Word)
    (program : OracleComp Query Response α) (s : State) :
    OracleComp.runState oracle (encoding.encodeProgram program) s =
      OracleComp.runState (fun q state =>
        (oracle (encoding.request q) state).map (fun (word, state') =>
          (encoding.decode q word, state'))) program s := by
  rw [encodeProgram, OracleComp.runState_simulate]
  congr 1

/-- A semantic word interpreter for a typed oracle. Invalid requests return the empty word and
leave private state unchanged. This interpreter's computation is external to the machine clock. -/
noncomputable def encodeOracle (encoding : OracleEncoding Operation Query Response)
    (oracle : (q : Query) → StateT State PMF (Response q)) :
    Operation × Word → StateT State PMF Word := by
  classical
  exact fun request state =>
    if h : ∃ q, encoding.request q = request then
      (oracle h.choose state).map (fun (answer, state') =>
        (encoding.response h.choose answer, state'))
    else PMF.pure ([], state)

/-- Valid requests are routed to the original oracle and their replies are encoded. -/
@[simp] theorem encodeOracle_request (encoding : OracleEncoding Operation Query Response)
    (oracle : (q : Query) → StateT State PMF (Response q)) (q : Query) (s : State) :
    encoding.encodeOracle oracle (encoding.request q) s =
      (oracle q s).map (fun (answer, s') => (encoding.response q answer, s')) := by
  classical
  have h : ∃ q', encoding.request q' = encoding.request q := ⟨q, rfl⟩
  simp only [encodeOracle, dite_eq_left h]
  have hq : h.choose = q := encoding.request.injective h.choose_spec
  rw [hq]

/-- Encoding preserves both the typed program's result and the oracle's final private state. -/
theorem runState_encode (encoding : OracleEncoding Operation Query Response)
    (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (s : State) :
    OracleComp.runState (encoding.encodeOracle oracle) (encoding.encodeProgram program) s =
      OracleComp.runState oracle program s := by
  rw [runState_encodeProgram]
  congr 1
  funext q state
  simp only [encodeOracle_request, PMF.map_comp, Function.comp_def, encoding.decode_response]
  exact PMF.map_id _

variable [DecidableEq Operation]

/-- A typed oracle program is PPT when the complete encoded program has a uniform machine
realization, including its request construction and response decoding. -/
def IsPPTOn (encoding : OracleEncoding Operation Query Response) (input : α → Word)
    (output : β ↪ Word) (program : α → OracleComp Query Response β) : Prop :=
  IsOraclePPTOn input output (fun a => encoding.encodeProgram (program a))

/-- The typed contract specializes exactly to the named-word contract. -/
@[simp] theorem word_isPPTOn (input : α → Word) (output : β ↪ Word)
    (program : α → WordOracleComp Operation β) :
    (word Operation).IsPPTOn input output program ↔ IsOraclePPTOn input output program := by
  simp [IsPPTOn]

/-- A typed certificate realizes the original program against every typed stateful oracle,
using its word interpreter and the same uniform machine and polynomial. -/
theorem IsPPTOn.realizes {encoding : OracleEncoding Operation Query Response} {input : α → Word}
    {output : β ↪ Word} {program : α → OracleComp Query Response β}
    (h : encoding.IsPPTOn input output program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
      ∀ a (State : Type) (oracle : (q : Query) → StateT State PMF (Response q)) s,
        OracleComp.runState oracle (output <$> program a) s =
          OracleComp.runState (encoding.encodeOracle oracle)
            (machine.run (fun op word => OracleComp.query (op, word))
              (c * ((input a).length + 1) ^ d) (input a)) s := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨k, Control, hfinite, machine, c, d, fun a State oracle s => ?_⟩
  simpa only [← encodeProgram_map, runState_encode] using
    h a State (encoding.encodeOracle oracle) s

/-- Stateful semantic equality of typed programs preserves their efficiency contract. -/
theorem IsPPTOn.congr {encoding : OracleEncoding Operation Query Response} {input : α → Word}
    {output : β ↪ Word} {program program' : α → OracleComp Query Response β}
    (h : encoding.IsPPTOn input output program)
    (heq : ∀ a (State : Type) (oracle : (q : Query) → StateT State PMF (Response q)) s,
      OracleComp.runState oracle (program a) s = OracleComp.runState oracle (program' a) s) :
    encoding.IsPPTOn input output program' := by
  apply Cslib.Probability.IsOraclePPTOn.congr h
  intro a State oracle s
  simpa only [runState_encodeProgram] using heq a State
    (fun q state => (oracle (encoding.request q) state).map (fun (word, state') =>
      (encoding.decode q word, state'))) s

/-- Boolean postprocessing composes with a typed oracle program and preserves all its effects. -/
theorem IsPPTOn.map_bool {encoding : OracleEncoding Operation Query Response} {input : α → Word}
    {program : α → OracleComp Query Response Bool} (h : encoding.IsPPTOn input boolEncoding program)
    (f : Bool → Bool) : encoding.IsPPTOn input boolEncoding (fun a => f <$> program a) := by
  simpa only [IsPPTOn, encodeProgram_map] using Cslib.Probability.IsOraclePPTOn.map_bool h f

/-- The encoded output has polynomial length for every typed oracle. -/
theorem IsPPTOn.length_le {encoding : OracleEncoding Operation Query Response} {input : α → Word}
    {output : β ↪ Word} {program : α → OracleComp Query Response β}
    (h : encoding.IsPPTOn input output program) :
    ∃ c d : ℕ, ∀ a (State : Type)
      (oracle : (q : Query) → StateT State PMF (Response q)) s s' result,
      (result, s') ∈ (OracleComp.runState oracle (program a) s).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨c, d, hbound⟩ := Cslib.Probability.IsOraclePPTOn.length_le h
  refine ⟨c, d, fun a State oracle s s' result hresult => ?_⟩
  exact hbound a State (encoding.encodeOracle oracle) s s' result
    (by simpa only [runState_encode] using hresult)

end OracleEncoding
end Cslib.Probability
