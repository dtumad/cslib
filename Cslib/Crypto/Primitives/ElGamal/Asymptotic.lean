/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Computability.PolynomialTime.Encoding
public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Crypto.Primitives.ElGamal.Security
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Asymptotic security of ElGamal encryption (spike)

Katz–Lindell's statement: if DDH is hard relative to a group generator `𝒢`, then ElGamal is
secure against eavesdroppers. Adversaries are coin-flipping programs that probabilistic machines
realize in polynomial time; experiments may also choose uniformly from finite ranges.
-/

@[expose] public section

open PFunctor MeasureTheory ProbabilityTheory Turing MultiTapePTM MultiTapeTM

namespace Cslib.Crypto

/-- Functions decaying faster than any inverse polynomial. -/
abbrev Negligible (ε : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) ε

/-- Programs flipping fair coins, as realized by probabilistic machines without oracles. -/
abbrev Prog := (effects Empty).FreeM

/-- One operation for each positive `k`, answered by an element of `Fin k`. -/
abbrev Uniform : PFunctor := ⟨ℕ+, fun k => Fin k⟩

/-- The operations of experiments: fair coins and uniform choices. -/
abbrev Ops : PFunctor := effects Empty + Uniform

/-- Experiments flip fair coins and choose uniformly from finite ranges. -/
abbrev Exp := Ops.FreeM

instance (a : Ops.A) : MeasurableSpace (Ops.B a) :=
  match a with
  | .inl a => inferInstanceAs (MeasurableSpace ((effects Empty).B a))
  | .inr k => inferInstanceAs (MeasurableSpace (Fin k))

instance (a : Ops.A) : DiscreteMeasurableSpace (Ops.B a) := by
  cases a with
  | inl a => exact inferInstanceAs (DiscreteMeasurableSpace ((effects Empty).B a))
  | inr k => exact inferInstanceAs (DiscreteMeasurableSpace (Fin k))

/-- Fair coins and uniform choices. -/
noncomputable def answers : (a : Ops.A) → Measure (Ops.B a)
  | .inl a => OracleEnv.fairCoins a
  | .inr _ => uniformOn Set.univ

instance (a : Ops.A) : IsProbabilityMeasure (answers a) := by
  rcases a with (_ | ⟨oracle, _⟩) | k
  · exact inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set Bool)))
  · exact isEmptyElim oracle
  · have : NeZero (k : ℕ) := ⟨k.ne_zero⟩
    exact inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin k))))

/-- The probability that an experiment returns `true`. -/
noncomputable def Pr (e : Exp Bool) : ℝ :=
  (e.toMeasure answers).real {true}

/-- Run a coin-flipping program within an experiment. -/
def toExp {α : Type} (x : Prog α) : Exp α :=
  x.liftM fun a => FreeM.lift (P := Ops) (.inl a)

/-- Choose an element of `Fin k` uniformly at random. -/
def uniform (k : ℕ+) : Exp (Fin k) :=
  FreeM.lift (P := Ops) (.inr k)

@[simp]
theorem toExp_pure {α : Type} (a : α) : toExp (pure a : Prog α) = pure a := rfl

@[simp]
theorem toExp_bind {α β : Type} (x : Prog α) (f : α → Prog β) :
    toExp (x >>= f) = toExp x >>= fun a => toExp (f a) :=
  (FreeM.isMonadHom_liftM _).map_bind x f

@[simp]
theorem toExp_map {α β : Type} (f : α → β) (x : Prog α) : toExp (f <$> x) = f <$> toExp x :=
  (FreeM.isMonadHom_liftM _).map_map f x

/-- The output measures of experiments. -/
theorem isMeasureSemantics_answers : IsMeasureSemantics Exp fun x => x.toMeasure answers :=
  FreeM.isMeasureSemantics_toMeasure answers

@[simp]
theorem toMeasure_uniform (k : ℕ+) : (uniform k).toMeasure answers = uniformOn Set.univ :=
  FreeM.toMeasure_lift _ _

@[simp]
theorem toMeasure_toExp_coin : (toExp coin).toMeasure answers = uniformOn Set.univ := by
  simp [toExp, coin, answers, OracleEnv.fairCoins, OracleEnv.statelessMeasure]

/-- A group generator: on the security parameter, it samples a description of a cyclic group
with a generator. Elements and descriptions are represented by binary words. -/
structure GroupGen where
  /-- Descriptions of groups. -/
  Desc : Type
  /-- The elements of the described group. -/
  Elem : Desc → Type
  [group : ∀ d, Group (Elem d)]
  /-- The representation of descriptions. -/
  encDesc : Desc ↪ Word
  /-- The representation of elements. -/
  encElem : ∀ d, Elem d ↪ Word
  /-- The order of the described group. -/
  order : Desc → ℕ+
  /-- The generator of the described group. -/
  gen : ∀ d, Elem d
  bijective_pow : ∀ d, Function.Bijective fun x : Fin (order d) => gen d ^ x.val
  /-- Sample a description for the security parameter. -/
  setup : ℕ → Exp Desc

namespace GroupGen

attribute [instance] group

variable (𝒢 : GroupGen)

instance : MeasurableSpace 𝒢.Desc := ⊤

instance : DiscreteMeasurableSpace 𝒢.Desc := ⟨fun _ => trivial⟩

instance : Countable 𝒢.Desc := 𝒢.encDesc.injective.countable

instance (d : 𝒢.Desc) : MeasurableSpace (𝒢.Elem d) := ⊤

instance (d : 𝒢.Desc) : DiscreteMeasurableSpace (𝒢.Elem d) := ⟨fun _ => trivial⟩

instance (d : 𝒢.Desc) : Countable (𝒢.Elem d) := (𝒢.encElem d).injective.countable

/-- The group operations are polynomial-time in the representation, and descriptions sampled for
the security parameter `n`, and their elements, have length polynomial in `n`. -/
structure IsEfficient : Prop where
  mul : IsPolyTime (sigmaEncoding 𝒢.encDesc fun d => pairEncoding (𝒢.encElem d) (𝒢.encElem d))
    fun x => 𝒢.encElem x.1 (x.2.1 * x.2.2)
  polySize : ∃ c e : ℕ, ∀ n d, MonadAttach.CanReturn (𝒢.setup n) d →
    (𝒢.encDesc d).length ≤ c * (n + 1) ^ e ∧
      ∀ x : 𝒢.Elem d, (𝒢.encElem d x).length ≤ c * (n + 1) ^ e

/-- A distinguisher for Diffie–Hellman triples in described groups. -/
structure DDHAdversary where
  /-- Guess whether a triple of elements of the group described by `d` is a DH triple. -/
  run : ℕ → (d : 𝒢.Desc) → 𝒢.Elem d → 𝒢.Elem d → 𝒢.Elem d → Prog Bool

/-- The distinguisher runs in probabilistic polynomial time in the security parameter and the
representations of the description and the triple. -/
def DDHAdversary.IsPPT {𝒢 : GroupGen} (D : 𝒢.DDHAdversary) : Prop :=
  MultiTapePTM.IsPPTFamily (fun _ => sigmaEncoding 𝒢.encDesc fun d =>
      pairEncoding (𝒢.encElem d) (pairEncoding (𝒢.encElem d) (𝒢.encElem d)))
    (fun _ _ => boolEncoding) fun n x => D.run n x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The DDH experiment on a Diffie–Hellman triple. -/
def ddhReal (D : 𝒢.DDHAdversary) (n : ℕ) : Exp Bool := do
  let d ← 𝒢.setup n
  DDH.realExperiment (uniform (𝒢.order d)) (𝒢.gen d) fun a b c => toExp (D.run n d a b c)

/-- The DDH experiment on a triple with an independent third exponent. -/
def ddhRand (D : 𝒢.DDHAdversary) (n : ℕ) : Exp Bool := do
  let d ← 𝒢.setup n
  DDH.idealExperiment (uniform (𝒢.order d)) (𝒢.gen d) fun a b c => toExp (D.run n d a b c)

/-- DDH is hard relative to `𝒢`: every polynomial-time distinguisher has negligible advantage. -/
def DDHHard : Prop :=
  ∀ D : 𝒢.DDHAdversary, D.IsPPT → Negligible fun n => |Pr (𝒢.ddhReal D n) - Pr (𝒢.ddhRand D n)|

end GroupGen

/-- A public-key encryption scheme, with the representations of its keys, messages and
ciphertexts. -/
structure PKE where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : PK → Type
  /-- Messages. -/
  Msg : PK → Type
  /-- Ciphertexts. -/
  Ctxt : PK → Type
  /-- The representation of public keys. -/
  encPK : PK ↪ Word
  /-- The representation of messages. -/
  encMsg : ∀ pk, Msg pk ↪ Word
  /-- The representation of ciphertexts. -/
  encCtxt : ∀ pk, Ctxt pk ↪ Word
  /-- Generate a key pair for the security parameter. -/
  gen : ℕ → Exp (Σ pk, SK pk)
  /-- Encrypt a message. -/
  enc : (pk : PK) → Msg pk → Exp (Ctxt pk)
  /-- Decrypt a ciphertext. -/
  dec : (pk : PK) → SK pk → Ctxt pk → Option (Msg pk)

namespace PKE

variable (S : PKE)

/-- Decryption recovers every encrypted message under every generated key pair. -/
def IsCorrect : Prop :=
  ∀ n pk sk m c, MonadAttach.CanReturn (S.gen n) ⟨pk, sk⟩ →
    MonadAttach.CanReturn (S.enc pk m) c → S.dec pk sk c = some m

/-- An eavesdropper: it chooses two messages for a public key, then guesses which was encrypted.
Its two phases share a private state. -/
structure EavAdversary where
  /-- The private state. -/
  State : Type
  /-- The representation of the private state. -/
  encState : State ↪ Word
  /-- Choose two messages for the public key. -/
  choose : ℕ → (pk : S.PK) → Prog (S.Msg pk × S.Msg pk × State)
  /-- Guess which message the ciphertext encrypts. -/
  guess : ℕ → State → (pk : S.PK) → S.Ctxt pk → Prog Bool

variable {S}

instance (A : S.EavAdversary) : MeasurableSpace A.State := ⊤

instance (A : S.EavAdversary) : DiscreteMeasurableSpace A.State := ⟨fun _ => trivial⟩

instance (A : S.EavAdversary) : Countable A.State := A.encState.injective.countable

/-- Both phases run in probabilistic polynomial time in the security parameter and the
representations of their inputs. -/
def EavAdversary.IsPPT (A : S.EavAdversary) : Prop :=
  MultiTapePTM.IsPPTFamily (fun _ => S.encPK)
      (fun _ pk => pairEncoding (S.encMsg pk) (pairEncoding (S.encMsg pk) A.encState)) A.choose ∧
    MultiTapePTM.IsPPTFamily (fun _ => pairEncoding A.encState (sigmaEncoding S.encPK S.encCtxt))
      (fun _ _ => boolEncoding) fun n x => A.guess n x.1 x.2.1 x.2.2

variable (S)

/-- The eavesdropping experiment: the adversary sees an encryption of one of its two messages,
selected by a fair coin, and wins by guessing which. -/
def eavExp (A : S.EavAdversary) (n : ℕ) : Exp Bool := do
  let ⟨pk, _⟩ ← S.gen n
  let (m₀, m₁, state) ← toExp (A.choose n pk)
  let bit ← toExp coin
  let c ← S.enc pk (if bit then m₁ else m₀)
  let answer ← toExp (A.guess n state pk c)
  pure (bit == answer)

/-- Every admissible eavesdropper guesses the encrypted message with negligible advantage. -/
def IsEavSecureAgainst (Adm : S.EavAdversary → Prop) : Prop :=
  ∀ A, Adm A → Negligible fun n => |Pr (S.eavExp A n) - 1 / 2|

/-- Security against polynomial-time eavesdroppers. -/
def IsEavSecure : Prop := S.IsEavSecureAgainst EavAdversary.IsPPT

end PKE

namespace ElGamal

variable (𝒢 : GroupGen)

/-- ElGamal encryption over the groups generated by `𝒢`. -/
def scheme : PKE where
  PK := Σ d, 𝒢.Elem d
  SK pk := Fin (𝒢.order pk.1)
  Msg pk := 𝒢.Elem pk.1
  Ctxt pk := 𝒢.Elem pk.1 × 𝒢.Elem pk.1
  encPK := sigmaEncoding 𝒢.encDesc 𝒢.encElem
  encMsg pk := 𝒢.encElem pk.1
  encCtxt pk := pairEncoding (𝒢.encElem pk.1) (𝒢.encElem pk.1)
  gen n := do
    let d ← 𝒢.setup n
    let (h, x) ← keygen (uniform (𝒢.order d)) (𝒢.gen d)
    pure ⟨⟨d, h⟩, x⟩
  enc pk m := encrypt (uniform (𝒢.order pk.1)) (𝒢.gen pk.1) pk.2 m
  dec _ x c := some (decrypt x c)

variable {𝒢}

/-- The DDH distinguisher playing the eavesdropping experiment with `A`, which keeps the public key
in its state. -/
def reduction (A : (scheme 𝒢).EavAdversary) : 𝒢.DDHAdversary where
  run n d h₁ h₂ h₃ := ddhReduction coin
    (fun h => (fun r => (r.1, r.2.1, (r.2.2, h))) <$> A.choose n ⟨d, h⟩)
    (fun s c => A.guess n s.1 ⟨d, s.2⟩ c) h₁ h₂ h₃

theorem isCorrect : (scheme 𝒢).IsCorrect := by
  rintro n ⟨d, h⟩ x m c hgen henc
  simp [scheme, keygen, encrypt] at hgen henc
  obtain ⟨r, -, rfl⟩ := (FreeM.canReturn_map' _ _ _).mp henc
  obtain ⟨d', -, x', -, heq⟩ := hgen
  cases heq
  exact congrArg some (decrypt_encrypt (G := 𝒢.Elem d) _ m x' r)

section Advantage

variable (A : (scheme 𝒢).EavAdversary) (n : ℕ)

/-- The first phase of `A` for the group `d`, keeping the public key in its state. -/
def choose' (d : 𝒢.Desc) (h : 𝒢.Elem d) : Exp (𝒢.Elem d × 𝒢.Elem d × (A.State × 𝒢.Elem d)) :=
  toExp ((fun r => (r.1, r.2.1, (r.2.2, h))) <$> A.choose n ⟨d, h⟩)

/-- The second phase of `A` for the group `d`, reading the public key from its state. -/
def guess' (d : 𝒢.Desc) (s : A.State × 𝒢.Elem d) (c : 𝒢.Elem d × 𝒢.Elem d) : Exp Bool :=
  toExp (A.guess n s.1 ⟨d, s.2⟩ c)

theorem eavExp_eq : (scheme 𝒢).eavExp A n = 𝒢.setup n >>= fun d =>
    cpaExperiment (uniform (𝒢.order d)) (toExp coin) (𝒢.gen d) (choose' A n d) (guess' A n d) := by
  simp only [PKE.eavExp, scheme, bind_assoc, pure_bind]
  congr 1; funext d
  simp [cpaExperiment, keygen, encrypt, challenge, choose', guess']
  rfl

theorem ddhReal_reduction : 𝒢.ddhReal (reduction A) n = 𝒢.setup n >>= fun d =>
    DDH.realExperiment (uniform (𝒢.order d)) (𝒢.gen d)
      (ddhReduction (toExp coin) (choose' A n d) (guess' A n d)) := by
  simp only [GroupGen.ddhReal]
  congr 1; funext d; congr 1; funext a b c
  simp [reduction, ddhReduction, challenge, choose', guess']

theorem ddhRand_reduction : 𝒢.ddhRand (reduction A) n = 𝒢.setup n >>= fun d =>
    DDH.idealExperiment (uniform (𝒢.order d)) (𝒢.gen d)
      (ddhReduction (toExp coin) (choose' A n d) (guess' A n d)) := by
  simp only [GroupGen.ddhRand]
  congr 1; funext d; congr 1; funext a b c
  simp [reduction, ddhReduction, challenge, choose', guess']

theorem eav_advantage_eq :
    |Pr ((scheme 𝒢).eavExp A n) - 1 / 2| =
      |Pr (𝒢.ddhReal (reduction A) n) - Pr (𝒢.ddhRand (reduction A) n)| := by
  have hsem := isMeasureSemantics_answers
  have hreal : Pr ((scheme 𝒢).eavExp A n) = Pr (𝒢.ddhReal (reduction A) n) := by
    rw [Pr, Pr, eavExp_eq, ddhReal_reduction, hsem.map_bind_of_discrete,
      hsem.map_bind_of_discrete]
    congr 3
    funext d
    exact (sem_realExperiment_ddhReduction hsem _ _ _ _ _).symm
  have hrand : Pr (𝒢.ddhRand (reduction A) n) = 1 / 2 := by
    rw [Pr, ddhRand_reduction, hsem.map_bind_of_discrete]
    have hd (d : 𝒢.Desc) := sem_idealExperiment_ddhReduction hsem (uniform (𝒢.order d))
      (toExp coin) (𝒢.gen d) (choose' A n d) (guess' A n d) (𝒢.bijective_pow d)
      (toMeasure_uniform _) toMeasure_toExp_coin
    simp only [hd, Measure.bind_const, measure_univ, one_smul]
    rw [measureReal_def, uniformOn_univ]
    simp
  rw [hreal, hrand]

end Advantage

theorem isPPT_reduction (h𝒢 : 𝒢.IsEfficient) {A : (scheme 𝒢).EavAdversary} (hA : A.IsPPT) :
    (reduction A).IsPPT := by
  sorry

/-- If DDH is hard relative to `𝒢`, ElGamal encryption is secure against eavesdroppers. -/
theorem isEavSecure_of_ddhHard (h𝒢 : 𝒢.IsEfficient) (hddh : 𝒢.DDHHard) :
    (scheme 𝒢).IsEavSecure := fun A hA => by
  simpa only [eav_advantage_eq] using hddh (reduction A) (isPPT_reduction h𝒢 hA)

end ElGamal

end Cslib.Crypto
