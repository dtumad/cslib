/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import Cslib.Computability.PolynomialTime.Probabilistic
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Composing probabilistic polynomial-time programs (spike)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.FreeM

universe uA uB uS

variable {P : PFunctor.{uA, uB}} {α β : Type uB}

/-- Continuations with the same output measure on every value a program can return give the
same output measure. No measurable structure on the intermediate values is needed. -/
theorem toMeasure_bind_congr [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace β]
    (μ : (a : P.A) → Measure (P.B a)) {x : P.FreeM α} {f g : α → P.FreeM β}
    (h : ∀ a, MonadAttach.CanReturn x a → (f a).toMeasure μ = (g a).toMeasure μ) :
    (x >>= f).toMeasure μ = (x >>= g).toMeasure μ := by
  induction x with
  | pure a => exact h a rfl
  | lift_bind a k ih =>
    simp only [bind_eq_bind, bind_assoc, toMeasure_lift_bind']
    refine congrArg (Measure.bind (μ a)) (funext fun b => ih b fun c hc => h c ?_)
    exact (canReturn_lift_bind _ _ _).mpr ⟨b, hc⟩

/-- A value a program returns from a state is a value the program can return. -/
theorem canReturn_withState {S : Type uB} {x : P.FreeM α} {s : S} {p : α × S}
    (h : MonadAttach.CanReturn (x.withState s) p) : MonadAttach.CanReturn x p.1 := by
  induction x generalizing s with
  | pure a => exact congrArg Prod.fst h
  | lift_bind a k ih =>
    rw [withState_lift_bind] at h
    obtain ⟨b, hb⟩ := (canReturn_lift_bind _ _ _).mp h
    exact (canReturn_lift_bind _ _ _).mpr ⟨b.1, ih b.1 hb⟩

/-- Threading a state through an interpretation of the operations threads it through each
interpreting program. -/
theorem withState_liftM {Q : PFunctor.{uA, uB}} {S : Type uB} (h : (a : P.A) → Q.FreeM (P.B a))
    (x : P.FreeM α) (s : S) :
    (x.liftM h).withState s = (x.withState s).liftM fun b : P.A × S => (h b.1).withState b.2 := by
  induction x generalizing s with
  | pure a => rfl
  | lift_bind a k ih =>
    change ((h a).bind fun b => (k b).liftM h).withState s =
      ((h a).withState s).bind fun b => ((k b.1).withState b.2).liftM _
    simp only [withState_bind, ih]

variable [∀ a, MeasurableSpace (P.B a)] [∀ a, DiscreteMeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : (a : P.A) → Measure (P.B a)}

/-- Each value charged by the output measure is a value the program can return. -/
theorem canReturn_of_toMeasure_singleton_ne_zero {x : P.FreeM α} {a : α}
    (h : x.toMeasure μ {a} ≠ 0) : MonadAttach.CanReturn x a := by
  induction x with
  | pure b => by_contra hab; simp [Ne.symm hab] at h
  | lift_bind op k ih =>
    rw [toMeasure_lift_bind, Measure.bind_apply (measurableSet_singleton a)
      Measurable.of_discrete.aemeasurable, lintegral_countable'] at h
    obtain ⟨b, hb⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr h)
    exact (canReturn_lift_bind _ _ _).mpr ⟨b, ih b (left_ne_zero_of_mul hb)⟩

/-- When every answer is charged, the output measure charges exactly the values the program can
return. -/
theorem toMeasure_singleton_ne_zero_iff (hμ : ∀ op b, μ op {b} ≠ 0) {x : P.FreeM α} {a : α} :
    x.toMeasure μ {a} ≠ 0 ↔ MonadAttach.CanReturn x a := by
  induction x with
  | pure b => by_cases hab : a = b <;> simp [hab, Ne.symm]
  | lift_bind op k ih =>
    rw [toMeasure_lift_bind, Measure.bind_apply (measurableSet_singleton a)
      Measurable.of_discrete.aemeasurable, lintegral_countable', canReturn_lift_bind]
    simp [ENNReal.tsum_eq_zero, ih, hμ]

/-- The output measure is carried by the values the program can return. -/
theorem ae_canReturn_toMeasure [Countable α] {x : P.FreeM α} :
    ∀ᵐ a ∂x.toMeasure μ, MonadAttach.CanReturn x a :=
  ae_iff_of_countable.mpr fun _ => canReturn_of_toMeasure_singleton_ne_zero

end PFunctor.FreeM

namespace Turing.MultiTapePTM

open PFunctor MultiTapeMachine

variable {Oracle : Type}

namespace OracleEnv

variable (env : OracleEnv Oracle) {α β : Type} [MeasurableSpace α]

/-- Continuations that run alike from every value a program can return run alike after it. -/
theorem run_bind_congr {x : (effects Oracle).FreeM β} {f g : β → (effects Oracle).FreeM α}
    (h : ∀ b, MonadAttach.CanReturn x b → ∀ s, env.run (f b) s = env.run (g b) s)
    (s : env.State) : env.run (x >>= f) s = env.run (x >>= g) s := by
  simp only [run, FreeM.withState_bind']
  exact FreeM.toMeasure_bind_congr _ fun p hp => h p.1 (FreeM.canReturn_withState hp) p.2

/-- A run is carried by the values the program can return. -/
theorem ae_canReturn_run [Countable α] [DiscreteMeasurableSpace α] (x : (effects Oracle).FreeM α)
    (s : env.State) : ∀ᵐ p ∂env.run x s, MonadAttach.CanReturn x p.1 :=
  FreeM.ae_canReturn_toMeasure.mono fun _ => FreeM.canReturn_withState

/-- Binding ports to oracles runs the program against the oracles they are bound to. -/
@[simp]
theorem run_liftM_rename {Ports : Type} (dispatch : Ports → Oracle)
    (x : (effects Ports).FreeM α) (s : env.State) :
    env.run (x.liftM (rename dispatch)) s = (env.comap dispatch).run x s := by
  rw [run, FreeM.withState_liftM, FreeM.toMeasure_liftM]
  congr 1
  funext ⟨op, s⟩
  rcases op with _ | ⟨port, word⟩
  · exact env.run_coin s
  · exact env.run_query (dispatch port) word s

/-- Rebinding ports bound to oracles binds them to the composite. -/
@[simp]
theorem run_comap_comap {Ports Ports' : Type} (dispatch : Ports → Oracle) (bind : Ports' → Ports)
    (x : (effects Ports').FreeM α) (s : env.State) :
    ((env.comap dispatch).comap bind).run x s = (env.comap (dispatch ∘ bind)).run x s :=
  rfl

/-- A coin whose value is discarded does not change the run. -/
@[simp]
theorem run_coin_bind_const (x : (effects Oracle).FreeM α) (s : env.State) :
    env.run (coin >>= fun _ => x) s = env.run x s := by
  ext t ht
  rw [run_bind, run_coin, Measure.bind_apply ht Measurable.of_discrete.aemeasurable,
    lintegral_map Measurable.of_discrete measurable_prodMk_right]
  simp only [lintegral_const, measure_univ, mul_one]

/-- A deterministic phase hands its reached tapes to the continuation, discarding its coins and
leaving the state unchanged. -/
theorem run_bind_ofDeterministic {k : ℕ} {State : Type} [DecidableEq Oracle] {input : List Bool}
    (machine : MultiTapeTM k Bool State) (fuel : ℕ) (cfg : Config k Bool State Oracle input)
    (next : Config k Bool State Oracle input → (effects Oracle).FreeM α) (s : env.State) :
    env.run ((ofDeterministic machine).runConfigFrom fuel cfg >>= next) s =
      env.run (next { cfg with tapes := machine.runFrom cfg.tapes fuel }) s := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    rw [runConfigFrom_succ, step_ofDeterministic]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [Option.isNone_none, ↓reduceIte, pure_bind, ih,
        fun n => machine.runFrom_eq_of_halt cfg.tapes (Nat.zero_le n) hs]
    | some control =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
        run_coin_bind_const, ih]
      rw [show fuel + 1 = 1 + fuel by omega, machine.runFrom_add, machine.runFrom_one]

end OracleEnv

namespace Composition

variable {k₀ k₁ ports₀ ports₁ : ℕ} {State₀ State₁ : Type} {input : List Bool}

/-- The charged handoff runs the continuation on the buffered intermediate input. -/
theorem run_continuation (env : OracleEnv (Fin (ports₀ + ports₁))) {α : Type} [MeasurableSpace α]
    (machine : MultiTapePTM k₁ Bool State₁ (Fin ports₁))
    (cfg : Config k₀ Bool State₀ (Fin ports₀) input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime (machine.initialConfig cfg.tapes.output))
    (next : Config (k₁ + k₀ + 2) Bool (MultiTapeTM.PrepareInput.Control ⊕ State₁)
      (Fin (ports₀ + ports₁)) input → (effects (Fin (ports₀ + ports₁))).FreeM α)
    (s : env.State) :
    env.run ((continuation machine k₀ ports₀).runConfigFrom (prepareTime + runTime)
        (Sequential.start (continuation machine k₀ ports₀) (buffer k₁ ports₁ cfg)) >>= next) s =
      env.run ((machine.runConfigFrom runTime (machine.initialConfig cfg.tapes.output)).liftM
          (rename (Fin.natAddEmb ports₀)) >>= fun final =>
            next (Sequential.right (consumerConfig cfg final))) s := by
  change env.run
    (((ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀))).seq
      (consumer machine k₀ ports₀)).runConfigFrom (prepareTime + runTime)
        (Sequential.left (consumer machine k₀ ports₀) (prepareInitial k₁ ports₁ cfg)) >>= next)
      s = _
  rw [runConfigFrom_seq _ _ prepareTime runTime _
    (fun final hfinal => by rw [prepare_canReturn _ _ cfg prepareTime hprepare final hfinal]; rfl)
    (fun final hfinal => by
      rw [prepare_canReturn _ _ cfg prepareTime hprepare final hfinal, prepare_start]
      exact consumer_halts machine cfg runTime hrun), bind_assoc, env.run_bind_ofDeterministic,
    run_preparation _ _ cfg prepareTime hprepare]
  change env.run ((Sequential.right <$> (consumer machine k₀ ports₀).runConfigFrom runTime
      (Sequential.start (consumer machine k₀ ports₀) (prepareFinal k₁ ports₁ cfg))) >>= next) s = _
  rw [prepare_start, runConfigFrom_consumer]
  simp only [bind_map_left]

end Composition

variable {k₀ k₁ ports₀ ports₁ : ℕ} {State₀ State₁ : Type}

/-- Composed machines run as the first machine followed, on its output, by the second, each
through its own ports. -/
theorem OracleEnv.run_comp (env : OracleEnv (Fin (ports₀ + ports₁)))
    (first : MultiTapePTM k₀ Bool State₀ (Fin ports₀))
    (second : MultiTapePTM k₁ Bool State₁ (Fin ports₁)) (input : List Bool)
    (firstTime secondTime : ℕ) (hfirst : first.HaltsWithin firstTime (first.initialConfig input))
    (hsecond : ∀ final,
      MonadAttach.CanReturn (first.runConfigFrom firstTime (first.initialConfig input)) final →
      second.HaltsWithin secondTime (second.initialConfig final.tapes.output))
    (s : env.State) :
    env.run ((first.comp second).run (firstTime + (firstTime + 4 + secondTime)) input) s =
      env.run ((first.run firstTime input).liftM (rename (Fin.castAddEmb ports₁)) >>= fun word =>
        word.elim (pure none) fun word =>
          (second.run secondTime word).liftM (rename (Fin.natAddEmb ports₀))) s := by
  simp only [MultiTapePTM.run, runFrom,
    runConfigFrom_comp first second input firstTime secondTime hfirst hsecond, map_bind,
    FreeM.liftM_map, bind_map_left]
  refine env.run_bind_congr (fun mid hmid s => ?_) s
  have hsource := (canReturn_liftM_rename _ _ _).mp hmid
  have houtput : output? mid = some mid.tapes.output := by simp [output?, hfirst mid hsource]
  rw [houtput]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  rw [Composition.run_continuation env second mid (firstTime + 4) secondTime
    (Nat.add_le_add_right (composition_output_bound first input firstTime mid hsource) 4)
    (hsecond mid hsource)]
  simp only [Sequential.output?_right]
  rfl

section IsPPT

open MultiTapeTM

/-- Stateless answers charging every word charge every response. -/
theorem OracleEnv.statelessMeasure_singleton_ne_zero {answer : Oracle → Word → Measure Word}
    (h : ∀ oracle word word', answer oracle word {word'} ≠ 0) (op : (effects Oracle).A)
    (b : (effects Oracle).B op) : OracleEnv.statelessMeasure answer op {b} ≠ 0 := by
  rcases op with ⟨⟨⟩⟩ | ⟨oracle, word⟩
  · change (uniformOn Set.univ : Measure Bool) {b} ≠ 0
    rw [uniformOn_univ, Measure.count_singleton]
    simp
  · exact h oracle word b

variable {k : ℕ} {State Ports α β γ : Type} [DecidableEq Ports]
  {machine : MultiTapePTM k Bool State Ports} {dispatch : Ports → Oracle} {fuel : ℕ}
  {input : Word} {encode : α ↪ Word} {program : (effects Oracle).FreeM α}

/-- A realizing machine can output exactly the encodings of the values the program can return. -/
theorem Realizes.canReturn_iff (h : machine.Realizes dispatch fuel input encode program)
    {word : Word} : MonadAttach.CanReturn (machine.run fuel input) (some word) ↔
      ∃ a, MonadAttach.CanReturn program a ∧ encode a = word := by
  have hcount {Oracle : Type} := OracleEnv.statelessMeasure_singleton_ne_zero (Oracle := Oracle)
    (answer := fun _ _ => Measure.count) fun _ _ _ => by simp
  have heq := h.toMeasure_eq fun _ _ => Measure.count
  simp only [Function.comp_def] at heq
  rw [← FreeM.toMeasure_singleton_ne_zero_iff hcount, heq,
    FreeM.toMeasure_singleton_ne_zero_iff hcount]
  simp

open Cslib in
/-- Polynomial-time programs compose, sharing the oracles and their state. -/
theorem IsPPT.bind {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {first : α → (effects Oracle).FreeM β} {second : β → (effects Oracle).FreeM γ}
    (hfirst : IsPPT input (fun _ => middle) first)
    (hsecond : IsPPT middle (fun _ => output) second) :
    IsPPT input (fun _ => output) fun a => first a >>= second := by
  obtain ⟨hfin, k₀, ports₀, State₀, _, source, dispatch₀, c₀, d₀, h₀⟩ := hfirst
  obtain ⟨-, k₁, ports₁, State₁, _, target, dispatch₁, c₁, d₁, h₁⟩ := hsecond
  let : MeasurableSpace β := ⊤
  have : Countable β := middle.injective.countable
  set t₀ := fun n : ℕ => c₀ * (n + 1) ^ d₀
  set t₁ := fun n : ℕ => c₁ * (n + 1) ^ d₁
  obtain ⟨c, d, hle⟩ : PolynomiallyBounded fun n => t₀ n + (t₀ n + 4 + t₁ (t₀ n)) := by
    simp only [t₀, t₁]
    fun_prop
  have hnext a b (hb : MonadAttach.CanReturn (first a) b) :
      target.HaltsWithin (t₁ (t₀ (input a).length)) (target.initialConfig (middle b)) ∧
        target.Realizes dispatch₁ (t₁ (t₀ (input a).length)) (middle b) output (second b) := by
    have hle : t₁ (middle b).length ≤ t₁ (t₀ (input a).length) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right
        (length_of_canReturn_run _ _ _ _ ((h₀ a).2.canReturn_iff.mpr ⟨b, hb, rfl⟩)) 1) _)
    exact ⟨(h₁ b).1.mono hle, (h₁ b).2.mono (h₁ b).1 hle⟩
  have hcont a cfg (hcfg : MonadAttach.CanReturn
      (source.runConfigFrom (t₀ (input a).length) (source.initialConfig (input a))) cfg) :
      target.HaltsWithin (t₁ (t₀ (input a).length)) (target.initialConfig cfg.tapes.output) := by
    obtain ⟨b, hb, hword⟩ := (h₀ a).2.canReturn_iff.mp
      ((FreeM.canReturn_map' _ _ (some cfg.tapes.output)).mpr
        ⟨cfg, hcfg, by simp [output?, (h₀ a).1 cfg hcfg]⟩)
    exact hword ▸ (hnext a b hb).1
  have hhalt a := (h₀ a).1.comp (hcont a)
  refine ⟨hfin, k₁ + k₀ + 2, ports₀ + ports₁, _, inferInstance, source.comp target,
    Fin.addCases dispatch₀ dispatch₁, c, d, fun a => ⟨(hhalt a).mono (hle _), ?_⟩⟩
  refine Realizes.mono (fun env s => ?_) (hhalt a) (hle _)
  have hleft : Fin.addCases dispatch₀ dispatch₁ ∘ Fin.castAddEmb ports₁ = dispatch₀ :=
    funext fun _ => by simp
  have hright : Fin.addCases dispatch₀ dispatch₁ ∘ Fin.natAddEmb ports₀ = dispatch₁ :=
    funext fun _ => by simp
  rw [OracleEnv.run_comp _ _ _ _ _ _ (h₀ a).1 (hcont a), OracleEnv.run_bind,
    OracleEnv.run_liftM_rename, OracleEnv.run_comap_comap, hleft, (h₀ a).2 env s,
    OracleEnv.run_map,
    ← Measure.bind_dirac_eq_map _ Measurable.of_discrete,
    Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable,
    map_bind, OracleEnv.run_bind]
  refine Measure.bind_congr_right ?_
  filter_upwards [env.ae_canReturn_run (first a) s] with p hp
  rw [Measure.dirac_bind Measurable.of_discrete]
  simp only [Prod.map, id, Option.elim_some, OracleEnv.run_liftM_rename,
    OracleEnv.run_comap_comap]
  rw [hright]
  exact (hnext a p.1 hp).2 env p.2

/-- Deterministic polynomial-time functions are probabilistic polynomial-time programs. -/
theorem _root_.Turing.MultiTapeTM.IsPolyTime.isPPT [Finite Oracle] {input : α ↪ Word}
    {output : β ↪ Word} {f : α → β} (h : IsPolyTime input fun a => output (f a)) :
    IsPPT input (fun _ => output) fun a => (pure (f a) : (effects Oracle).FreeM β) := by
  obtain ⟨k, State, _, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, 0, State, inferInstance, ofDeterministic machine, Fin.elim0, c, d,
    fun a => ⟨fun cfg hcfg => ?_, fun env s => ?_⟩⟩
  · rw [canReturn_ofDeterministic _ _ _ _ hcfg]
    exact (h a).1
  · obtain ⟨hhalt, hout⟩ := h a
    rw [MultiTapePTM.run, runFrom, ← bind_pure_comp, OracleEnv.run_bind_ofDeterministic]
    simp only [output?, tapes_initialConfig_ofDeterministic, hhalt, hout, Option.isNone_none,
      ↓reduceIte, OracleEnv.run_pure, map_pure]

/-- A deterministic polynomial-time function may process a probabilistic result. -/
theorem IsPPT.map {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : α → (effects Oracle).FreeM β} {f : β → γ}
    (hprogram : IsPPT input (fun _ => middle) program)
    (hf : IsPolyTime middle fun b => output (f b)) :
    IsPPT input (fun _ => output) fun a => f <$> program a :=
  have := hprogram.1
  by simpa only [bind_pure_comp] using hprogram.bind hf.isPPT

/-- A deterministic polynomial-time function may prepare a probabilistic program's input. -/
theorem IsPPT.comp {input : α ↪ Word} {middle : β ↪ Word} {output : γ ↪ Word}
    {program : β → (effects Oracle).FreeM γ} {f : α → β}
    (hprogram : IsPPT middle (fun _ => output) program)
    (hf : IsPolyTime input fun a => middle (f a)) :
    IsPPT input (fun _ => output) fun a => program (f a) :=
  have := hprogram.1
  by simpa only [pure_bind] using hf.isPPT.bind hprogram

end IsPPT

end Turing.MultiTapePTM
