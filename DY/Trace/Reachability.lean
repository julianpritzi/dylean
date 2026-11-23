module

public import DY.Trace.Monad
public meta import DY.Meta.CombineMacro

namespace DY

variable [ExecTraceTypes]

public
structure ReachabilityConfig where
  Input: Type
  PreCond: Input → ExecTrace → Prop
  step: Input → (Output: Type) × Traceful Output

public
abbrev ReachabilityConfig.make
  {α β: Type}
  (step: α → Traceful β)
  : ReachabilityConfig
where
  Input := α
  PreCond _ _ := True
  step x := ⟨ _, step x ⟩

@[expose]
public
def ReachabilityConfig.combine {α: Type} (configs: α → ReachabilityConfig): ReachabilityConfig where
  Input := (x: α) × (configs x).Input
  PreCond := fun ⟨ x, inp ⟩ tr => (configs x).PreCond inp tr
  step := fun ⟨ x, inp ⟩ => (configs x).step inp

public
class ReachabilityConfig.HasStep (config1: ReachabilityConfig) (config2: semiOutParam ReachabilityConfig) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step: ∀ input, config1.step input = config2.step (inj input)

public
class ReachabilityConfig.Has (config1 config2: ReachabilityConfig) where
  inj: config1.Input → config2.Input
  pf_pre: ∀ input tr, config1.PreCond input tr = config2.PreCond (inj input) tr
  pf_step (config1 config2): ∀ input, config1.step input = config2.step (inj input)

public
instance instReachabilityConfigHasItself
  (config: ReachabilityConfig)
  : ReachabilityConfig.Has config config
where
  inj x := x
  pf_pre input tr := by simp
  pf_step input := by simp

public
instance instReachabilityConfigHasStep
  (config1 config2 config3: ReachabilityConfig)
  [inst12: ReachabilityConfig.HasStep config1 config2]
  [inst23: ReachabilityConfig.Has config2 config3]
  : ReachabilityConfig.Has config1 config3
where
  inj x := inst23.inj (inst12.inj x)
  pf_pre input tr := by simp [inst23.pf_pre, inst12.pf_pre]
  pf_step input := by simp [inst23.pf_step, inst12.pf_step]

public
instance instReachabilityConfigCombineHasStep
  {α: Type}
  (configs: α → ReachabilityConfig)
  (id: α)
  : ReachabilityConfig.HasStep (configs id) (.combine configs)
where
  inj x := ⟨ id, x ⟩
  pf_pre input tr := by simp [ReachabilityConfig.combine]
  pf_step input := by simp [ReachabilityConfig.combine]

public
inductive Trace.Reachable (config: ReachabilityConfig): ExecTrace → Prop where
  | Base:
    Trace.Reachable config Trace.nil
  | Step:
    {tr: ExecTrace} →
    (input: config.Input) →
    config.PreCond input tr →
    Trace.Reachable config tr →
    Trace.Reachable config (((config.step input).snd).run tr).snd

/-- Every position of a reachable trace lies inside a reachable truncation of
    it: the run could have stopped at the step boundary just after that point.

    A step can only extend the trace -- `Traceful` carries `trIn ≤ trOut` in its
    type -- so the truncation is reachable by the same steps. This is what lets
    a guarantee stated over the whole trace be read as a guarantee that already
    holds by the time its trigger occurs. -/
public
theorem Trace.Reachable.exists_prefix_containing
  {config: ReachabilityConfig} {tr: ExecTrace}
  (h: tr.Reachable config)
  : ∀ i, i < tr.length →
      ∃ n, i < n ∧ n ≤ tr.length ∧ (tr.prefix n).Reachable config
:= by
  induction h with
  | Base => intro i hi; rw [Trace.length_nil] at hi; omega
  | @Step tr0 input hpre hreach ih =>
    intro i hi
    have hle := ((((config.step input).snd).run tr0).snd).property
    by_cases hlt : i < tr0.length
    · obtain ⟨n, hin, hnle, hn⟩ := ih i hlt
      refine ⟨n, hin, Nat.le_trans hnle (Trace.length_le _ _ hle), ?_⟩
      rw [Trace.prefix_of_le hle n hnle]
      exact hn
    · refine ⟨_, hi, Nat.le_refl _, ?_⟩
      rw [Trace.prefix_eq]
      exact Trace.Reachable.Step input hpre hreach

-- Weakest Precondition
@[expose]
public
def Traceful.PreservesReachabilityFrom
  {a: Type}
  (config: ReachabilityConfig)
  (f: Traceful a)
  (post: a → ExecTrace → Prop)
  (tr: ExecTrace): Prop
:=
  let (optRes, trOut) := Traceful.run f tr
  Trace.Reachable config trOut ∧
  match optRes with
  | none => True
  | some res => post res trOut

-- Hoare Triple
@[expose]
public
def Traceful.PreservesReachability
  {a: Type}
  (config: ReachabilityConfig)
  (f: Traceful a)
  (pre: ExecTrace → Prop)
  (post: a → ExecTrace → Prop)
  : Prop
:=
  ∀ tr,
    tr.Reachable config →
    pre tr →
    f.PreservesReachabilityFrom config post tr

public
theorem Traceful.PreservesReachabilityFrom_bind
  {a b: Type}
  (config: ReachabilityConfig)
  (x: Traceful a) (f: a → Traceful b)
  (postF: b → ExecTrace → Prop)
  (preX: ExecTrace → Prop)
  (postX: a → ExecTrace → Prop)
  (tr: ExecTrace)
  (h_x: x.PreservesReachability config preX postX)
  (h_tr_reachable: tr.Reachable config)
  (h_pre_x: preX tr)
  (h_f: ∀ x':a, ∀ trMid: ExecTrace,
      postX x' trMid →
      trMid.Reachable config →
      tr ≤ trMid →
      (f x').PreservesReachabilityFrom config postF trMid
  )
  : (x >>= f).PreservesReachabilityFrom config postF tr
:= by
  simp_all only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, Traceful.run_bind]
  grind

public
theorem Traceful.PreservesReachability_base
  (subConfig config: ReachabilityConfig)
  [ReachabilityConfig.Has subConfig config]
  (input: subConfig.Input)
  : (subConfig.step input).snd.PreservesReachability config (subConfig.PreCond input) (fun _ _ => True)
:= by
  dsimp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom]
  intro tr h_reach h_pre
  apply And.intro
  · rewrite [ReachabilityConfig.Has.pf_step subConfig config]
    apply Trace.Reachable.Step (ReachabilityConfig.Has.inj input) <;>
    grind [ReachabilityConfig.Has.pf_pre]
  · grind

public
theorem Traceful.PreservesReachabilityFrom_pure
  {α: Type}
  (config: ReachabilityConfig)
  (x: α)
  (tr: ExecTrace)
  (post: α → ExecTrace → Prop)
  : tr.Reachable config →
    post x tr →
    (pure x: Traceful α).PreservesReachabilityFrom config post tr
:= by
  simp only [Traceful.PreservesReachabilityFrom, Traceful.run_pure]
  grind

public
theorem Traceful.PreservesReachability_to_Reachable
  {a: Type}
  {config: ReachabilityConfig}
  {f: Traceful a}
  {pre: ExecTrace → Prop}
  {post: a → ExecTrace → Prop}
  (h: f.PreservesReachability config pre post)
  : pre Trace.nil →
    (f.run Trace.nil).snd.val.Reachable config
:= by
  simp_all [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom]
  have := h Trace.nil (.Base)
  grind

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $_options* ReachabilityConfig $params* from $sources,*) => do
    let sources := sources.getElems

    let combined ← combineExplicit params sources {
      name := `reachability
      combineName := ``DY.ReachabilityConfig.combine
      internalOutTypeStx := fun _ _ => `(term| ReachabilityConfig)
      outTypeStx := fun _ => `(term| ReachabilityConfig)
    }

    let hasStep ← mkHasStep params sources <| .makeSimple {
      name := `reachability
      combineName := ``DY.ReachabilityConfig.combine
      hasStepName := ``DY.ReachabilityConfig.HasStep
    }

    return Lean.mkNullNode (combined ++ hasStep)

end Meta.CombineMacro

end DY
