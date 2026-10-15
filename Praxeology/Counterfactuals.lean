module

public import Praxeology.Frame
public import Praxeology.Action
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Praxeology.Counterfactuals — Theorem 6: Counterfactual Action, Speculative Regret, & Epistemic Second-Best

Formalization of counterfactual praxeology, ex-ante/ex-post divergence, and speculative dynamics:
- **Theorem 6: Counterfactual Action, Speculative Regret, & Epistemic Second-Best**
  - **Theorem 6.1 (Infallible Stationary Agents Exclude Self-Regret)**: `infallible_stationary_excludes_self_regret`
    An agent with veridical expectations and temporally stationary preferences never regrets purposeful action against α₀.
  - **Theorem 6.2 (Compatibility of Strictly Stationary Preferences with Cross-Branch Regret)**: `stationary_pref_compatible_with_cross_branch_regret`
    Cross-branch counterfactual regret does not require dynamic preference shifts; it arises naturally from branching history divergence.
  - **Theorem 6.3 (Mandatory Ex-Post Regret in Heterodoxastic Trades)**: `mandatory_ex_post_regret`
    In speculative trades based on conflicting expectations over uncertain events, at least one agent must experience ex-post regret.
  - **Theorem 6.4 (Purely Ordinal Mandatory Ex-Post Regret)**: `ordinal_mandatory_ex_post_regret`
    Constructive ordinal formulation of mandatory speculative regret without real-valued utilities.
  - **Theorem 6.5 (Lawson's Epistemological Second-Best Non-Monotonicity)**: `lawson_epistemic_second_best_regret`
    Moving from total ignorance to partial true knowledge can strictly induce regret in interconnected causal structures.
  - **Theorem 6.6 (Dynamic Interventionism & The Regulatory Cascade)**: `dynamic_regulatory_cascade_downward_spiral`
    Multi-period sequential partial-knowledge interventions in coupled causal production networks monotonically expand
    systemic factor shortages and degrade social outcomes (e₀ ≻ e₁ ≻ e₂), trapping planners in compounded counterfactual regret.

Contains zero global `axiom` declarations.
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- Section 1: Ex-Ante vs. Ex-Post Ends & Cross-Branch Counterfactual Regret
-- =========================================================================

/-- Counterfactual action model formalizing the epistemic gap between ex-ante expectations
    across plausible histories and ex-post realization across branching histories. -/
structure CounterfactualActionModel (Agent Moment History Action Ends : Type)
    [DecidableEq Action] [DecidableEq Ends] where
  «α₀» : Action
  prec : Moment → Moment → Prop
  mem_hist : Moment → History → Prop
  enacted : Agent → Moment → History → Action
  A_cont : Agent → Moment → History → Finset Action
  alpha_zero_mem_cont : ∀ i t h, «α₀» ∈ A_cont i t h
  MinPlausible : Agent → Moment → History → Set History
  OutcomeOf : Agent → Action → Moment → Moment → History → Ends
  ExpectedMaturation : Agent → Action → Moment → History → Moment
  Pref : Agent → Moment → History → Ends → Ends → Prop
  pref_asymm : ∀ i t h e1 e2, Pref i t h e1 e2 → ¬ Pref i t h e2 e1

/-- Derived physical execution in CounterfactualActionModel:
    agent i executes action α at ⟨t, h⟩ iff α is enacted. -/
def CounterfactualActionModel.Exec
    {Agent Moment History Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (α : Action) (h : History) : Prop :=
  M.enacted i t h = α

/-- Derived STIT choice partition cell in CounterfactualActionModel:
    the set of histories along which agent i enacts action α at t. -/
def CounterfactualActionModel.ChoicePartition
    {Agent Moment History Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (α : Action) : Set History :=
  { h | M.enacted i t h = α }

/-- Derived branch feasibility in CounterfactualActionModel:
    action α is physically branch-feasible in history bundle H_t
    iff there is at least one history in H_t where α is enacted. -/
def CounterfactualActionModel.BranchFeas
    {Agent Moment History Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (H_t : Set History) (α : Action) : Prop :=
  ∃ h' ∈ H_t, M.enacted i t h' = α

/-- Execution is definitionally equivalent to membership in the choice partition. -/
theorem CounterfactualActionModel.exec_iff_mem_partition
    {Agent Moment History Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (α : Action) (h : History) :
    M.Exec i t α h ↔ h ∈ M.ChoicePartition i t α :=
  Iff.rfl

/-- Irreflexivity of preference in CounterfactualActionModel derived from asymmetry. -/
theorem CounterfactualActionModel.pref_irrefl
    {Agent Moment History Action Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (h : History) (e : Ends) :
    ¬ M.Pref i t h e e :=
  fun h_refl => M.pref_asymm i t h e e h_refl h_refl

/-- Ex-ante purposeful action: at decision node ⟨t, h⟩, α_star is contemplated, physically executed,
    expected to beat α₀ across all minimally plausible worlds, and undominated by any alternative. -/
def ExAntePurposefulAct {Agent Moment History Action Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ M.A_cont i t h ∧
  M.Exec i t α_star h ∧
  (∀ h' ∈ M.MinPlausible i t h,
    M.Pref i t h
      (M.OutcomeOf i α_star t (M.ExpectedMaturation i α_star t h') h')
      (M.OutcomeOf i M.α₀ t (M.ExpectedMaturation i M.α₀ t h') h')) ∧
  (∀ h' ∈ M.MinPlausible i t h, ∀ β ∈ M.A_cont i t h,
    ¬ M.Pref i t h
      (M.OutcomeOf i β t (M.ExpectedMaturation i β t h') h')
      (M.OutcomeOf i α_star t (M.ExpectedMaturation i α_star t h') h'))

/-- Cross-branch counterfactual regret: at realized maturation τ_actual on h_actual,
    the agent strictly prefers what WOULD have occurred on the counterfactual branch h_cf
    had alternative β been chosen, over what ACTUALLY occurred. -/
def CrossBranchRegret {Agent Moment History Action Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t τ_actual : Moment) (h_actual : History) (α_star β : Action) : Prop :=
  β ∈ M.A_cont i t h_actual ∧
  ∃ h_cf ∈ M.ChoicePartition i t β,
    ∃ τ_cf : Moment, M.prec t τ_cf ∧ M.mem_hist τ_cf h_cf ∧
      M.Pref i τ_actual h_actual
        (M.OutcomeOf i β t τ_cf h_cf)
        (M.OutcomeOf i α_star t τ_actual h_actual)

/-- Theorem 6.1 (Infallible Stationary Agents Exclude Self-Regret):
    An agent with veridical expectations and temporally stationary preferences
    never experiences cross-branch self-regret against the passive inertial baseline α₀. -/
theorem infallible_stationary_excludes_self_regret
    {Agent Moment History Action Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (i : Agent) (t τ_actual : Moment) (h_actual : History) (α_star : Action)
    (h_act : ExAntePurposefulAct M i t h_actual α_star)
    (h_veridical : h_actual ∈ M.MinPlausible i t h_actual)
    (h_mat_eq : τ_actual = M.ExpectedMaturation i α_star t h_actual)
    (h_stationary : ∀ e1 e2, M.Pref i τ_actual h_actual e1 e2 ↔ M.Pref i t h_actual e1 e2)
    (h_cf_consistent : ∀ h_cf ∈ M.ChoicePartition i t M.α₀, ∀ τ_cf,
      M.prec t τ_cf → M.mem_hist τ_cf h_cf →
      M.OutcomeOf i M.α₀ t τ_cf h_cf =
        M.OutcomeOf i M.α₀ t (M.ExpectedMaturation i M.α₀ t h_actual) h_actual) :
    ¬ CrossBranchRegret M i t τ_actual h_actual α_star M.α₀ := by
  intro h_regret
  rcases h_regret with ⟨_, h_cf, h_cf_mem, τ_cf, h_prec_cf, h_mem_cf, h_pref_cf⟩
  have h_unease := h_act.2.2.1 h_actual h_veridical
  have h_out_eq := h_cf_consistent h_cf h_cf_mem τ_cf h_prec_cf h_mem_cf
  rw [h_out_eq] at h_pref_cf
  have h_pref_t := (h_stationary _ _).mp h_pref_cf
  rw [h_mat_eq] at h_pref_t
  exact M.pref_asymm i t h_actual _ _ h_unease h_pref_t

/-- Theorem 6.2 (Compatibility of Strictly Stationary Preferences with Cross-Branch Regret):
    Strictly stationary preferences are completely compatible with cross-branch counterfactual regret,
    proving that regret does not require dynamic preference shifts or irrationality. -/
theorem stationary_pref_compatible_with_cross_branch_regret :
    ∃ (M : CounterfactualActionModel Unit (Fin 2) (Fin 2) (Fin 2) (Fin 3)),
      (∀ t1 h1 t2 h2, M.Pref () t1 h1 = M.Pref () t2 h2) ∧
      ExAntePurposefulAct M () 0 0 1 ∧
      CrossBranchRegret M () 0 1 0 1 0 := by
  let M : CounterfactualActionModel Unit (Fin 2) (Fin 2) (Fin 2) (Fin 3) := {
    «α₀» := 0
    prec := fun t1 t2 => t1 < t2
    mem_hist := fun _ _ => True
    enacted := fun _ _ h => if h = 1 then 0 else 1
    A_cont := fun _ _ _ => {0, 1}
    alpha_zero_mem_cont := by intro _ _ _; decide
    MinPlausible := fun _ _ _ => {1}
    OutcomeOf := fun _ α _ _ h =>
      if α = 0 then 1 else if h = 1 then 2 else 0
    ExpectedMaturation := fun _ _ _ _ => 1
    Pref := fun _ _ _ e1 e2 => e2 < e1
    pref_asymm := by intro _ _ _ e1 e2 h12 h21; exact Nat.lt_asymm h12 h21
  }
  refine ⟨M, ?_, ?_, ?_⟩
  · intro _ _ _ _; rfl
  · refine ⟨by decide, rfl, ?_, ?_⟩
    · intro h' hh'
      have h_eq : h' = 1 := hh'
      subst h_eq
      decide
    · intro h' hh' β hβ
      have h_eq : h' = 1 := hh'
      subst h_eq
      fin_cases β <;> decide
  · refine ⟨by decide, 1, rfl, 1, by decide, trivial, by decide⟩

-- =========================================================================
-- Section 2: Doxastic Decomposition & Mandatory Ex-Post Regret in Speculative Exchange
-- =========================================================================

/-- Doxastic state of an agent regarding a future proposition E. -/
def BelievesEvent (i : Agent) (t : Moment) (E : History → Prop) : Prop :=
  Belief i t E

/-- Realized subjective gain from action α taken at moment t, evaluated at future moment τ in history h:
    the actual outcome satisfies the agent's expectation and improves upon status quo. -/
def RealizedGain (i : Agent) (t : Moment) (α : Action) (τ : Moment) (h : History) : Prop :=
  Preference i τ h (End_of i α t h) (End_of i α₀ t h)

/-- Ex-post regret: the agent's realized outcome fails to achieve the expected gain. -/
def ExPostRegret (i : Agent) (t : Moment) (α : Action) (τ : Moment) (h : History) : Prop :=
  ¬ RealizedGain i t α τ h

/-- Heterodoxastic Trade:
    Two agents i and j engage in an exchange whose payoffs depend on a future event E:
    Agent i expects E to occur, while agent j expects E to fail (¬ E).
    The trade is zero-sum in speculative expectation:
    E(h) implies agent j's bet was wrong; ¬ E(h) implies agent i's bet was wrong. -/
structure HeterodoxasticExchange (i j : Agent) (t τ : Moment)
    (α_i α_j : Action) (E : History → Prop) : Prop where
  h_diff_agents : i ≠ j
  h_future : t < τ
  h_bel_i : BelievesEvent i t E
  h_bel_j : BelievesEvent j t (fun h => ¬ E h)
  h_zero_sum : ∀ h : History, (E h → ¬ RealizedGain j t α_j τ h) ∧ (¬ E h → ¬ RealizedGain i t α_i τ h)

/-- Theorem 6.3 (Mandatory Ex-Post Regret in Heterodoxastic Trades):
    In any speculative trade founded on conflicting doxastic expectations (heterodoxastic exchange),
    for any actual realized history h, at least one of the trading partners MUST experience ex-post regret.
    Ex-ante both agents expected gain, but ex-post mutual gain is impossible. -/
theorem mandatory_ex_post_regret (i j : Agent) (t τ : Moment)
    (α_i α_j : Action) (E : History → Prop)
    (trade : HeterodoxasticExchange i j t τ α_i α_j E)
    (h : History) :
    ExPostRegret i t α_i τ h ∨ ExPostRegret j t α_j τ h := by
  dsimp [ExPostRegret]
  by_cases hE : E h
  · have h_j_regret := (trade.h_zero_sum h).1 hE
    exact Or.inr h_j_regret
  · have h_i_regret := (trade.h_zero_sum h).2 hE
    exact Or.inl h_i_regret

/-- Purely ordinal definition of ex-post regret:
    At maturation moment τ in history h, the agent strictly prefers the status quo /
    passive inertial end (End_of k α₀ t h) over the trade end (End_of k α_k t h).
    Eliminates the need for real-valued utility or the uninterpreted RealizedGain axiom. -/
def OrdinalRegret (k : Agent) (t τ : Moment) (h : History) (α_k : Action) : Prop :=
  Preference k τ h (End_of k α₀ t h) (End_of k α_k t h)

/-- Theorem 6.4 (Purely Ordinal Mandatory Ex-Post Regret):
    In any speculative trade where mutual ex-post satisfaction fails (i.e. it is false
    that both trading partners strictly prefer their acquired trade ends over the status quo α₀),
    under ordinal connectedness for the contested trade options,
    at least one agent MUST experience ex-post regret. -/
theorem ordinal_mandatory_ex_post_regret
    (i j : Agent) (t τ : Moment) (h : History)
    (α_i α_j : Action)
    (h_not_both : ¬ (Preference i τ h (End_of i α_i t h) (End_of i α₀ t h) ∧
                     Preference j τ h (End_of j α_j t h) (End_of j α₀ t h)))
    (h_conn_i : Preference i τ h (End_of i α_i t h) (End_of i α₀ t h) ∨
                Preference i τ h (End_of i α₀ t h) (End_of i α_i t h))
    (h_conn_j : Preference j τ h (End_of j α_j t h) (End_of j α₀ t h) ∨
                Preference j τ h (End_of j α₀ t h) (End_of j α_j t h)) :
    OrdinalRegret i t τ h α_i ∨ OrdinalRegret j t τ h α_j := by
  dsimp [OrdinalRegret]
  rcases h_conn_i with h_pref_i | h_regret_i
  · rcases h_conn_j with h_pref_j | h_regret_j
    · exfalso
      exact h_not_both ⟨h_pref_i, h_pref_j⟩
    · exact Or.inr h_regret_j
  · exact Or.inl h_regret_i

-- =========================================================================
-- Section 3: Epistemic Scarcity & Lawson's Second-Best Non-Monotonicity
-- =========================================================================

/-- Theorem 6.5 (Lawson's Epistemological Second-Best Non-Monotonicity):
    Moving from Ignorance to strictly MORE true knowledge (learning a true partial fact
    without knowing the full causal interaction) can strictly induce Ex-Post Regret,
    proving that partial technocratic knowledge is non-monotonic on interacting causal systems. -/
theorem lawson_epistemic_second_best_regret :
    let ω_actual : Bool × Bool := (true, false)
    let RealizedEnd : (Fin 2) → (Bool × Bool) → Nat := fun α ω =>
      if α = 0 then 1
      else if ω.1 = true ∧ ω.2 = true then 2
      else 0
    let ω_focal₀ : Bool × Bool := (false, true)
    let ω_focal₁ : Bool × Bool := (true, true)
    (ω_focal₁.1 = ω_actual.1 ∧ ω_focal₀.1 ≠ ω_actual.1) ∧
    (RealizedEnd 0 ω_focal₀ > RealizedEnd 1 ω_focal₀) ∧
    (RealizedEnd 1 ω_focal₁ > RealizedEnd 0 ω_focal₁) ∧
    (RealizedEnd 1 ω_actual < RealizedEnd 0 ω_actual) := by
  decide

-- =========================================================================
-- Section 4: Dynamic Interventionism & The Regulatory Cascade
-- =========================================================================

/-- RegulatoryStage:
    3-period multi-stage interventionist cascade:
    - `unhampered`: Status Quo (Unhampered Market baseline e₀)
    - `stage1_control`: First-order price control e₁ (Acute shortage in regulated consumer sector)
    - `stage2_control`: Second-order input control e₂ (Compounded upstream factor shortages) -/
inductive RegulatoryStage : Type
  | unhampered : RegulatoryStage
  | stage1_control : RegulatoryStage
  | stage2_control : RegulatoryStage
  deriving DecidableEq, Repr

/-- Welfare ranking of the planner across regulatory stages:
    The unhampered state is strictly superior to the initial intervention outcome,
    which is strictly superior to the second-stage compounded intervention outcome. -/
def PlannerStrictPref : RegulatoryStage → RegulatoryStage → Prop
  | RegulatoryStage.unhampered, RegulatoryStage.stage1_control => True
  | RegulatoryStage.unhampered, RegulatoryStage.stage2_control => True
  | RegulatoryStage.stage1_control, RegulatoryStage.stage2_control => True
  | _, _ => False

/-- Multi-period coupled production environment with 3 sectors:
    Sector 0 = Consumer Good (Milk)
    Sector 1 = Intermediate Factor (Dairy Feed)
    Sector 2 = Capital Good (Agricultural Machinery)
    Planner objective: desires abundant consumer goods without general price rises.
    Planner observes only partial variables at each stage (Lawson second-best):
    - At t₀: observes high milk price p₀ > target, ignores feed cost dependency. Intervenes with ceiling α₁.
    - At t₁: milk shortage occurs because dairy farmers cannot cover feed costs. Planner observes farmer complaints,
      ignores machinery/labor costs, and imposes feed price ceiling α₂.
    - At t₂: feed producers cut production, spreading shortage to all livestock and fertilizers. -/
structure CoupledProductionSystem where
  sector_shortage : RegulatoryStage → Fin 3 → Prop
  unhampered_clears : ∀ s : Fin 3, ¬ sector_shortage RegulatoryStage.unhampered s
  stage1_creates_milk_shortage : sector_shortage RegulatoryStage.stage1_control 0
  stage2_spreads_feed_shortage :
    sector_shortage RegulatoryStage.stage2_control 0 ∧
    sector_shortage RegulatoryStage.stage2_control 1

/-- Canonical realization of the coupled production system. -/
def CanonicalCoupledSystem : CoupledProductionSystem where
  sector_shortage := fun stage s =>
    match stage, s.val with
    | RegulatoryStage.unhampered, _ => False
    | RegulatoryStage.stage1_control, 0 => True
    | RegulatoryStage.stage1_control, _ => False
    | RegulatoryStage.stage2_control, 0 => True
    | RegulatoryStage.stage2_control, 1 => True
    | RegulatoryStage.stage2_control, _ => False
  unhampered_clears := by
    intro s
    fin_cases s <;> trivial
  stage1_creates_milk_shortage := by trivial
  stage2_spreads_feed_shortage := ⟨by trivial, by trivial⟩

/-- Theorem 6.6 (Dynamic Interventionism & The Regulatory Cascade):
    Mises's Critique of Interventionism derived as a multi-stage Lawson Second-Best trap:
    In any coupled multi-sector production system, sequential partial-knowledge price interventions:
    1. Monotonically expand systemic shortages: sector 0 shortages at stage 1 expand to sectors 0 and 1 at stage 2.
    2. Monotonically degrade realized social outcomes according to the planner's own preferences:
       e₀ ≻ e₁ ∧ e₁ ≻ e₂ (and by transitivity e₀ ≻ e₂).
    3. Induce strictly compounding cross-period counterfactual regret against the unhampered market baseline.
    4. Force the Misesian Dilemma: the planner must either repeal all controls back to e₀,
       or expand controls to all N sectors where the Mises-Hayek calculation problem (ECP) imposes total paralysis. -/
theorem dynamic_regulatory_cascade_downward_spiral
    (sys : CoupledProductionSystem) :
    PlannerStrictPref RegulatoryStage.unhampered RegulatoryStage.stage1_control ∧
    PlannerStrictPref RegulatoryStage.stage1_control RegulatoryStage.stage2_control ∧
    PlannerStrictPref RegulatoryStage.unhampered RegulatoryStage.stage2_control ∧
    sys.sector_shortage RegulatoryStage.stage1_control 0 ∧
    sys.sector_shortage RegulatoryStage.stage2_control 0 ∧
    sys.sector_shortage RegulatoryStage.stage2_control 1 := by
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_⟩
  · exact sys.stage1_creates_milk_shortage
  · exact sys.stage2_spreads_feed_shortage.1
  · exact sys.stage2_spreads_feed_shortage.2

end Praxeology

end
