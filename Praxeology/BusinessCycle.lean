module

public import Praxeology.Frame
public import Praxeology.Counterfactuals
public import Praxeology.FirmBoundary
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false

/-!
# Praxeology.BusinessCycle — Theorem 8: Austrian Business Cycle Theory (ABCT)

Formalization of the monetary-macroeconomic dynamics of praxeology:
- **Theorem 8: The Austrian Business Cycle Theory (ABCT) & Synchronized Cluster of Errors**
  - **Theorem 8.1 (Artificial Credit Expansion Distorts Intertemporal Valuation)**: `credit_expansion_distorts_stage_valuation`
    Artificially lowered discount rates ι_credit induce present-value overestimation of higher-order capital stages,
    making unviable projects appear profitable against the natural rate ι_nat.
  - **Theorem 8.2 (Strategic Opacity Traps DEL Epistemic Update)**: `strategic_opacity_traps_del_update`
    When credit expansion mimics genuine savings signals, the agent's signal-filtered plausibility set retains
    unsustainable expectations, trapping Dynamic Epistemic Logic (DEL) belief updates.
  - **Theorem 8.3 (Endogenous IC1 Tug-of-War Factor Starvation)**: `ic1_tug_of_war_starves_completion`
    Resource-supplying consumers continuing uncurtailed consumption starves the complementary completion factor m_comp,
    rendering stage-2 completion strictly physically infeasible.
  - **Theorem 8.4 (The ABCT Master Malinvestment & Regret Theorem)**: `abct_intertemporal_malinvestment_regret`
    Fiduciary signal distortion induces higher-order capital initiation that cannot be completed,
    culminating in midstream factor exhaustion and mandatory ex-post cross-branch regret.
  - **Theorem 8.5 (Hülsmann-Rothbard Synchronized Cluster of Entrepreneurial Errors)**: `abct_cluster_of_entrepreneurial_errors`
    A common credit-distorted interest signal synchronizes malinvestment across an entire finite cohort of entrepreneurs,
    generating a pervasive economic boom-bust cluster of errors.
  - **Theorem 8.6 (Kernel-Checked Non-Vacuity & Consistency of the ABCT Master Theorem)**: `abct_master_theorem_non_vacuous`
    Concrete 2-actor, 3-period, 3-history model witness verifying that all 21 hypotheses of the ABCT Master Theorem
    are simultaneously satisfiable and mathematically consistent.

Contains zero global `axiom` declarations.
-/

@[expose] public section

namespace Praxeology

open scoped Classical

-- =========================================================================
-- Section 1: Fiduciary Signal Opacity & Present-Value Stage Distortion
-- =========================================================================

/-- DEL epistemic update filtered by an observable monetary/price signal. -/
def SignalFilteredPlausible {History : Type}
    (K : Set History) (signal : History → ℚ) (h_actual : History) : Set History :=
  { h' ∈ K | signal h' = signal h_actual }

/-- Theorem 8.1 (Artificial Credit Expansion Distorts Intertemporal Valuation):
    An artificially lowered discount rate ι_credit makes a higher-order capital project
    appear profitable (> V_safe) despite the natural rate ι_nat making it unprofitable (≤ V_safe). -/
theorem credit_expansion_distorts_stage_valuation
    (ΔP_proj ι_nat ι_credit deadband V_safe : ℚ)
    (h_pos_nat : 0 < 1 + ι_nat)
    (h_pos_cred : 0 < 1 + ι_credit)
    (h_V_nonneg : 0 ≤ V_safe)
    (h_cred_boom : (1 + ι_credit) * (V_safe + deadband) < ΔP_proj)
    (h_nat_restraint : ΔP_proj ≤ (1 + ι_nat) * (V_safe + deadband)) :
    AttenuateHop ΔP_proj ι_nat deadband ≤ V_safe ∧
    V_safe < AttenuateHop ΔP_proj ι_credit deadband := by
  constructor
  · unfold AttenuateHop
    apply max_le h_V_nonneg
    have h_div : ΔP_proj / (1 + ι_nat) ≤ V_safe + deadband := by
      rw [div_le_iff₀ h_pos_nat]
      linarith
    linarith
  · unfold AttenuateHop
    have h_div : V_safe + deadband < ΔP_proj / (1 + ι_credit) := by
      rw [lt_div_iff₀ h_pos_cred]
      linarith
    have h_lt : V_safe < ΔP_proj / (1 + ι_credit) - deadband := by linarith
    exact lt_of_lt_of_le h_lt (le_max_right 0 _)

/-- Theorem 8.2 (Strategic Opacity Traps DEL Epistemic Update):
    If an unbacked credit-expansion world produces the same nominal interest signal
    as a genuine savings world, the savings world remains in the agent's signal-filtered
    plausibility set, trapping dynamic epistemic logic updates. -/
theorem strategic_opacity_traps_del_update {History : Type}
    (K : Set History) (signal : History → ℚ) (h_saved h_credit : History)
    (h_in_prior : h_saved ∈ K)
    (h_opacity : signal h_saved = signal h_credit) :
    h_saved ∈ SignalFilteredPlausible K signal h_credit :=
  ⟨h_in_prior, h_opacity⟩

-- =========================================================================
-- Section 2: Endogenous Multi-Agent Factor Tug-of-War (IC1)
-- =========================================================================

/-- IntertemporalFactorTugOfWar (Axiom IC1 as an explicit structure):
    Models multi-agent intertemporal resource coupling between a resource-supplying
    Consumer `c` and an Entrepreneur `i`. At `t0`, if Consumer `c` executes
    `α_save` (on `h_saved`), 1 unit of complementary factor `m_comp` is released
    to Entrepreneur `i` at `t1`. If Consumer `c` executes `α_consume_now`
    (unchanged time preference on `h_credit`), `m_comp` is exhausted in consumption,
    leaving Entrepreneur `i` with `omega i t1 h_credit m_comp = 0`. -/
structure IntertemporalFactorTugOfWar
    {Agent Moment History Action Means : Type} [DecidableEq Action]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (c i : Agent) (t0 t1 : Moment) (h_saved h_credit : History)
    (α_save α_consume_now α_complete : Action) (m_comp : Means) : Prop where
  h_prec01 : F.prec t0 t1
  h_consumer_saves_on_saved : F.Exec c t0 α_save h_saved
  h_consumer_consumes_on_credit : F.Exec c t0 α_consume_now h_credit
  h_saved_releases_factor :
    F.Exec c t0 α_save h_saved → F.prec t0 t1 → F.omega i t1 h_saved m_comp = 1
  h_credit_exhausts_factor :
    F.Exec c t0 α_consume_now h_credit → F.prec t0 t1 → F.omega i t1 h_credit m_comp = 0
  h_comp_req : F.use_means α_complete m_comp = 1

/-- Theorem 8.3 (Endogenous IC1 Tug-of-War Factor Starvation):
    When Consumer `c` maintains unchanged time preference on `h_credit` (`α_consume_now`)
    rather than saving (`α_save` on `h_saved`), the complementary factor `m_comp` is
    available on `h_saved` (`omega = 1`) but starved on `h_credit` (`omega = 0`),
    rendering Stage-2 completion `α_complete` physically infeasible on `h_credit`. -/
theorem ic1_tug_of_war_starves_completion
    {Agent Moment History Action Means : Type} [DecidableEq Action]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (c i : Agent) (t0 t1 : Moment) (h_saved h_credit : History)
    (α_save α_consume_now α_complete : Action) (m_comp : Means)
    (h_tow : IntertemporalFactorTugOfWar F c i t0 t1 h_saved h_credit α_save α_consume_now α_complete m_comp) :
    F.omega i t1 h_saved m_comp = 1 ∧
    F.omega i t1 h_credit m_comp = 0 ∧
    α_complete ∉ F.A_feas i t1 h_credit := by
  have h_saved_om := h_tow.h_saved_releases_factor h_tow.h_consumer_saves_on_saved h_tow.h_prec01
  have h_cred_om := h_tow.h_credit_exhausts_factor h_tow.h_consumer_consumes_on_credit h_tow.h_prec01
  refine ⟨h_saved_om, h_cred_om, ?_⟩
  apply infeasible_of_insufficient_endowment F i t1 h_credit α_complete m_comp
  rw [h_cred_om, h_tow.h_comp_req]
  exact Nat.zero_lt_one

-- =========================================================================
-- Section 3: Intertemporal Capital Malinvestment & The ABCT Master Theorem
-- =========================================================================

/-- Theorem 8.4 (The ABCT Master Malinvestment & Regret Theorem):
    Credit-expansion induced signal distortion induces an entrepreneur to begin
    an unsustainable higher-order capital structure (yielding intermediate k1 but not
    the complementary means m_comp required for completion). At stage t1, completion
    α_complete is strictly physically infeasible. At bust moment t2, the agent suffers
    cross-branch counterfactual regret relative to the safe baseline α₀. -/
theorem abct_intertemporal_malinvestment_regret
    {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (K : Set History) (signal : History → ℚ)
    (i : Agent) (t0 t1 t2 τ_safe : Moment) (h_saved h_credit h_safe : History)
    (α_stage1 α_complete : Action) (k1 m_comp : Means)
    (ΔP_proj ι_nat ι_credit deadband V_safe : ℚ)
    (h_pos_nat : 0 < 1 + ι_nat) (h_pos_cred : 0 < 1 + ι_credit) (h_V_nonneg : 0 ≤ V_safe)
    (h_cred_boom : (1 + ι_credit) * (V_safe + deadband) < ΔP_proj)
    (h_nat_restraint : ΔP_proj ≤ (1 + ι_nat) * (V_safe + deadband))
    (h_in_prior : h_saved ∈ K) (h_opacity : signal h_saved = signal h_credit)
    (h_ex_ante : ExAntePurposefulAct M i t0 h_credit α_stage1)
    (h_exec_s1 : F.Exec i t0 α_stage1 h_credit) (h_prec01 : F.prec t0 t1)
    (h_init_k1 : F.omega i t0 h_credit k1 = 0)
    (h_use_s1_k1 : F.use_means α_stage1 k1 = 0)
    (h_yield_s1_k1 : F.yield_means α_stage1 k1 = 1)
    (h_init_comp : F.omega i t0 h_credit m_comp = 0)
    (h_use_s1_comp : F.use_means α_stage1 m_comp = 0)
    (h_yield_s1_comp : F.yield_means α_stage1 m_comp = 0)
    (h_comp_req : F.use_means α_complete m_comp = 1)
    (h_safe_part : h_safe ∈ M.ChoicePartition i t0 M.α₀)
    (h_prec_safe : M.prec t0 τ_safe) (h_mem_safe : M.mem_hist τ_safe h_safe)
    (h_bust_pref : M.Pref i t2 h_credit
      (M.OutcomeOf i M.α₀ t0 τ_safe h_safe)
      (M.OutcomeOf i α_stage1 t0 t2 h_credit)) :
    (AttenuateHop ΔP_proj ι_nat deadband ≤ V_safe ∧
      V_safe < AttenuateHop ΔP_proj ι_credit deadband) ∧
    h_saved ∈ SignalFilteredPlausible K signal h_credit ∧
    F.omega i t1 h_credit k1 = 1 ∧
    F.omega i t1 h_credit m_comp = 0 ∧
    α_complete ∉ F.A_feas i t1 h_credit ∧
    CrossBranchRegret M i t0 t2 h_credit α_stage1 M.α₀ := by
  have h_val := credit_expansion_distorts_stage_valuation
    ΔP_proj ι_nat ι_credit deadband V_safe h_pos_nat h_pos_cred h_V_nonneg h_cred_boom h_nat_restraint
  have h_op := strategic_opacity_traps_del_update K signal h_saved h_credit h_in_prior h_opacity
  have h_tr_k1 := F.law_in_re_transition i t0 t1 h_credit α_stage1 k1 h_exec_s1 h_prec01
  rw [h_use_s1_k1, h_init_k1, h_yield_s1_k1, Nat.add_zero, Nat.zero_add] at h_tr_k1
  have h_tr_comp := F.law_in_re_transition i t0 t1 h_credit α_stage1 m_comp h_exec_s1 h_prec01
  rw [h_use_s1_comp, h_init_comp, h_yield_s1_comp, Nat.add_zero, Nat.zero_add] at h_tr_comp
  have h_infeas : α_complete ∉ F.A_feas i t1 h_credit := by
    apply infeasible_of_insufficient_endowment F i t1 h_credit α_complete m_comp
    rw [h_tr_comp, h_comp_req]
    exact Nat.zero_lt_one
  have h_regret : CrossBranchRegret M i t0 t2 h_credit α_stage1 M.α₀ :=
    ⟨M.alpha_zero_mem_cont i t0 h_credit, h_safe, h_safe_part, τ_safe, h_prec_safe, h_mem_safe, h_bust_pref⟩
  exact ⟨h_val, h_op, h_tr_k1, h_tr_comp, h_infeas, h_regret⟩

-- =========================================================================
-- Section 4: Synchronized Cluster of Entrepreneurial Errors
-- =========================================================================

/-- Theorem 8.5 (Hülsmann-Rothbard Synchronized Cluster of Entrepreneurial Errors):
    In any non-empty cohort of entrepreneurs `Entrepreneurs : Finset Agent` who
    all observe the same credit-distorted market interest signal (`signal h_saved = signal h_credit`),
    fiduciary credit expansion (`ι_credit < ι_nat`) does not merely cause an isolated error;
    it induces a synchronized cluster of errors where EVERY entrepreneur `i ∈ Entrepreneurs`
    simultaneously builds Stage-1 capital `k1`, encounters midstream completion infeasibility
    (`α_complete ∉ F.A_feas i t1 h_credit`) due to Consumer `c`'s unchanged consumption on `h_credit`,
    and suffers strict `CrossBranchRegret` at `t2`. -/
theorem abct_cluster_of_entrepreneurial_errors
    {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (F : CausalTransitionFrame Agent Moment History Action Means)
    (M : CounterfactualActionModel Agent Moment History Action Ends)
    (Entrepreneurs : Finset Agent) (h_nonempty : Entrepreneurs.Nonempty)
    (K : Set History) (signal : History → ℚ)
    (c : Agent) (t0 t1 t2 τ_safe : Moment) (h_saved h_credit h_safe : History)
    (α_save α_consume_now α_stage1 α_complete : Action) (k1 m_comp : Means)
    (ΔP_proj ι_nat ι_credit deadband V_safe : ℚ)
    (h_pos_nat : 0 < 1 + ι_nat) (h_pos_cred : 0 < 1 + ι_credit) (h_V_nonneg : 0 ≤ V_safe)
    (h_cred_boom : (1 + ι_credit) * (V_safe + deadband) < ΔP_proj)
    (h_nat_restraint : ΔP_proj ≤ (1 + ι_nat) * (V_safe + deadband))
    (h_in_prior : h_saved ∈ K) (h_opacity : signal h_saved = signal h_credit)
    (h_use_s1_k1 : F.use_means α_stage1 k1 = 0)
    (h_yield_s1_k1 : F.yield_means α_stage1 k1 = 1)
    (h_prec_safe : M.prec t0 τ_safe) (h_mem_safe : M.mem_hist τ_safe h_safe)
    (h_cohort_act : ∀ i ∈ Entrepreneurs, ExAntePurposefulAct M i t0 h_credit α_stage1)
    (h_cohort_exec : ∀ i ∈ Entrepreneurs, F.Exec i t0 α_stage1 h_credit)
    (h_cohort_init_k1 : ∀ i ∈ Entrepreneurs, F.omega i t0 h_credit k1 = 0)
    (h_cohort_tow : ∀ i ∈ Entrepreneurs,
      IntertemporalFactorTugOfWar F c i t0 t1 h_saved h_credit α_save α_consume_now α_complete m_comp)
    (h_cohort_safe : ∀ i ∈ Entrepreneurs, h_safe ∈ M.ChoicePartition i t0 M.α₀)
    (h_cohort_bust : ∀ i ∈ Entrepreneurs,
      M.Pref i t2 h_credit
        (M.OutcomeOf i M.α₀ t0 τ_safe h_safe)
        (M.OutcomeOf i α_stage1 t0 t2 h_credit)) :
    (AttenuateHop ΔP_proj ι_nat deadband ≤ V_safe ∧
      V_safe < AttenuateHop ΔP_proj ι_credit deadband) ∧
    h_saved ∈ SignalFilteredPlausible K signal h_credit ∧
    ∀ i ∈ Entrepreneurs,
      F.omega i t1 h_credit k1 = 1 ∧
      F.omega i t1 h_credit m_comp = 0 ∧
      α_complete ∉ F.A_feas i t1 h_credit ∧
      CrossBranchRegret M i t0 t2 h_credit α_stage1 M.α₀ := by
  have h_val := credit_expansion_distorts_stage_valuation
    ΔP_proj ι_nat ι_credit deadband V_safe h_pos_nat h_pos_cred h_V_nonneg h_cred_boom h_nat_restraint
  have h_op := strategic_opacity_traps_del_update K signal h_saved h_credit h_in_prior h_opacity
  refine ⟨h_val, h_op, ?_⟩
  intro i hi
  have h_tow := h_cohort_tow i hi
  have h_starve := ic1_tug_of_war_starves_completion F c i t0 t1 h_saved h_credit
    α_save α_consume_now α_complete m_comp h_tow
  have h_tr_k1 := F.law_in_re_transition i t0 t1 h_credit α_stage1 k1
    (h_cohort_exec i hi) h_tow.h_prec01
  rw [h_use_s1_k1, h_cohort_init_k1 i hi, h_yield_s1_k1, Nat.add_zero, Nat.zero_add] at h_tr_k1
  have h_regret : CrossBranchRegret M i t0 t2 h_credit α_stage1 M.α₀ :=
    ⟨M.alpha_zero_mem_cont i t0 h_credit, h_safe, h_cohort_safe i hi,
     τ_safe, h_prec_safe, h_mem_safe, h_cohort_bust i hi⟩
  exact ⟨h_tr_k1, h_starve.2.1, h_starve.2.2, h_regret⟩

-- =========================================================================
-- Section 5: Concrete 2-Actor, 3-Period ABCT Non-Vacuity Model Witness
-- =========================================================================

/-- Concrete 2-Actor, 3-Period CausalTransitionFrame for ABCT:
    - Agents (`Fin 2`): `0` = Entrepreneur, `1` = Resource-Consumer
    - Moments (`Fin 3`): `0` = Boom initiation (t0), `1` = Midstream bottleneck (t1), `2` = Realization/Bust (t2)
    - Histories (`Fin 3`): `0` = h_credit (Credit shock), `1` = h_saved (Genuine savings), `2` = h_safe (Safe baseline)
    - Actions (`Fin 3`): `0` = α₀ (Safe/Passive baseline), `1` = α_stage1 (Start long project), `2` = α_complete (Complete stage 2)
    - Means (`Fin 2`): `0` = k1 (Stage-1 intermediate capital), `1` = m_comp (Complementary completion factor) -/
def ABCTConcreteTransitionFrame :
    CausalTransitionFrame (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 2) where
  «α₀» := 0
  prec := fun t1 t2 => t1.val = 0 ∧ t2.val = 1
  A_feas := fun _ t h =>
    if t = 0 then {0, 1}
    else if t = 1 ∧ h = 1 then {0, 2}
    else {0}
  alpha_zero_mem := by
    intro i t h
    fin_cases t <;> fin_cases h <;> decide
  Exec := fun i t α h =>
    i = 0 ∧ t = 0 ∧ α = 1 ∧ h = 0
  omega := fun _ t h m =>
    if t = 0 then 0
    else if t = 1 ∧ h = 0 ∧ m = 0 then 1
    else if t = 1 ∧ h = 1 then 1
    else 0
  use_means := fun α m =>
    if α = 2 ∧ m = 1 then 1 else 0
  yield_means := fun α m =>
    if α = 1 ∧ m = 0 then 1 else 0
  phys_feas := by
    intro i t h α hα m
    fin_cases i <;> fin_cases t <;> fin_cases h <;> fin_cases α <;> fin_cases m <;>
      revert hα <;> decide
  law_in_re_transition := by
    intro i t t' h α m h_exec h_prec
    rcases h_exec with ⟨rfl, rfl, rfl, rfl⟩
    rcases h_prec with ⟨_, ht'⟩
    have ht1 : t' = 1 := Fin.ext ht'
    subst ht1
    fin_cases m <;> decide

/-- Concrete 2-Actor, 3-Period CounterfactualActionModel for ABCT:
    - Ends (`Fin 3`): `0` = e_bust (Liquidation loss), `1` = e_safe (Safe baseline return), `2` = e_boom (Completed project return)
    - Strict stationary preference: `e_boom (2) ≻ e_safe (1) ≻ e_bust (0)` (`e2 < e1`).
    - Under strategic opacity at `t0` on `h_credit (0)`, Entrepreneur's `MinPlausible` is `{1}` (`h_saved`),
      where `α_stage1 (1)` yields `2` (`e_boom`) > `1` (`e_safe`).
    - On the actual path `h_credit (0)` at `t2 (2)`, `α_stage1 (1)` yields `0` (`e_bust`), while the
      counterfactual safe branch `h_safe (2)` yields `1` (`e_safe`), triggering strict `CrossBranchRegret`. -/
def ABCTConcreteActionModel :
    CounterfactualActionModel (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 3) where
  «α₀» := 0
  prec := fun t1 t2 => t1 < t2
  mem_hist := fun _ _ => True
  enacted := fun _ _ h => if h = 2 then 0 else 1
  A_cont := fun _ t _ => if t = 0 then {0, 1} else {0}
  alpha_zero_mem_cont := by
    intro i t h
    fin_cases t <;> decide
  MinPlausible := fun _ _ _ => {1}
  OutcomeOf := fun _ α _ _ h =>
    if α = 0 then 1
    else if α = 1 ∧ h = 1 then 2
    else 0
  ExpectedMaturation := fun _ _ _ _ => 2
  Pref := fun _ _ _ e1 e2 => e2 < e1
  pref_asymm := by intro _ _ _ e1 e2 h12 h21; exact Nat.lt_asymm h12 h21

/-- Theorem 8.6 (Kernel-Checked Non-Vacuity & Consistency of the ABCT Master Theorem):
    Instantiates `abct_intertemporal_malinvestment_regret` on `ABCTConcreteTransitionFrame`
    and `ABCTConcreteActionModel` with explicit rational parameters:
    `ΔP_proj = 11`, `ι_nat = 1/4`, `ι_credit = 1/10`, `deadband = 1`, `V_safe = 8`.
    Certifies that all 21 hypotheses of the ABCT Master Theorem are simultaneously
    satisfiable and non-vacuous. -/
theorem abct_master_theorem_non_vacuous :
    let F := ABCTConcreteTransitionFrame
    let M := ABCTConcreteActionModel
    let K : Set (Fin 3) := {0, 1}
    let signal : Fin 3 → ℚ := fun h => if h = 2 then (1 : ℚ) / 4 else (1 : ℚ) / 10
    (AttenuateHop 11 (1 / 4) 1 ≤ 8 ∧ 8 < AttenuateHop 11 (1 / 10) 1) ∧
    (1 : Fin 3) ∈ SignalFilteredPlausible K signal 0 ∧
    F.omega 0 1 0 0 = 1 ∧
    F.omega 0 1 0 1 = 0 ∧
    (2 : Fin 3) ∉ F.A_feas 0 1 0 ∧
    CrossBranchRegret M 0 0 2 0 1 0 := by
  have h_ex_ante : ExAntePurposefulAct ABCTConcreteActionModel 0 0 0 1 := by
    refine ⟨by decide, rfl, ?_, ?_⟩
    · intro h' hh'
      have h_eq : h' = 1 := hh'
      subst h_eq
      dsimp [ABCTConcreteActionModel]
      decide
    · intro h' hh' β hβ
      have h_eq : h' = 1 := hh'
      subst h_eq
      dsimp [ABCTConcreteActionModel]
      fin_cases β <;> decide
  exact abct_intertemporal_malinvestment_regret
    ABCTConcreteTransitionFrame
    ABCTConcreteActionModel
    ({0, 1} : Set (Fin 3))
    (fun h => if h = 2 then (1 : ℚ) / 4 else (1 : ℚ) / 10)
    0 0 1 2 2 1 0 2 1 2 0 1
    11 (1 / 4) (1 / 10) 1 8
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by simp)
    rfl
    h_ex_ante
    ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl⟩
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    (by dsimp [ABCTConcreteActionModel]; decide)
    trivial
    (by dsimp [ABCTConcreteActionModel]; decide)

end Praxeology

end
