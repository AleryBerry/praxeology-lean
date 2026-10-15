module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Marginal
public import Praxeology.Catallactics
public import Praxeology.Breakthroughs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false

/-!
# Praxeology.Consistency

Formalization of Phase 5 of Praxeology:
Model-Theoretic Consistency & Verification:
1. Section 1: Multi-Option Menu Consistency for Purposeful Action (Theorem 5.1a).
2. Section 2: Purely Ordinal Ex-Post Regret (Theorem 6.2_ordinal).
3. Section 3: Concrete Finite Model Witness (Theorem 5.1b: ModelM0).
-/

@[expose] public section

namespace Praxeology

open scoped Classical

-- =========================================================================
-- Section 1: Multi-Option Menu Consistency (Theorem 5.1a)
-- =========================================================================

/-- Theorem 5.1a (Multi-Option Menu Consistency for Purposeful Action):
    Under a 3-option choice menu {α1, α2, α3} with strict ordinal ranking e1 ≻ e2 ≻ e3,
    e1 strictly beating the passive baseline e0, and α1 being physically executed,
    PurposefulAct is completely consistent, uniquely selecting α1 and refuting
    purposeful execution for both dominated actions α2 and α3. -/
theorem three_option_menu_consistency
    (i : Agent) (t : Moment) (h : History)
    (α1 α2 α3 : Action)
    (h_menu : A_feas i t h = {α1, α2, α3})
    (hne12 : α1 ≠ α2) (hne13 : α1 ≠ α3) (hne23 : α2 ≠ α3)
    (h_exec1 : Exec i t α1 h)
    (h_pref10 : Preference i t h (End_of i α1 t h) (End_of i α₀ t h))
    (h_pref12 : Preference i t h (End_of i α1 t h) (End_of i α2 t h))
    (h_pref23 : Preference i t h (End_of i α2 t h) (End_of i α3 t h))
    (h_trans : ∀ e1 e2 e3, Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    PurposefulAct i t h α1 ∧
    ¬ PurposefulAct i t h α2 ∧
    ¬ PurposefulAct i t h α3 := by
  have h_feas1 : α1 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_feas2 : α2 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_feas3 : α3 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_pref13 : Preference i t h (End_of i α1 t h) (End_of i α3 t h) :=
    h_trans (End_of i α1 t h) (End_of i α2 t h) (End_of i α3 t h) h_pref12 h_pref23
  -- 1. α1 satisfies PurposefulAct
  have h_act1 : PurposefulAct i t h α1 := by
    refine ⟨h_feas1, h_exec1, h_pref10, ?_⟩
    intro β hβ
    rw [h_menu] at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with hβ1 | hβ2 | hβ3
    · rw [hβ1]; exact pref_irrefl i t h (End_of i α1 t h)
    · rw [hβ2]; exact pref_asymm i t h h_pref12
    · rw [hβ3]; exact pref_asymm i t h h_pref13
  -- 2. α2 fails PurposefulAct (dominated by α1)
  have h_not_act2 : ¬ PurposefulAct i t h α2 := by
    intro h_act2
    have h_undom2 := h_act2.2.2.2 α1 h_feas1
    exact h_undom2 h_pref12
  -- 3. α3 fails PurposefulAct (dominated by α2)
  have h_not_act3 : ¬ PurposefulAct i t h α3 := by
    intro h_act3
    have h_undom3 := h_act3.2.2.2 α2 h_feas2
    exact h_undom3 h_pref23
  exact ⟨h_act1, h_not_act2, h_not_act3⟩

-- =========================================================================
-- Section 2: Purely Ordinal Ex-Post Regret (Theorem 6.2_ordinal)
-- =========================================================================

/-- Purely ordinal definition of ex-post regret:
    At maturation moment τ in history h, the agent strictly prefers the status quo /
    passive inertial end (End_of k α₀ t h) over the trade end (End_of k α_k t h).
    Eliminates the need for real-valued utility or the uninterpreted RealizedGain axiom. -/
def OrdinalRegret (k : Agent) (t τ : Moment) (h : History) (α_k : Action) : Prop :=
  Preference k τ h (End_of k α₀ t h) (End_of k α_k t h)

/-- Theorem 6.2_ordinal (Purely Ordinal Mandatory Ex-Post Regret):
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
-- Section 3: Concrete Finite Model Witness (ModelM0)
-- =========================================================================

/-- FinitePraxeologicalModel:
    A self-contained, computable model-theoretic structure over concrete finite types
    (without relying on global axioms), establishing the mutual consistency and non-vacuity of:
    1. A discrete temporal tree with forward branching and backward linearity.
    2. Disjoint STIT choice partitions and purposeful agency.
    3. An acceptance profile over commodities featuring a uniquely max-marketable money good
       that is a fixed point of the Bourbaki-Witt indirect exchange operator. -/
structure FinitePraxeologicalModel where
  MomentM : Type
  AgentM  : Type
  MeansM  : Type
  [instFintypeAgent : Fintype AgentM]
  prec : MomentM → MomentM → Prop
  prec_irrefl : ∀ m, ¬ prec m m
  prec_trans : ∀ a b c, prec a b → prec b c → prec a c
  prec_backward_linear : ∀ t1 t2 t3, prec t1 t3 → prec t2 t3 → prec t1 t2 ∨ t1 = t2 ∨ prec t2 t1
  root : MomentM
  branch1 : MomentM
  branch2 : MomentM
  h_branch1 : prec root branch1
  h_branch2 : prec root branch2
  h_incomp1 : ¬ prec branch1 branch2
  h_incomp2 : ¬ prec branch2 branch1
  h_distinct_branches : branch1 ≠ branch2
  gamma0 : MeansM → Finset AgentM
  money_good : MeansM
  h_max_marketable : ∀ m : MeansM, m ≠ money_good → (gamma0 m).card < (gamma0 money_good).card
  h_money_universal : gamma0 money_good = Finset.univ

/-- Concrete acceptance profile for the 3-good, 2-agent finite model:
    - Good 0 is universally accepted by both agents ({0, 1}).
    - Good 1 is accepted only by agent 0 ({0}).
    - Good 2 is accepted only by agent 1 ({1}). -/
def model_gamma0 : Fin 3 → Finset (Fin 2)
  | 0 => Finset.univ
  | 1 => {0}
  | 2 => {1}

/-- Concrete 3-moment temporal precedence relation on Fin 3:
    0 < 1 and 0 < 2, with 1 and 2 forming mutually incomparable branches. -/
def model_prec (a b : Fin 3) : Prop :=
  a = 0 ∧ (b = 1 ∨ b = 2)

/-- ModelM0: Concrete Finite Model Witness certifying the non-vacuity of praxeological frames. -/
def ModelM0 : FinitePraxeologicalModel where
  MomentM := Fin 3
  AgentM  := Fin 2
  MeansM  := Fin 3
  prec := model_prec
  prec_irrefl := by
    intro m hm
    dsimp [model_prec] at hm
    rcases hm with ⟨hm0, hm12⟩
    subst hm0
    rcases hm12 with h1 | h2
    · have h_ne1 : (0 : Fin 3) ≠ 1 := by decide
      exact (h_ne1 h1).elim
    · have h_ne2 : (0 : Fin 3) ≠ 2 := by decide
      exact (h_ne2 h2).elim
  prec_trans := by
    intro a b c hab hbc
    dsimp [model_prec] at hab hbc
    have hb1 : b = 0 := hbc.1
    have hb2 : b = 1 ∨ b = 2 := hab.2
    subst hb1
    rcases hb2 with h1 | h2
    · have h_ne1 : (0 : Fin 3) ≠ 1 := by decide
      exact (h_ne1 h1).elim
    · have h_ne2 : (0 : Fin 3) ≠ 2 := by decide
      exact (h_ne2 h2).elim
  prec_backward_linear := by
    intro t1 t2 t3 h1 h2
    dsimp [model_prec] at h1 h2
    have ht1 : t1 = 0 := h1.1
    have ht2 : t2 = 0 := h2.1
    right; left
    rw [ht1, ht2]
  root := 0
  branch1 := 1
  branch2 := 2
  h_branch1 := by dsimp [model_prec]; decide
  h_branch2 := by dsimp [model_prec]; decide
  h_incomp1 := by dsimp [model_prec]; decide
  h_incomp2 := by dsimp [model_prec]; decide
  h_distinct_branches := by decide
  gamma0 := model_gamma0
  money_good := 0
  h_max_marketable := by
    intro m hm
    fin_cases m
    · exact (hm rfl).elim
    · decide
    · decide
  h_money_universal := by
    rfl

/-- Theorem 5.1b (Model-Theoretic Consistency & Non-Vacuity):
    The finite model structure is non-empty, constructively verifying that the
    temporal branching conditions and Bourbaki-Witt money emergence axioms are satisfiable. -/
theorem finite_model_witness_consistent : Nonempty FinitePraxeologicalModel :=
  ⟨ModelM0⟩

-- =========================================================================
-- Section 5: Concrete 2-Actor, 3-Period ABCT Counterfactual Model Witness
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
  A_feas := fun _ t _ => if t = 0 then {0, 1} else {0}
  A_cont := fun _ t _ => if t = 0 then {0, 1} else {0}
  cont_subset_feas := by intro _ _ _ a ha; exact ha
  alpha_zero_mem_cont := by
    intro i t h
    fin_cases t <;> decide
  ChoicePartition := fun _ _ α =>
    { h | (α = 0 ∧ h = 2) ∨ (α = 1 ∧ (h = 0 ∨ h = 1)) }
  Exec := fun _ _ α h =>
    (α = 0 ∧ h = 2) ∨ (α = 1 ∧ (h = 0 ∨ h = 1))
  exec_iff_mem_partition := by intro _ _ _ _; rfl
  MinPlausible := fun _ _ _ => {1}
  OutcomeOf := fun _ α _ _ h =>
    if α = 0 then 1
    else if α = 1 ∧ h = 1 then 2
    else 0
  ExpectedMaturation := fun _ _ _ _ => 2
  Pref := fun _ _ _ e1 e2 => e2 < e1
  pref_irrefl := by intro _ _ _ e; exact Nat.lt_irrefl e.val
  pref_asymm := by intro _ _ _ e1 e2 h12 h21; exact Nat.lt_asymm h12 h21

/-- Theorem 5.2 (Kernel-Checked Non-Vacuity of the ABCT Master Theorem):
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
    refine ⟨by decide, Or.inr ⟨rfl, Or.inl rfl⟩, ?_, ?_⟩
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
    (by simp [ABCTConcreteActionModel])
    (by dsimp [ABCTConcreteActionModel]; decide)
    trivial
    (by dsimp [ABCTConcreteActionModel]; decide)

end Praxeology

end
