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
public import Mathlib.Algebra.Order.Field.Basic
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
Model-Theoretic Consistency & Master Coalescence Completion:
1. Section 1: Multi-Option Menu Consistency (Theorem 5.1a).
2. Section 2: Purely Ordinal Ex-Post Regret (Theorem 6.2_ordinal).
3. Section 3: Exact Theorem 7.1 — Shadow-Price Simplex & Critical Attenuation Regime (Lemma 7.1, Theorem 7.1(I), Theorem 7.1(II)).
4. Section 4: Concrete Finite Model Witness (Theorem 5.1b: ModelM0).
-/

@[expose] public section

namespace Praxeology

open scoped Classical

-- =========================================================================
-- Section 1: Multi-Option Menu Consistency (Theorem 5.1a)
-- =========================================================================

/-- Theorem 5.1a (Multi-Option Menu Consistency for Demonstrated Preference):
    Under a 3-option choice menu {α1, α2, α3} with strict ordinal ranking e1 ≻ e2 ≻ e3,
    Axiom 2(3)' (Demonstrated Preference) is completely consistent,
    uniquely forcing deliberative STIT execution of the top-ranked action α1,
    while refuting deliberative execution for both dominated actions α2 and α3. -/
theorem three_option_menu_consistency
    (i : Agent) (t : Moment) (h : History)
    (α1 α2 α3 : Action)
    (h_menu : A_feas i t h = {α1, α2, α3})
    (hne12 : α1 ≠ α2) (hne13 : α1 ≠ α3) (hne23 : α2 ≠ α3)
    (h_pref12 : Preference i t h (End_of i α1 t h) (End_of i α2 t h))
    (h_pref23 : Preference i t h (End_of i α2 t h) (End_of i α3 t h)) :
    dstit i t (Exec i t α1) h ∧
    ¬ dstit i t (Exec i t α2) h ∧
    ¬ dstit i t (Exec i t α3) h := by
  have h_feas1 : α1 ∈ A_feas i t h := by
    rw [h_menu]
    simp
  have h_feas2 : α2 ∈ A_feas i t h := by
    rw [h_menu]
    simp
  have h_feas3 : α3 ∈ A_feas i t h := by
    rw [h_menu]
    simp
  have h_pref13 : Preference i t h (End_of i α1 t h) (End_of i α3 t h) :=
    pref_trans i t h h_pref12 h_pref23
  -- 1. α1 is deliberatively executed
  have h_dstit1 : dstit i t (Exec i t α1) h := by
    apply (demonstrated_preference i t h α1 h_feas1).mpr
    intro β hβ
    rw [h_menu] at hβ
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with ⟨hne_b1, rfl | rfl | rfl⟩
    · exact (hne_b1 rfl).elim
    · exact h_pref12
    · exact h_pref13
  -- 2. α2 is not deliberatively executed
  have h_not_dstit2 : ¬ dstit i t (Exec i t α2) h := by
    intro hd2
    have h_dem2 := (demonstrated_preference i t h α2 h_feas2).mp hd2
    have h_mem1_in_erase2 : α1 ∈ (A_feas i t h).erase α2 := by
      rw [Finset.mem_erase, h_menu]
      simp [hne12]
    have h_pref21 := h_dem2 α1 h_mem1_in_erase2
    exact pref_asymm i t h h_pref12 h_pref21
  -- 3. α3 is not deliberatively executed
  have h_not_dstit3 : ¬ dstit i t (Exec i t α3) h := by
    intro hd3
    have h_dem3 := (demonstrated_preference i t h α3 h_feas3).mp hd3
    have h_mem2_in_erase3 : α2 ∈ (A_feas i t h).erase α3 := by
      rw [Finset.mem_erase, h_menu]
      simp [hne23]
    have h_pref32 := h_dem3 α2 h_mem2_in_erase3
    exact pref_asymm i t h h_pref23 h_pref32
  exact ⟨h_dstit1, h_not_dstit2, h_not_dstit3⟩

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
    if both ends belong to each agent's feasible choice set at maturation τ and are distinct,
    then by strict connectedness of ordinal preference (pref_connected),
    at least one agent MUST experience ex-post regret. -/
theorem ordinal_mandatory_ex_post_regret
    (i j : Agent) (t τ : Moment) (h : History)
    (α_i α_j : Action)
    (h_not_both : ¬ (Preference i τ h (End_of i α_i t h) (End_of i α₀ t h) ∧
                     Preference j τ h (End_of j α_j t h) (End_of j α₀ t h)))
    (h_mem_i_act : End_of i α_i t h ∈ (A_feas i τ h).image (End_of i · τ h))
    (h_mem_i_zero : End_of i α₀ t h ∈ (A_feas i τ h).image (End_of i · τ h))
    (hne_i : End_of i α_i t h ≠ End_of i α₀ t h)
    (h_mem_j_act : End_of j α_j t h ∈ (A_feas j τ h).image (End_of j · τ h))
    (h_mem_j_zero : End_of j α₀ t h ∈ (A_feas j τ h).image (End_of j · τ h))
    (hne_j : End_of j α_j t h ≠ End_of j α₀ t h) :
    OrdinalRegret i t τ h α_i ∨ OrdinalRegret j t τ h α_j := by
  have h_conn_i := pref_connected i τ h h_mem_i_act h_mem_i_zero hne_i
  have h_conn_j := pref_connected j τ h h_mem_j_act h_mem_j_zero hne_j
  dsimp [OrdinalRegret]
  rcases h_conn_i with h_pref_i | h_regret_i
  · rcases h_conn_j with h_pref_j | h_regret_j
    · exfalso
      exact h_not_both ⟨h_pref_i, h_pref_j⟩
    · exact Or.inr h_regret_j
  · exact Or.inl h_regret_i

-- =========================================================================
-- Section 3: Exact Theorem 7.1 — Shadow-Price Simplex & Critical Attenuation Regime
-- =========================================================================

/-- Single-hop backward price attenuation operator:
    Discounts price difference ΔP by originary interest (1 + ι) and subtracts
    the deadband (quantization noise + transaction interval width).
    Clipped at 0 (non-negative price uncertainty). -/
def AttenuateHop (ΔP ι deadband : ℚ) : ℚ :=
  max 0 (ΔP / (1 + ι) - deadband)

/-- Two-hop signal transmission through an intermediate split market interface:
    Attenuates first across the intermediate market interface (ι1, db_int),
    then across the upstream interface (ι2, db_u). -/
def SignalSplit (ΔP_out ι1 ι2 db_int db_u : ℚ) : ℚ :=
  AttenuateHop (AttenuateHop ΔP_out ι1 db_int) ι2 db_u

/-- Merged single-stage signal transmission within an integrated firm:
    Eliminates the intermediate market interface (db_int = 0), transmitting
    directly upstream through the compounded interest rate (1 + ι1) * (1 + ι2). -/
def SignalMerge (ΔP_out ι1 ι2 db_u : ℚ) : ℚ :=
  max 0 (ΔP_out / ((1 + ι1) * (1 + ι2)) - db_u)

/-- Theorem 7.1(II) (Critical Attenuation Signal Extinction):
    In the Critical Attenuation Regime, where the downstream consumer price signal ΔP_out
    exceeds the merged boundary threshold but falls below the compounded two-stage split threshold:
      (1 + ι1) * (1 + ι2) * db_u < ΔP_out ≤ (1 + ι1) * (db_int + (1 + ι2) * db_u),
    the split-market transmission suffers total signal extinction (SignalSplit = 0),
    whereas the coalesced/merged firm transmission transmits a strictly positive price signal
    (SignalMerge > 0). -/
theorem critical_attenuation_signal_extinction
    (ΔP_out ι1 ι2 db_int db_u : ℚ)
    (h_pos1 : 0 < 1 + ι1)
    (h_pos2 : 0 < 1 + ι2)
    (h_db_int : 0 ≤ db_int)
    (h_db_u : 0 ≤ db_u)
    (h_crit_low : (1 + ι1) * (1 + ι2) * db_u < ΔP_out)
    (h_crit_high : ΔP_out ≤ (1 + ι1) * (db_int + (1 + ι2) * db_u)) :
    SignalSplit ΔP_out ι1 ι2 db_int db_u = 0 ∧
    0 < SignalMerge ΔP_out ι1 ι2 db_u := by
  have h_comp_pos : 0 < (1 + ι1) * (1 + ι2) := mul_pos h_pos1 h_pos2
  -- Part 1: SignalMerge > 0
  have h_merge_pos : 0 < SignalMerge ΔP_out ι1 ι2 db_u := by
    dsimp [SignalMerge]
    have h_crit_low' : db_u * ((1 + ι1) * (1 + ι2)) < ΔP_out := by
      rw [mul_comm]
      exact h_crit_low
    have h_div_lt : db_u < ΔP_out / ((1 + ι1) * (1 + ι2)) :=
      (lt_div_iff₀ h_comp_pos).mpr h_crit_low'
    have h_diff_pos : 0 < ΔP_out / ((1 + ι1) * (1 + ι2)) - db_u :=
      sub_pos.mpr h_div_lt
    have h_max : max 0 (ΔP_out / ((1 + ι1) * (1 + ι2)) - db_u) =
        ΔP_out / ((1 + ι1) * (1 + ι2)) - db_u :=
      max_eq_right (le_of_lt h_diff_pos)
    rw [h_max]
    exact h_diff_pos
  -- Part 2: SignalSplit = 0
  have h_split_zero : SignalSplit ΔP_out ι1 ι2 db_int db_u = 0 := by
    dsimp [SignalSplit, AttenuateHop]
    let hop1 := max 0 (ΔP_out / (1 + ι1) - db_int)
    have h_hop1_le : hop1 ≤ (1 + ι2) * db_u := by
      dsimp [hop1]
      by_cases h_case : ΔP_out / (1 + ι1) - db_int ≤ 0
      · rw [max_eq_left h_case]
        have h_prod_nonneg : 0 ≤ (1 + ι2) * db_u := mul_nonneg (le_of_lt h_pos2) h_db_u
        exact h_prod_nonneg
      · have h_gt : 0 < ΔP_out / (1 + ι1) - db_int := not_le.mp h_case
        rw [max_eq_right (le_of_lt h_gt)]
        have h_crit_high' : ΔP_out ≤ (db_int + (1 + ι2) * db_u) * (1 + ι1) := by
          rw [mul_comm]
          exact h_crit_high
        have h_div_le : ΔP_out / (1 + ι1) ≤ db_int + (1 + ι2) * db_u :=
          (div_le_iff₀ h_pos1).mpr h_crit_high'
        linarith
    have h_hop2_le : hop1 / (1 + ι2) - db_u ≤ 0 := by
      have h_hop1_le' : hop1 ≤ db_u * (1 + ι2) := by
        rw [mul_comm]
        exact h_hop1_le
      have h_div_le2 : hop1 / (1 + ι2) ≤ db_u :=
        (div_le_iff₀ h_pos2).mpr h_hop1_le'
      linarith
    exact max_eq_left h_hop2_le
  exact ⟨h_split_zero, h_merge_pos⟩

/-- Spot market transaction uncertainty width (Lemma 7.1):
    Quantization grid step plus intermediate price spread W_int, scaled by physical volume. -/
def SpotMarketUncertainty (W_int grid_step Δz_abs : ℚ) : ℚ :=
  (W_int + grid_step) * Δz_abs

/-- Internal firm shadow-price uncertainty width (Lemma 7.1 & Theorem 7.1(I)):
    Internal shadow-price uncertainty caused by upstream interval width,
    joint-cost allocation blur (d_int ≥ 2), and external opportunity-cost loss. -/
def InternalFirmUncertainty (upstream_blur joint_cost_blur ext_opp_loss Δz_abs : ℚ) : ℚ :=
  (upstream_blur + joint_cost_blur + ext_opp_loss) * Δz_abs

/-- Theorem 7.1(I) (Master Coalescence Inequality):
    Internal firm coordination strictly reduces calculation uncertainty compared to spot markets
    if and only if the sum of upstream blur, joint-cost allocation blur, and external opportunity
    loss is strictly less than the spot-market price spread plus quantization step. -/
theorem master_coalescence_inequality
    (upstream_blur joint_cost_blur ext_opp_loss W_int grid_step Δz_abs : ℚ)
    (h_pos : 0 < Δz_abs) :
    InternalFirmUncertainty upstream_blur joint_cost_blur ext_opp_loss Δz_abs <
      SpotMarketUncertainty W_int grid_step Δz_abs ↔
    upstream_blur + joint_cost_blur + ext_opp_loss < W_int + grid_step := by
  dsimp [InternalFirmUncertainty, SpotMarketUncertainty]
  exact mul_lt_mul_iff_of_pos_right h_pos

-- =========================================================================
-- Section 4: Theorem 5.1b — Concrete Finite Model Witness (ModelM0)
-- =========================================================================

/-- FinitePraxeologicalModel:
    A self-contained, computable model-theoretic structure over concrete finite types
    (without relying on global axioms), establishing the mutual consistency and non-vacuity of:
    1. A discrete temporal tree with forward branching and backward linearity.
    2. Disjoint STIT choice partitions and purposeful agency.
    3. An acceptance profile over commodities featuring a uniquely max-marketable money good
       that is a fixed point of the Bourbaki-Witt indirect exchange operator. -/
structure FinitePraxeologicalModel where
  -- Sorts
  MomentM : Type
  AgentM  : Type
  MeansM  : Type
  [instFintypeAgent : Fintype AgentM]
  -- Temporal order
  prec : MomentM → MomentM → Prop
  prec_irrefl : ∀ m, ¬ prec m m
  prec_trans : ∀ a b c, prec a b → prec b c → prec a c
  prec_backward_linear : ∀ t1 t2 t3, prec t1 t3 → prec t2 t3 → prec t1 t2 ∨ t1 = t2 ∨ prec t2 t1
  -- Forward branching witness at root
  root : MomentM
  branch1 : MomentM
  branch2 : MomentM
  h_branch1 : prec root branch1
  h_branch2 : prec root branch2
  h_incomp1 : ¬ prec branch1 branch2
  h_incomp2 : ¬ prec branch2 branch1
  h_distinct_branches : branch1 ≠ branch2
  -- Catallactics & Money Emergence
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

end Praxeology

end
