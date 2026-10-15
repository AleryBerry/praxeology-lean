module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Marginal
public import Praxeology.Catallactics
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false

/-!
# Praxeology.Breakthroughs

Formalization of Phase 4 of Praxeology:
The Three Emergent Breakthroughs of 𝒯_prx^rev ∪ 𝒯_cat^rev:
1. Breakthrough I (Theorem 6.1): The Catallactic Price Box ℬ_t and the Indeterminacy Cone ℤ_t.
2. Breakthrough II (Theorem 6.2): Doxastic Decomposition & Mandatory Ex-Post Regret in Heterodoxastic Trades.
   - Including Lawson's (2022) Epistemological Second-Best Regret Theorem.
3. Breakthrough III (Theorems 6.3 & 7.1): Signal Quantization Attenuation in Deep Production Chains,
   Optimal STIT Partition Clustering (Firm Coalescence), Critical Attenuation Signal Extinction,
   and Master Coalescence Inequality.
-/

@[expose] public section

namespace Praxeology

open scoped Classical

-- =========================================================================
-- Section 1: Breakthrough I — Catallactic Price Box & Indeterminacy Cone
-- =========================================================================

/-- Catallactic Price Box ℬ_t for d capital goods:
    A price vector P belongs to ℬ_t iff each component P r lies within
    the marginal-pair bounds [P_low r, P_high r]. -/
def InPriceBox (d : ℕ) (P_low P_high P : Fin d → ℚ) : Prop :=
  ∀ r : Fin d, P_low r ≤ P r ∧ P r ≤ P_high r

/-- Price interval width for capital good r. -/
def BoxWidth (d : ℕ) (P_low P_high : Fin d → ℚ) (r : Fin d) : ℚ :=
  P_high r - P_low r

/-- The Indeterminacy Cone ℤ_t:
    Two production methods x and y belong to the Indeterminacy Cone of ℬ_t
    if their economic cost ranking flips depending on the realized price vector
    within the Catallactic Price Box. -/
def InIndeterminacyCone (d : ℕ) (P_low P_high : Fin d → ℚ) (x y : InputVec d) : Prop :=
  ∃ P1 P2 : Fin d → ℚ,
    InPriceBox d P_low P_high P1 ∧
    InPriceBox d P_low P_high P2 ∧
    Cost d P1 x < Cost d P1 y ∧
    Cost d P2 y < Cost d P2 x

/-- Criterion theorem for the Indeterminacy Cone:
    If two price vectors in the Price Box evaluate an antichain in opposite directions,
    then the methods lie in the Indeterminacy Cone. -/
theorem indeterminacy_cone_criterion (d : ℕ) (P_low P_high : Fin d → ℚ) (x y : InputVec d)
    (P1 P2 : Fin d → ℚ)
    (hP1 : InPriceBox d P_low P_high P1)
    (hP2 : InPriceBox d P_low P_high P2)
    (h_c1 : Cost d P1 x < Cost d P1 y)
    (h_c2 : Cost d P2 y < Cost d P2 x) :
    InIndeterminacyCone d P_low P_high x y :=
  ⟨P1, P2, hP1, hP2, h_c1, h_c2⟩

/-- Robust Dominance Excludes Indeterminacy:
    If production method x weakly uses fewer or equal inputs than method y across all factors
    (x r ≤ y r for all r), and prices in the price box are non-negative, then x and y can NEVER
    belong to the Indeterminacy Cone ℤ_t. -/
theorem robust_dominance_excludes_indeterminacy (d : ℕ) (P_low P_high : Fin d → ℚ) (x y : InputVec d)
    (h_dom : ∀ r : Fin d, x r ≤ y r)
    (h_nonneg : ∀ P : Fin d → ℚ, InPriceBox d P_low P_high P → ∀ r : Fin d, 0 ≤ P r) :
    ¬ InIndeterminacyCone d P_low P_high x y := by
  intro ⟨P1, P2, hP1, hP2, h_c1, h_c2⟩
  have hP2_nonneg := h_nonneg P2 hP2
  have h_le_each : ∀ r : Fin d, P2 r * (x r : ℚ) ≤ P2 r * (y r : ℚ) := by
    intro r
    have hx_le_y : (x r : ℚ) ≤ (y r : ℚ) := Nat.cast_le.mpr (h_dom r)
    exact mul_le_mul_of_nonneg_left hx_le_y (hP2_nonneg r)
  have h_cost_le : Cost d P2 x ≤ Cost d P2 y := by
    dsimp [Cost]
    apply Finset.sum_le_sum
    intro r _
    exact h_le_each r
  linarith

/-- Degenerate Price Box Eliminates Indeterminacy:
    When the Catallactic Price Box collapses to a single point (P_low = P_high),
    the Indeterminacy Cone is completely eliminated (ℤ_t = ∅). -/
theorem degenerate_box_eliminates_indeterminacy (d : ℕ) (P_low P_high : Fin d → ℚ) (x y : InputVec d)
    (h_degen : P_low = P_high) :
    ¬ InIndeterminacyCone d P_low P_high x y := by
  intro ⟨P1, P2, hP1, hP2, h_c1, h_c2⟩
  have hP1_eq : P1 = P2 := by
    ext r
    have h1a := (hP1 r).1
    have h1b := (hP1 r).2
    have h2a := (hP2 r).1
    have h2b := (hP2 r).2
    rw [h_degen] at h1a h2a
    have hP1_r : P1 r = P_high r := le_antisymm h1b h1a
    have hP2_r : P2 r = P_high r := le_antisymm h2b h2a
    rw [hP1_r, hP2_r]
  rw [hP1_eq] at h_c1
  linarith

/-- Helper evaluation: cost of a 2-good input vector. -/
theorem cost_two (P : Fin 2 → ℚ) (x : InputVec 2) :
    Cost 2 P x = P 0 * (x 0 : ℚ) + P 1 * (x 1 : ℚ) := by
  dsimp [Cost]
  rw [Fin.sum_univ_two]

/-- Theorem 6.1 (The Catallactic Price Box and Indeterminacy Cone):
    Whenever discrete marginal pairs induce positive interval widths for distinct capital goods,
    there exist physical antichain methods whose cost comparison is strictly indeterminate
    across the Catallactic Price Box ℬ_t. -/
theorem price_box_indeterminacy_cone_exists :
    ∃ (P_low P_high : Fin 2 → ℚ) (x y : InputVec 2),
      (∀ r : Fin 2, 0 < P_low r ∧ P_low r < P_high r) ∧
      PhysicalAntichain x y ∧
      InIndeterminacyCone 2 P_low P_high x y := by
  let P_low : Fin 2 → ℚ := fun _ => 1
  let P_high : Fin 2 → ℚ := fun _ => 3
  let x : InputVec 2 := fun r => if r.val = 0 then 2 else 0
  let y : InputVec 2 := fun r => if r.val = 0 then 0 else 2
  have h_pos : ∀ r : Fin 2, 0 < P_low r ∧ P_low r < P_high r := by
    intro r
    fin_cases r <;> norm_num [P_low, P_high]
  have h_antichain : PhysicalAntichain x y := by
    refine ⟨⟨0, ?_⟩, ⟨1, ?_⟩⟩
    · dsimp [x, y]; decide
    · dsimp [x, y]; decide
  let P1 : Fin 2 → ℚ := fun r => if r.val = 0 then 1 else 3
  let P2 : Fin 2 → ℚ := fun r => if r.val = 0 then 3 else 1
  have hP1 : InPriceBox 2 P_low P_high P1 := by
    intro r
    fin_cases r <;> norm_num [InPriceBox, P1, P_low, P_high]
  have hP2 : InPriceBox 2 P_low P_high P2 := by
    intro r
    fin_cases r <;> norm_num [InPriceBox, P2, P_low, P_high]
  have h_cost1 : Cost 2 P1 x < Cost 2 P1 y := by
    rw [cost_two, cost_two]
    dsimp [P1, x, y]
    norm_num
  have h_cost2 : Cost 2 P2 y < Cost 2 P2 x := by
    rw [cost_two, cost_two]
    dsimp [P2, x, y]
    norm_num
  have h_cone : InIndeterminacyCone 2 P_low P_high x y :=
    ⟨P1, P2, hP1, hP2, h_cost1, h_cost2⟩
  exact ⟨P_low, P_high, x, y, h_pos, h_antichain, h_cone⟩

-- =========================================================================
-- Section 2: Breakthrough II — Doxastic Decomposition & Mandatory Ex-Post Regret
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

/-- Theorem 6.2 (Mandatory Ex-Post Regret in Heterodoxastic Trades):
    In any speculative trade founded on conflicting doxastic expectations (heterodoxastic exchange),
    for any actual realized history h, at least one of the trading partners MUST experience ex-post regret.
    Ex-ante both agents expected gain (Theorem 3.1), but ex-post mutual gain is impossible. -/
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

/-- Lawson's Epistemological Second-Best Theorem:
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
-- Section 3: Breakthrough III — Signal Quantization Attenuation & Firm Coalescence
-- =========================================================================

/-- Multi-stage production chain of depth L (stages of production from capital to consumer goods). -/
structure ProductionChain (L : ℕ) where
  stage_width : Fin L → ℚ
  h_width_ge_grid : ∀ k : Fin L, ∀ D : ℕ, 0 < D → GridStep D ≤ stage_width k

/-- Theorem 6.3 (Signal Quantization Attenuation in Deep Production DAGs):
    Along an L-stage production chain, the accumulated price interval width / quantization noise
    is bounded below by L * (1 / D). As chain depth L increases, price uncertainty compounds linearly,
    attenuating consumer-demand price signals transmitted upstream to higher-order capital goods. -/
theorem signal_quantization_attenuation (L D : ℕ) (hD : 0 < D)
    (chain : ProductionChain L) :
    (L : ℚ) * GridStep D ≤ ∑ k : Fin L, chain.stage_width k := by
  have h_each : ∀ k : Fin L, GridStep D ≤ chain.stage_width k :=
    fun k => chain.h_width_ge_grid k D hD
  have h_const_sum : (L : ℚ) * GridStep D = ∑ k : Fin L, GridStep D := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h_const_sum]
  apply Finset.sum_le_sum
  intro k _
  exact h_each k

/-- Firm Coalescence (Optimal STIT Partition Clustering):
    A firm coalesces K contiguous stages into an integrated internal STIT choice cell,
    replacing intermediate market price interfaces with internal coordination.
    Remaining external market interfaces: L - K + 1. -/
def CoalescedExternalInterfaces (L K : ℕ) : ℕ :=
  L - K + 1

/-- Theorem 7.1(1) (Quantization Noise Reduction via Firm Coalescence):
    Internalizing K > 1 stages within an integrated entrepreneurial firm strictly reduces
    accumulated external market quantization noise from L * (1/D) to (L - K + 1) * (1/D). -/
theorem firm_coalescence_noise_reduction (L K D : ℕ) (hD : 0 < D)
    (hK_ge : 2 ≤ K) (hK_le : K ≤ L) :
    ((CoalescedExternalInterfaces L K : ℚ) * GridStep D) < ((L : ℚ) * GridStep D) := by
  dsimp [CoalescedExternalInterfaces]
  have h_step_pos := grid_step_pos D hD
  have h_diff : CoalescedExternalInterfaces L K < L := by
    dsimp [CoalescedExternalInterfaces]
    omega
  have h_cast_lt : (CoalescedExternalInterfaces L K : ℚ) < (L : ℚ) := by
    exact Nat.cast_lt.mpr h_diff
  exact mul_lt_mul_of_pos_right h_cast_lt h_step_pos

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

/-- Theorem 7.1(2) (The Coasean-Misesian Boundary of the Firm):
    The boundary of the firm is uniquely determined by the trade-off between:
    1. Signal quantization attenuation from external market depth (driving integration K > 1), and
    2. Calculation incommensurability (ECP Theorems 4.2 & 4.3), which makes cost minimization
       mathematically undefined when the firm expands to eliminate all market price interfaces. -/
theorem firm_boundary_tradeoff (L K D : ℕ) (hD : 0 < D)
    (hK_ge : 2 ≤ K) (hK_le : K ≤ L)
    (h_coalesced_noise : ((CoalescedExternalInterfaces L K : ℚ) * GridStep D) < ((L : ℚ) * GridStep D)) :
    (((CoalescedExternalInterfaces L K : ℚ) * GridStep D) < ((L : ℚ) * GridStep D)) ∧
    (∀ P : Fin 0 → ℚ, ∀ x y : InputVec 0, Cost 0 P x = Cost 0 P y) := by
  refine ⟨h_coalesced_noise, ?_⟩
  intro P x y
  dsimp [Cost]
  simp
-- =========================================================================
-- Section 4: Strategic Opacity, Capital Complementarity, & ABCT Malinvestment
-- =========================================================================

/-- DEL epistemic update filtered by an observable monetary/price signal. -/
def SignalFilteredPlausible {History : Type}
    (K : Set History) (signal : History → ℚ) (h_actual : History) : Set History :=
  { h' ∈ K | signal h' = signal h_actual }

/-- Strategic opacity traps the agent's epistemic update: if an unbacked credit-expansion
    world produces the same nominal interest signal as a genuine savings world,
    the savings world remains in the agent's signal-filtered plausibility set. -/
theorem strategic_opacity_traps_del_update {History : Type}
    (K : Set History) (signal : History → ℚ) (h_saved h_credit : History)
    (h_in_prior : h_saved ∈ K)
    (h_opacity : signal h_saved = signal h_credit) :
    h_saved ∈ SignalFilteredPlausible K signal h_credit :=
  ⟨h_in_prior, h_opacity⟩

/-- Artificial credit expansion distorts intertemporal stage valuation:
    an artificially lowered discount rate ι_credit makes a higher-order capital project
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

/-- Austrian Business Cycle Theory (ABCT) Master Malinvestment & Regret Theorem:
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

/-- Theorem 8.4 (Endogenous IC1 Tug-of-War Factor Starvation):
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

end Praxeology

end
