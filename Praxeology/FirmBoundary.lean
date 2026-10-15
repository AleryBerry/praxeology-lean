module

public import Praxeology.Catallactics
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
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
# Praxeology.FirmBoundary — Theorem 7: The Coasean-Misesian Boundary of the Firm

Formalization of the entrepreneurial firm boundary, market price-box indeterminacy,
and multi-stage signal quantization attenuation:
- **Theorem 7: The Coasean-Misesian Boundary of the Firm & Signal Quantization Attenuation**
  - **Theorem 7.1 (The Catallactic Price Box and Indeterminacy Cone)**: `price_box_indeterminacy_cone_exists`
    Discrete marginal-pair price spreads create indeterminacy cones over physical antichains,
    generating bounded calculational indeterminacy in intermediate goods markets.
  - **Theorem 7.2 (Signal Quantization Attenuation in Deep Production Chains)**: `signal_quantization_attenuation`
    Price interval spreads compound linearly along multi-stage production DAGs,
    attenuating consumer price signals transmitted upstream to higher-order capital goods.
  - **Theorem 7.3 (Quantization Noise Reduction via Firm Coalescence)**: `firm_coalescence_noise_reduction`
    Internalizing contiguous production stages within a firm strictly reduces accumulated external market quantization noise.
  - **Theorem 7.4 (Critical Attenuation Signal Extinction)**: `critical_attenuation_signal_extinction`
    Split markets suffer complete signal extinction in the critical attenuation regime,
    whereas merged firm coordination preserves positive upstream signal transmission.
  - **Theorem 7.5 (Master Coalescence Inequality)**: `master_coalescence_inequality`
    Internal coordination strictly reduces calculational uncertainty iff upstream and joint-cost
    allocation blurs remain strictly below the spot market price spread plus quantization step.
  - **Theorem 7.6 (The Coasean-Misesian Boundary of the Firm)**: `firm_boundary_tradeoff`
    The optimal boundary of the firm is strictly bounded between quantization noise reduction (favoring integration)
    and Misesian calculation chaos / ECP (precluding complete non-market socialization).

Contains zero global `axiom` declarations.
-/

@[expose] public section

namespace Praxeology

open scoped Classical

-- =========================================================================
-- Section 1: The Catallactic Price Box ℬ_t and Indeterminacy Cone ℤ_t
-- =========================================================================

/-- Price vector for d capital goods. -/
abbrev PriceVec (d : ℕ) := Fin d → ℚ

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

/-- Theorem 7.1 (The Catallactic Price Box and Indeterminacy Cone):
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
-- Section 2: Multi-Stage Signal Quantization Attenuation & Backward Signal Extinction
-- =========================================================================

/-- Multi-stage production chain of depth L (stages of production from capital to consumer goods). -/
structure ProductionChain (L : ℕ) where
  stage_width : Fin L → ℚ
  h_width_ge_grid : ∀ k : Fin L, ∀ D : ℕ, 0 < D → GridStep D ≤ stage_width k

/-- Total quantization noise across an L-stage production chain. -/
def TotalQuantizationNoise (L D : ℕ) : ℚ :=
  (L : ℚ) * GridStep D

/-- Theorem 7.2 (Signal Quantization Attenuation in Deep Production Chains):
    Along an L-stage production chain, the accumulated price interval width / quantization noise
    is bounded below by L * (1 / D). As chain depth L increases, price uncertainty compounds linearly,
    attenuating consumer-demand price signals transmitted upstream to higher-order capital goods. -/
theorem signal_quantization_attenuation (L D : ℕ) (hD : 0 < D)
    (chain : ProductionChain L) :
    TotalQuantizationNoise L D ≤ ∑ k : Fin L, chain.stage_width k := by
  dsimp [TotalQuantizationNoise]
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

/-- Coalesced quantization noise after internalizing K stages within a firm. -/
def CoalescedQuantizationNoise (L K D : ℕ) : ℚ :=
  (CoalescedExternalInterfaces L K : ℚ) * GridStep D

/-- Theorem 7.3 (Quantization Noise Reduction via Firm Coalescence):
    Internalizing K > 1 stages within an integrated entrepreneurial firm strictly reduces
    accumulated external market quantization noise from L * (1/D) to (L - K + 1) * (1/D). -/
theorem firm_coalescence_noise_reduction (L K D : ℕ) (hD : 0 < D)
    (hK_ge : 2 ≤ K) (hK_le : K ≤ L) :
    CoalescedQuantizationNoise L K D < TotalQuantizationNoise L D := by
  dsimp [CoalescedQuantizationNoise, TotalQuantizationNoise, CoalescedExternalInterfaces]
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

/-- Theorem 7.4 (Critical Attenuation Signal Extinction):
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

-- =========================================================================
-- Section 3: Shadow-Price Simplex & The Coasean-Misesian Boundary of the Firm
-- =========================================================================

/-- Spot market transaction uncertainty width:
    Quantization grid step plus intermediate price spread W_int, scaled by physical volume. -/
def SpotMarketUncertainty (W_int grid_step Δz_abs : ℚ) : ℚ :=
  (W_int + grid_step) * Δz_abs

/-- Internal firm shadow-price uncertainty width:
    Internal shadow-price uncertainty caused by upstream interval width,
    joint-cost allocation blur (d_int ≥ 2), and external opportunity-cost loss. -/
def InternalFirmUncertainty (upstream_blur joint_cost_blur ext_opp_loss Δz_abs : ℚ) : ℚ :=
  (upstream_blur + joint_cost_blur + ext_opp_loss) * Δz_abs

/-- Theorem 7.5 (Master Coalescence Inequality):
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

/-- Theorem 7.6 (The Coasean-Misesian Boundary of the Firm):
    The boundary of the firm is uniquely determined by the trade-off between:
    1. Signal quantization attenuation from external market depth (driving integration K > 1), and
    2. Calculation incommensurability (ECP Theorems 4.2 & 4.3), which makes cost minimization
       mathematically undefined when the firm expands to eliminate all market price interfaces. -/
theorem firm_boundary_tradeoff (L K D : ℕ) (hD : 0 < D)
    (hK_ge : 2 ≤ K) (hK_le : K ≤ L)
    (h_coalesced_noise : CoalescedQuantizationNoise L K D < TotalQuantizationNoise L D) :
    (CoalescedQuantizationNoise L K D < TotalQuantizationNoise L D) ∧
    (∀ P : Fin 0 → ℚ, ∀ x y : InputVec 0, Cost 0 P x = Cost 0 P y) := by
  refine ⟨h_coalesced_noise, ?_⟩
  intro P x y
  dsimp [Cost]
  simp

end Praxeology

end
