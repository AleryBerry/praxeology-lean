/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Catallactics
public import Praxeology.Production
public import Praxeology.Organization
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# Firm Boundary: Calculation, Coasean Costs, and Conglomeration

This module formalizes the economic calculation problem within the firm,
the Coase-Rothbard boundary of the firm, and the impossibility of universal
socialist planning/artificial conglomeration.
-/

@[expose] public section



namespace Praxeology


-- Section 1: Price Boxes and Indeterminacy


/-- A price for each of `d` goods. -/
abbrev PriceVec (d : ℕ) := Fin d → ℕ

/-- A price vector whose components lie between the corresponding lower and upper bounds. -/
def InPriceBox (d : ℕ) (P_low P_high P : Fin d → ℕ) : Prop :=
  ∀ r : Fin d, P_low r ≤ P r ∧ P r ≤ P_high r

def InIndeterminacyCone (d : ℕ) (P_low P_high : Fin d → ℕ) (x y : InputVec d) : Prop :=
  ∃ P1 P2 : Fin d → ℕ,
    InPriceBox d P_low P_high P1 ∧
    InPriceBox d P_low P_high P2 ∧
    Cost d P1 x < Cost d P1 y ∧
    Cost d P2 y < Cost d P2 x


theorem indeterminacy_cone_criterion (d : ℕ) (P_low P_high : Fin d → ℕ) (x y : InputVec d)
    (P1 P2 : Fin d → ℕ)
    (hP1 : InPriceBox d P_low P_high P1)
    (hP2 : InPriceBox d P_low P_high P2)
    (h_c1 : Cost d P1 x < Cost d P1 y)
    (h_c2 : Cost d P2 y < Cost d P2 x) :
    InIndeterminacyCone d P_low P_high x y :=
  ⟨P1, P2, hP1, hP2, h_c1, h_c2⟩


theorem robust_dominance_excludes_indeterminacy
    (d : ℕ) (P_low P_high : Fin d → ℕ) (x y : InputVec d)
    (h_dom : ∀ r : Fin d, x r ≤ y r) :
    ¬ InIndeterminacyCone d P_low P_high x y := by
  intro ⟨_, P2, _, hP2, _, h_c2⟩
  have h_le_each : ∀ r : Fin d, P2 r * x r ≤ P2 r * y r := by
    intro r
    exact Nat.mul_le_mul_left (P2 r) (h_dom r)
  have h_cost_le : Cost d P2 x ≤ Cost d P2 y := by
    dsimp [Cost]
    apply Finset.sum_le_sum
    intro r _
    exact h_le_each r
  omega


theorem hayekian_epistemic_compression
    {Ω : Type*} {d : ℕ} (P_low P_high : PriceVec d)
    (P_realized : Ω → PriceVec d)
    (h_realized_in_box : ∀ ω : Ω, InPriceBox d P_low P_high (P_realized ω))
    (x y : Fin d → ℕ)
    (h_robust : ∑ r : Fin d, x r * P_high r < ∑ r : Fin d, y r * P_low r) :
    ∀ ω : Ω, Cost d (P_realized ω) x < Cost d (P_realized ω) y := by
  intro ω
  have h_box := h_realized_in_box ω
  have h_le_x : Cost d (P_realized ω) x ≤ ∑ r : Fin d, x r * P_high r := by
    dsimp [Cost]
    have : (∑ r : Fin d, P_realized ω r * x r) = (∑ r : Fin d, x r * P_realized ω r) := by
      apply Finset.sum_congr rfl; intro r _; rw [Nat.mul_comm]
    rw [this]
    apply Finset.sum_le_sum
    intro r _
    exact Nat.mul_le_mul_left (x r) (h_box r).2
  have h_le_y : ∑ r : Fin d, y r * P_low r ≤ Cost d (P_realized ω) y := by
    dsimp [Cost]
    have : (∑ r : Fin d, P_realized ω r * y r) = (∑ r : Fin d, y r * P_realized ω r) := by
      apply Finset.sum_congr rfl; intro r _; rw [Nat.mul_comm]
    rw [this]
    apply Finset.sum_le_sum
    intro r _
    exact Nat.mul_le_mul_left (y r) (h_box r).1
  omega


theorem kirznerian_arbitrage_contracts_cone
    {d : ℕ} (P_low P_high P_low' P_high' : PriceVec d)
    (h_tighten_low : ∀ r : Fin d, P_low r ≤ P_low' r)
    (h_tighten_high : ∀ r : Fin d, P_high' r ≤ P_high r)
    (x y : Fin d → ℕ) :
    InIndeterminacyCone d P_low' P_high' x y → InIndeterminacyCone d P_low P_high x y := by
  rintro ⟨p1, p2, hp1_box, hp2_box, h_lt1, h_lt2⟩
  have hp1_outer : InPriceBox d P_low P_high p1 := fun r =>
    ⟨le_trans (h_tighten_low r) (hp1_box r).left, le_trans (hp1_box r).right (h_tighten_high r)⟩
  have hp2_outer : InPriceBox d P_low P_high p2 := fun r =>
    ⟨le_trans (h_tighten_low r) (hp2_box r).left, le_trans (hp2_box r).right (h_tighten_high r)⟩
  exact ⟨p1, p2, hp1_outer, hp2_outer, h_lt1, h_lt2⟩


theorem degenerate_box_eliminates_indeterminacy
    (d : ℕ) (P_low P_high : Fin d → ℕ) (x y : InputVec d)
    (h_degen : P_low = P_high) :
    ¬ InIndeterminacyCone d P_low P_high x y := by
  intro ⟨P1, P2, hP1, hP2, h_c1, _h_c2⟩
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
  omega

/-- Cost of a two-good input vector. -/
theorem cost_two (P : Fin 2 → ℕ) (x : InputVec 2) :
    Cost 2 P x = P 0 * x 0 + P 1 * x 1 := by
  dsimp [Cost]
  rw [Fin.sum_univ_two]


theorem price_box_indeterminacy_cone_exists :
    ∃ (P_low P_high : Fin 2 → ℕ) (x y : InputVec 2),
      (∀ r : Fin 2, 0 < P_low r ∧ P_low r < P_high r) ∧
      PhysicalAntichain x y ∧
      InIndeterminacyCone 2 P_low P_high x y := by
  let P_low : Fin 2 → ℕ := fun _ => 1
  let P_high : Fin 2 → ℕ := fun _ => 3
  let x : InputVec 2 := fun r => if r.val = 0 then 2 else 0
  let y : InputVec 2 := fun r => if r.val = 0 then 0 else 2
  have h_pos : ∀ r : Fin 2, 0 < P_low r ∧ P_low r < P_high r := by
    intro r
    fin_cases r <;> decide
  have h_antichain : PhysicalAntichain x y := by
    refine ⟨⟨0, ?_⟩, ⟨1, ?_⟩⟩
    · dsimp [x, y]; decide
    · dsimp [x, y]; decide
  let P1 : Fin 2 → ℕ := fun r => if r.val = 0 then 1 else 3
  let P2 : Fin 2 → ℕ := fun r => if r.val = 0 then 3 else 1
  have hP1 : InPriceBox 2 P_low P_high P1 := by
    intro r
    fin_cases r <;> decide
  have hP2 : InPriceBox 2 P_low P_high P2 := by
    intro r
    fin_cases r <;> decide
  have h_cost1 : Cost 2 P1 x < Cost 2 P1 y := by
    rw [cost_two, cost_two]
    dsimp [P1, x, y]
    decide
  have h_cost2 : Cost 2 P2 y < Cost 2 P2 x := by
    rw [cost_two, cost_two]
    dsimp [P2, x, y]
    decide
  have h_cone : InIndeterminacyCone 2 P_low P_high x y :=
    ⟨P1, P2, hP1, hP2, h_cost1, h_cost2⟩
  exact ⟨P_low, P_high, x, y, h_pos, h_antichain, h_cone⟩


theorem kirznerian_arbitrage_strictly_contracts_cone :
    ∃ (P_low P_high P_low' P_high' : PriceVec 2) (x y : InputVec 2),
      (∀ r, P_low r ≤ P_low' r) ∧
      (∀ r, P_high' r ≤ P_high r) ∧
      PhysicalAntichain x y ∧
      InIndeterminacyCone 2 P_low P_high x y ∧
      ¬ InIndeterminacyCone 2 P_low' P_high' x y := by
  let P_low : PriceVec 2 := fun _ => 1
  let P_high : PriceVec 2 := fun _ => 4
  let P_low' : PriceVec 2 := fun _ => 2
  let P_high' : PriceVec 2 := fun _ => 3
  let x : InputVec 2 := fun r => if r.val = 0 then 3 else 0
  let y : InputVec 2 := fun r => if r.val = 0 then 0 else 5
  have h_tighten_low : ∀ r, P_low r ≤ P_low' r := by
    intro r; fin_cases r <;> decide
  have h_tighten_high : ∀ r, P_high' r ≤ P_high r := by
    intro r; fin_cases r <;> decide
  have h_antichain : PhysicalAntichain x y := by
    refine ⟨⟨0, ?_⟩, ⟨1, ?_⟩⟩
    · dsimp [x, y]; decide
    · dsimp [x, y]; decide
  let P1 : PriceVec 2 := fun r => if r.val = 0 then 1 else 4
  let P2 : PriceVec 2 := fun r => if r.val = 0 then 4 else 1
  have hP1 : InPriceBox 2 P_low P_high P1 := by
    intro r; fin_cases r <;> decide
  have hP2 : InPriceBox 2 P_low P_high P2 := by
    intro r; fin_cases r <;> decide
  have h_cost1 : Cost 2 P1 x < Cost 2 P1 y := by
    rw [cost_two, cost_two]
    dsimp [P1, x, y]
    decide
  have h_cost2 : Cost 2 P2 y < Cost 2 P2 x := by
    rw [cost_two, cost_two]
    dsimp [P2, x, y]
    decide
  have h_cone_outer : InIndeterminacyCone 2 P_low P_high x y :=
    ⟨P1, P2, hP1, hP2, h_cost1, h_cost2⟩
  have h_not_cone_inner : ¬ InIndeterminacyCone 2 P_low' P_high' x y := by
    intro ⟨_p1, p2, _hp1, hp2, _h_lt1, _h_lt2⟩
    have hp2_0 : p2 0 ≤ 3 := (hp2 0).2
    have hp2_1 : 2 ≤ p2 1 := (hp2 1).1
    have h_cost_x : Cost 2 p2 x ≤ 9 := by
      rw [cost_two]
      dsimp [x]
      have : p2 0 * 3 ≤ 3 * 3 := by nlinarith
      omega
    have h_cost_y : 10 ≤ Cost 2 p2 y := by
      rw [cost_two]
      dsimp [y]
      have : 2 * 5 ≤ p2 1 * 5 := by nlinarith
      omega
    omega
  exact ⟨P_low, P_high, P_low', P_high', x, y,
         h_tighten_low, h_tighten_high, h_antichain, h_cone_outer, h_not_cone_inner⟩


theorem kirznerian_menu_expansion_discovery
    [W : ActionFrame]
    (A_old : Finset W.Action) (α_star : W.Action) (h_novel : α_star ∉ A_old)
    (End_of : W.Action → W.Ends)
    (Pref : W.Ends → W.Ends → Prop)
    (h_asymm : ∀ {e1 e2 : W.Ends}, Pref e1 e2 → ¬ Pref e2 e1)
    (h_dom : ∀ β ∈ A_old, Pref (End_of α_star) (End_of β))
    (h_distinct : ∀ β ∈ A_old, End_of α_star ≠ End_of β) :
    let A_new := insert α_star A_old
    A_old ⊂ A_new ∧
    α_star ∈ A_new ∧
    (∀ β ∈ A_old, End_of α_star ≠ End_of β ∧ Pref (End_of α_star) (End_of β)) ∧
    (∀ β ∈ A_new, ¬ Pref (End_of β) (End_of α_star)) ∧
    (∀ γ ∈ A_new, (∀ β ∈ A_new, ¬ Pref (End_of β) (End_of γ)) → γ = α_star) := by
  intro A_new
  refine ⟨Finset.ssubset_insert h_novel, Finset.mem_insert_self α_star A_old, ?_, ?_, ?_⟩
  · intro β hβ
    exact ⟨h_distinct β hβ, h_dom β hβ⟩
  · intro β hβ
    rw [Finset.mem_insert] at hβ
    rcases hβ with rfl | hβ_old
    · intro h_self
      exact h_asymm h_self h_self
    · have h_dom_beta := h_dom β hβ_old
      exact h_asymm h_dom_beta
  · intro γ hγ h_undom
    rw [Finset.mem_insert] at hγ
    rcases hγ with rfl | hγ_old
    · rfl
    · have h_dom_gamma := h_dom γ hγ_old
      have h_star_in : α_star ∈ A_new := Finset.mem_insert_self α_star A_old
      exact (h_undom α_star h_star_in h_dom_gamma).elim


structure BoundedContemplationContext (W : ActionFrame) where
  A_phys : Finset W.Action
  A_cont : Finset W.Action
  End_of : W.Action → W.Ends
  Pref : W.Ends → W.Ends → Prop
  pref_asymm : ∀ {e1 e2 : W.Ends}, Pref e1 e2 → ¬ Pref e2 e1


def BoundedContemplationContext.A_eff [W : ActionFrame]
    (B : BoundedContemplationContext W) : Finset W.Action :=
  B.A_phys ∩ B.A_cont


def KirznerAlertnessOperator [W : ActionFrame]
    (B : BoundedContemplationContext W) (α_star : W.Action) : Finset W.Action :=
  insert α_star B.A_cont


theorem kirznerian_alertness_discovery_expansion
    [W : ActionFrame]
    (B : BoundedContemplationContext W)
    (α_star : W.Action)
    (h_phys : α_star ∈ B.A_phys)
    (h_novel : α_star ∉ B.A_cont)
    (h_dom : ∀ β ∈ B.A_cont, B.Pref (B.End_of α_star) (B.End_of β))
    (h_dist : ∀ β ∈ B.A_cont, B.End_of α_star ≠ B.End_of β) :
    let A_new := KirznerAlertnessOperator B α_star
    let A_new_eff := B.A_phys ∩ A_new
    A_new_eff ⊆ B.A_phys ∧
    B.A_eff ⊂ A_new_eff ∧
    B.A_cont ⊂ A_new ∧
    α_star ∈ A_new_eff ∧
    (∀ β ∈ B.A_cont, B.Pref (B.End_of α_star) (B.End_of β)) ∧
    (∀ β ∈ A_new, ¬ B.Pref (B.End_of β) (B.End_of α_star)) ∧
    (∀ γ ∈ A_new, (∀ β ∈ A_new, ¬ B.Pref (B.End_of β) (B.End_of γ)) → γ = α_star) := by
  intro A_new A_new_eff
  have h_sub_new : A_new_eff ⊆ B.A_phys := Finset.inter_subset_left
  have h_eff_eq : A_new_eff = insert α_star B.A_eff := by
    dsimp [A_new_eff, A_new, KirznerAlertnessOperator, BoundedContemplationContext.A_eff]
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨ha_phys, rfl | ha_cont⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨ha_phys, ha_cont⟩
    · rintro (rfl | ⟨ha_phys, ha_cont⟩)
      · exact ⟨h_phys, Or.inl rfl⟩
      · exact ⟨ha_phys, Or.inr ha_cont⟩
  have h_not_in_eff : α_star ∉ B.A_eff := by
    dsimp [BoundedContemplationContext.A_eff]
    rw [Finset.mem_inter]
    rintro ⟨_, ha_cont⟩
    exact h_novel ha_cont
  have h_eff_ssub : B.A_eff ⊂ A_new_eff := by
    rw [h_eff_eq]
    exact Finset.ssubset_insert h_not_in_eff
  have h_star_in_eff : α_star ∈ A_new_eff := by
    rw [h_eff_eq]
    exact Finset.mem_insert_self α_star B.A_eff
  have ⟨h_ssub, _h_in, h_dom_all, h_undom, h_uniq⟩ :=
    kirznerian_menu_expansion_discovery B.A_cont α_star h_novel B.End_of B.Pref
      (fun h => B.pref_asymm h) h_dom h_dist
  exact ⟨h_sub_new, h_eff_ssub, h_ssub, h_star_in_eff,
    fun β hβ => (h_dom_all β hβ).2, h_undom, h_uniq⟩


def DiscoveryRegret [W : ActionFrame]
    (B : BoundedContemplationContext W)
    (α_chosen : W.Action) (α_overlooked : W.Action) : Prop :=
  α_chosen ∈ B.A_cont ∧
  α_overlooked ∈ B.A_phys ∧
  α_overlooked ∉ B.A_cont ∧
  B.Pref (B.End_of α_overlooked) (B.End_of α_chosen)


theorem discovery_regret_of_overlooked_opportunity
    [W : ActionFrame]
    (B : BoundedContemplationContext W)
    (α_chosen α_overlooked : W.Action)
    (h_chosen : α_chosen ∈ B.A_cont)
    (h_phys : α_overlooked ∈ B.A_phys)
    (h_novel : α_overlooked ∉ B.A_cont)
    (h_pref : B.Pref (B.End_of α_overlooked) (B.End_of α_chosen)) :
    DiscoveryRegret B α_chosen α_overlooked :=
  ⟨h_chosen, h_phys, h_novel, h_pref⟩


-- Section 2: Price Box Inclusion and Production Chains


/-- Price bounds for each of `d` goods. -/
structure OrdinalPriceBox (d : ℕ) where
  low : Fin d → ℕ
  high : Fin d → ℕ
  le : ∀ r : Fin d, low r ≤ high r

/-- Exact width of the ordered interval at coordinate `r`. -/
def OrdinalPriceBox.width {d : ℕ} (B : OrdinalPriceBox d) (r : Fin d) : ℕ :=
  (NatRemainder.ofLE (B.high r) (B.low r) (B.le r)).remaining

theorem OrdinalPriceBox.width_balance {d : ℕ}
    (B : OrdinalPriceBox d) (r : Fin d) :
    B.low r + B.width r = B.high r := by
  exact (NatRemainder.ofLE (B.high r) (B.low r) (B.le r)).balance

/-- `B2` contains the price intervals in `B1`. -/
def BoxCoarsening {d : ℕ} (B1 B2 : OrdinalPriceBox d) : Prop :=
  (∀ r, B2.low r ≤ B1.low r) ∧ (∀ r, B1.high r ≤ B2.high r)

/-- Widening a price box preserves membership in the indeterminacy cone. -/
theorem box_coarsening_widens_indeterminacy_cone {d : ℕ} (B1 B2 : OrdinalPriceBox d)
    (h_coarsen : BoxCoarsening B1 B2) (x y : InputVec d) :
    InIndeterminacyCone d B1.low B1.high x y →
    InIndeterminacyCone d B2.low B2.high x y := by
  rintro ⟨p1, p2, hp1, hp2, hc1, hc2⟩
  refine ⟨p1, p2, ?_, ?_, hc1, hc2⟩
  · intro r
    exact ⟨le_trans (h_coarsen.1 r) (hp1 r).1, le_trans (hp1 r).2 (h_coarsen.2 r)⟩
  · intro r
    exact ⟨le_trans (h_coarsen.1 r) (hp2 r).1, le_trans (hp2 r).2 (h_coarsen.2 r)⟩

/-- A sequence of price boxes whose intervals widen with each stage. -/
structure MultiStageProductionChain (d L : ℕ) where
  box : Fin L → OrdinalPriceBox d
  widening : ∀ (k1 k2 : Fin L), k1.val ≤ k2.val → BoxCoarsening (box k1) (box k2)


theorem upstream_indeterminacy_cone_widening {d L : ℕ} (chain : MultiStageProductionChain d L)
    (k1 k2 : Fin L) (hk : k1.val ≤ k2.val) (x y : InputVec d) :
    InIndeterminacyCone d (chain.box k1).low (chain.box k1).high x y →
    InIndeterminacyCone d (chain.box k2).low (chain.box k2).high x y :=
  box_coarsening_widens_indeterminacy_cone
    (chain.box k1) (chain.box k2) (chain.widening k1 k2 hk) x y

/-- `L` times the grid step. -/
def TotalQuantizationNoise (L grid_step : ℕ) : ℕ :=
  L * grid_step


def CoalescedExternalInterfaces {L K : ℕ} (external : NatRemainder L K) : ℕ :=
  external.remaining + 1

/-- Exact geometry for an incomplete firm integration. `external` carries
the additive stage-count balance, while `externalPositive` records that at
least one interface remains outside the firm. -/
structure FirmCoalescenceGeometry (stages internalized : ℕ) where
  external : NatRemainder stages internalized
  internalizedPositive : 1 ≤ internalized
  externalPositive : 0 < external.remaining

theorem FirmCoalescenceGeometry.incomplete
    {stages internalized : ℕ} (G : FirmCoalescenceGeometry stages internalized) :
    internalized < stages :=
  (NatRemainder.remaining_pos_iff G.external).mp G.externalPositive

/-- If every stage is internalized, the exact external remainder is zero. -/
theorem complete_integration_has_no_external_interface
    {stages : ℕ} (external : NatRemainder stages stages) :
    external.remaining = 0 :=
  (NatRemainder.remaining_eq_zero_iff external).2 rfl

/-- The interface count multiplied by the grid step. -/
def CoalescedQuantizationNoise {L K : ℕ}
    (external : NatRemainder L K) (grid_step : ℕ) : ℕ :=
  CoalescedExternalInterfaces external * grid_step

/-- The coalesced noise is smaller than the total noise. -/
theorem firm_coalescence_noise_reduction {L K : ℕ}
    (external : NatRemainder L K) (grid_step : ℕ) (h_step : 0 < grid_step)
    (hK_ge : 2 ≤ K) :
    CoalescedQuantizationNoise external grid_step < TotalQuantizationNoise L grid_step := by
  have h_diff : external.remaining + 1 < L := by
    have hb := external.balance
    omega
  dsimp [CoalescedQuantizationNoise, TotalQuantizationNoise, CoalescedExternalInterfaces]
  exact Nat.mul_lt_mul_of_pos_right h_diff h_step


def SplitSignalThreshold (R1 R2 db_int db_u : ℕ) : ℕ :=
  R1 * db_int + R1 * R2 * db_u


def MergeSignalThreshold (R1 R2 db_u : ℕ) : ℕ :=
  R1 * R2 * db_u

/-- Split and merge observations compare the spread directly with their exact
cross-multiplied thresholds. -/
def SignalSplit (spread threshold : ℕ) : Bool := decide (threshold < spread)

def SignalMerge (spread threshold : ℕ) : Bool := decide (threshold < spread)


theorem critical_attenuation_signal_extinction
    (ΔP_out R1 R2 db_int db_u : ℕ)
    (_h_pos1 : 1 ≤ R1)
    (_h_pos2 : 1 ≤ R2)
    (h_crit_low : R1 * R2 * db_u < ΔP_out)
    (h_crit_high : ΔP_out ≤ R1 * db_int + R1 * R2 * db_u) :
    SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
    SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true := by
  have hsplit : ¬ R1 * db_int + R1 * R2 * db_u < ΔP_out :=
    Nat.not_lt_of_ge h_crit_high
  exact ⟨by simp [SignalSplit, SplitSignalThreshold, hsplit],
    by simp [SignalMerge, MergeSignalThreshold, h_crit_low]⟩

/-- The spread can remain below the split threshold while crossing the lower
merge threshold, with no quotient or integer rounding involved. -/
theorem exact_signal_threshold_regression :
    SignalSplit 3 (SplitSignalThreshold 1 2 3 1) = false ∧
    SignalMerge 3 (MergeSignalThreshold 1 2 1) = true := by
  norm_num [SignalSplit, SignalMerge, SplitSignalThreshold, MergeSignalThreshold]


-- Section 3: Market Prices and Firm Boundaries


/-- Price spread and grid step, scaled by physical volume. -/
def SpotMarketUncertainty (W_int grid_step Δz_abs : ℕ) : ℕ :=
  (W_int + grid_step) * Δz_abs


def InternalFirmUncertainty (upstream_blur joint_cost_blur ext_opp_loss Δz_abs : ℕ) : ℕ :=
  (upstream_blur + joint_cost_blur + ext_opp_loss) * Δz_abs


theorem master_coalescence_inequality
    (upstream_blur joint_cost_blur ext_opp_loss W_int grid_step Δz_abs : ℕ)
    (h_pos : 0 < Δz_abs) :
    InternalFirmUncertainty upstream_blur joint_cost_blur ext_opp_loss Δz_abs <
      SpotMarketUncertainty W_int grid_step Δz_abs ↔
    upstream_blur + joint_cost_blur + ext_opp_loss < W_int + grid_step := by
  dsimp [InternalFirmUncertainty, SpotMarketUncertainty]
  exact mul_lt_mul_iff_of_pos_right h_pos


theorem firm_boundary_tradeoff (L K grid_step : ℕ) (h_step : 0 < grid_step)
    (hK_ge : 2 ≤ K) (hK_le : K ≤ L) :
    (CoalescedQuantizationNoise (NatRemainder.ofLE L K hK_le) grid_step <
      TotalQuantizationNoise L grid_step) ∧
    (K < L → 0 < (NatRemainder.ofLE L K hK_le).remaining) ∧
    (K = L → (NatRemainder.ofLE L K hK_le).remaining = 0 ∧
      ∃ (φ1 φ2 : Fin 4 → ℕ),
        IsRankPreserving φ1 ∧ IsRankPreserving φ2 ∧
        (φ1 0 + φ1 3 > φ1 1 + φ1 2) ∧
        (φ2 0 + φ2 3 < φ2 1 + φ2 2)) := by
  refine ⟨firm_coalescence_noise_reduction (NatRemainder.ofLE L K hK_le)
    grid_step h_step hK_ge, ?_, ?_⟩
  · intro hKL
    exact (NatRemainder.remaining_pos_iff _).2 hKL
  · intro h_eq
    subst h_eq
    refine ⟨(NatRemainder.remaining_eq_zero_iff _).2 rfl,
      socialist_calculation_incommensurability⟩

/-- Every factor price is positive. -/
def ExternalMarketActive (d : ℕ) (P : PriceVec d) : Prop :=
  ∀ r : Fin d, 0 < P r


theorem positive_prices_and_ordinal_rank_sum_reversal :
    let x : InputVec 2 := fun r => if r.val = 0 then 2 else 1
    let y : InputVec 2 := fun r => if r.val = 0 then 1 else 2
    -- Positive prices give positive costs and a total comparison.
    (∀ P : PriceVec 2, ExternalMarketActive 2 P →
      0 < Cost 2 P x ∧ 0 < Cost 2 P y ∧
      (Cost 2 P x ≤ Cost 2 P y ∨ Cost 2 P y ≤ Cost 2 P x)) ∧
    -- The two rank-preserving functions give opposite rank-sum comparisons.
    (∃ (φ1 φ2 : Fin 4 → ℕ),
      IsRankPreserving φ1 ∧ IsRankPreserving φ2 ∧
      (φ1 0 + φ1 3 > φ1 1 + φ1 2) ∧
      (φ2 0 + φ2 3 < φ2 1 + φ2 2)) := by
  intro x y
  refine ⟨fun P hP => ?_, socialist_calculation_incommensurability⟩
  have hp0 := hP 0
  have hp1 := hP 1
  rw [cost_two P x, cost_two P y]
  have hx0 : x 0 = 2 := rfl
  have hx1 : x 1 = 1 := rfl
  have hy0 : y 0 = 1 := rfl
  have hy1 : y 1 = 2 := rfl
  rw [hx0, hx1, hy0, hy1]
  refine ⟨by omega, by omega, le_total _ _⟩


theorem viable_coalescence_window
    (L K K_min : ℕ)
    (ΔP_out R1 R2 db_u : ℕ)
    (h_K_min : 1 ≤ K_min)
    (h_K_ge : K_min ≤ K)
    (geometry : FirmCoalescenceGeometry L K)
    (h_signal : SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true) :
    1 ≤ K ∧
    SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
    0 < geometry.external.remaining := by
  refine ⟨le_trans h_K_min h_K_ge, h_signal, ?_⟩
  exact geometry.externalPositive


theorem viable_coalescence_noise_and_market_window
    (L K K_min grid_step : ℕ)
    (ΔP_out R1 R2 db_u : ℕ)
    (h_step : 0 < grid_step)
    (h_K_min : 2 ≤ K_min)
    (h_K_ge : K_min ≤ K)
    (geometry : FirmCoalescenceGeometry L K)
    (h_signal : SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true) :
    CoalescedQuantizationNoise
      geometry.external grid_step <
      TotalQuantizationNoise L grid_step ∧
    SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
    0 < geometry.external.remaining := by
  have hK2 : 2 ≤ K := le_trans h_K_min h_K_ge
  let external := geometry.external
  exact ⟨firm_coalescence_noise_reduction external grid_step h_step hK2,
    h_signal, geometry.externalPositive⟩


theorem viable_coalescence_critical_attenuation_window
    (L K K_min grid_step : ℕ)
    (ΔP_out R1 R2 db_int db_u : ℕ)
    (h_step : 0 < grid_step)
    (h_pos1 : 1 ≤ R1)
    (h_pos2 : 1 ≤ R2)
    (h_crit_low : R1 * R2 * db_u < ΔP_out)
    (h_crit_high : ΔP_out ≤ R1 * db_int + R1 * R2 * db_u)
    (h_K_min : 2 ≤ K_min)
    (h_K_ge : K_min ≤ K)
    (geometry : FirmCoalescenceGeometry L K) :
    SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
    SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
    CoalescedQuantizationNoise
      geometry.external grid_step <
      TotalQuantizationNoise L grid_step ∧
    0 < geometry.external.remaining := by
  have ⟨h_split_zero, h_merge_pos⟩ :=
    critical_attenuation_signal_extinction ΔP_out R1 R2 db_int db_u
      h_pos1 h_pos2 h_crit_low h_crit_high
  have hK2 : 2 ≤ K := le_trans h_K_min h_K_ge
  let external := geometry.external
  have h_noise := firm_coalescence_noise_reduction external grid_step h_step hK2
  exact ⟨h_split_zero, h_merge_pos, h_noise,
    geometry.externalPositive⟩

section EntrepreneurialActionFrame

variable [W : ActionFrame]


def FactorCost (Factors : Finset Means) (P : Means → ℕ) (x : Means → ℕ) : ℕ :=
  ∑ m ∈ Factors, P m * x m


def InFactorPriceBox (Factors : Finset Means) (P_low P_high P : Means → ℕ) : Prop :=
  ∀ m ∈ Factors, P_low m ≤ P m ∧ P m ≤ P_high m


def InFactorIndeterminacyCone (Factors : Finset Means) (P_low P_high : Means → ℕ)
    (x y : Means → ℕ) : Prop :=
  ∃ P1 P2 : Means → ℕ,
    InFactorPriceBox Factors P_low P_high P1 ∧
    InFactorPriceBox Factors P_low P_high P2 ∧
    FactorCost Factors P1 x < FactorCost Factors P1 y ∧
    FactorCost Factors P2 y < FactorCost Factors P2 x


theorem factor_indeterminacy_cone_criterion (Factors : Finset Means)
    (P_low P_high : Means → ℕ) (x y : Means → ℕ)
    (P1 P2 : Means → ℕ)
    (hP1 : InFactorPriceBox Factors P_low P_high P1)
    (hP2 : InFactorPriceBox Factors P_low P_high P2)
    (h_c1 : FactorCost Factors P1 x < FactorCost Factors P1 y)
    (h_c2 : FactorCost Factors P2 y < FactorCost Factors P2 x) :
    InFactorIndeterminacyCone Factors P_low P_high x y :=
  ⟨P1, P2, hP1, hP2, h_c1, h_c2⟩


theorem robust_factor_dominance_excludes_indeterminacy
    (Factors : Finset Means) (P_low P_high : Means → ℕ) (x y : Means → ℕ)
    (h_dom : ∀ m ∈ Factors, x m ≤ y m) :
    ¬ InFactorIndeterminacyCone Factors P_low P_high x y := by
  intro ⟨_, P2, _, hP2, _, h_c2⟩
  have h_le_each : ∀ m ∈ Factors, P2 m * x m ≤ P2 m * y m := by
    intro m hm
    exact Nat.mul_le_mul_left (P2 m) (h_dom m hm)
  have h_le_sum : ∑ m ∈ Factors, P2 m * x m ≤ ∑ m ∈ Factors, P2 m * y m :=
    Finset.sum_le_sum h_le_each
  dsimp [FactorCost] at h_c2
  omega


end EntrepreneurialActionFrame


inductive FirmInformationInterface where
  | demandHidden
  | bothSignals
  | factorHidden
  | demandRestored
  | factorRestored
  deriving DecidableEq


abbrev FirmInformationState := Bool × Bool

/-- The first state coordinate is the downstream demand target. -/
def firmDemand (s : FirmInformationState) : Bool := s.1

/-- The second state coordinate is the factor-allocation target. -/
def firmFactor (s : FirmInformationState) : Bool := s.2


def informationObservation : FirmInformationInterface → FirmInformationState → Bool × Bool
  | .demandHidden, s => (false, firmFactor s)
  | .bothSignals, s => s
  | .factorHidden, s => (firmDemand s, false)
  | .demandRestored, s => s
  | .factorRestored, s => s


def firmPriceLevel (baseline transmittedSpread : ℕ) (demand : Bool) : ℕ :=
  baseline + if demand then transmittedSpread else 0

/-- The observation records whether the price exceeds the baseline and the factor coordinate. -/
def firmPriceSignalObservation (visible : Bool)
    (s : FirmInformationState) : Bool × Bool :=
  (visible && firmDemand s, firmFactor s)


theorem firm_price_signal_observation_eq_demand_hidden
    (s : FirmInformationState) :
    firmPriceSignalObservation false s = informationObservation .demandHidden s := by
  rcases s with ⟨demand, factor⟩
  cases demand <;>
    simp [firmPriceSignalObservation, firmDemand, firmFactor, informationObservation]


theorem firm_price_signal_observation_eq_both_signals
    (s : FirmInformationState) :
    firmPriceSignalObservation true s =
      informationObservation .bothSignals s := by
  rcases s with ⟨demand, factor⟩
  cases demand <;> simp [firmPriceSignalObservation, firmDemand, firmFactor,
    informationObservation]


theorem critical_attenuation_observation_equivalences
    (ΔP_out R1 R2 db_int db_u : ℕ)
    (h_pos1 : 1 ≤ R1) (h_pos2 : 1 ≤ R2)
    (h_crit_low : R1 * R2 * db_u < ΔP_out)
    (h_crit_high : ΔP_out ≤ R1 * db_int + R1 * R2 * db_u)
    (s : FirmInformationState) :
    firmPriceSignalObservation
        (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u)) s =
      informationObservation .demandHidden s ∧
    firmPriceSignalObservation
        (SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u)) s =
      informationObservation .bothSignals s := by
  have hsignals := critical_attenuation_signal_extinction ΔP_out R1 R2 db_int db_u
    h_pos1 h_pos2 h_crit_low h_crit_high
  refine ⟨?_, ?_⟩
  · rw [hsignals.1]
    exact firm_price_signal_observation_eq_demand_hidden s
  · rw [hsignals.2]
    exact firm_price_signal_observation_eq_both_signals s

/-- A production decision specifies a demand-facing output and a factor allocation. -/
abbrev FirmProductionDecision := Bool × Bool

/-- The decision required in each state. -/
def firmRequiredDecision (s : FirmInformationState) : FirmProductionDecision :=
  (firmDemand s, firmFactor s)

/-- Two states are related when the channel gives them the same observation. -/
def informationInterfaceKnowledge (org : FirmInformationInterface) :
    KnowledgeRelation Unit FirmInformationState where
  indistinguishable := fun _ s₁ s₂ => informationObservation org s₁ = informationObservation org s₂
  refl := by intro _ s; rfl
  symm := by intro _ s₁ s₂ h; exact h.symm
  trans := by intro _ s₁ s₂ s₃ h₁₂ h₂₃; exact h₁₂.trans h₂₃

/-- A production decision for each information channel and signal. -/
def informationPolicy : FirmInformationInterface → Bool × Bool → FirmProductionDecision
  | .demandHidden, signal => (false, signal.2)
  | .bothSignals, signal => signal
  | .factorHidden, signal => (signal.1, false)
  | .demandRestored, signal => signal
  | .factorRestored, signal => signal

/-- Whether a policy based on this channel chooses the state-required decision. -/
def PolicyCorrect (org : FirmInformationInterface) (s : FirmInformationState) : Prop :=
  informationPolicy org (informationObservation org s) = firmRequiredDecision s

/-- Observing both coordinates supports the correct policy in all four states. -/
theorem both_signals_policy_correct (s : FirmInformationState) :
    PolicyCorrect .bothSignals s := by
  rfl

/-- The `demandRestored` policy selects the required decision in every state. -/
theorem demand_restored_policy_correct (s : FirmInformationState) :
    PolicyCorrect .demandRestored s := by
  rfl

/-- The `factorRestored` policy selects the required decision in every state. -/
theorem factor_restored_policy_correct (s : FirmInformationState) :
    PolicyCorrect .factorRestored s := by
  rfl


theorem demand_hidden_policy_conflict (π : Bool × Bool → FirmProductionDecision) :
    ¬ ∀ s, π (informationObservation .demandHidden s) = firmRequiredDecision s := by
  intro hall
  let πstate : FirmInformationState → FirmProductionDecision :=
    fun s => π (informationObservation .demandHidden s)
  have h_respects : KnowledgeRespectingPolicy
      (informationInterfaceKnowledge .demandHidden) () πstate := by
    intro s₁ s₂ hsame
    exact congrArg π hsame
  have h_required : firmRequiredDecision (false, false) ≠
      firmRequiredDecision (true, false) := by decide
  have h_impossible := no_knowledge_respecting_policy_across_conflict
    (informationInterfaceKnowledge .demandHidden) () πstate firmRequiredDecision
    (false, false) (true, false) (by rfl) h_required
  apply h_impossible
  exact ⟨h_respects, hall⟩


theorem factor_hidden_policy_conflict (π : Bool × Bool → FirmProductionDecision) :
    ¬ ∀ s, π (informationObservation .factorHidden s) = firmRequiredDecision s := by
  intro hall
  let πstate : FirmInformationState → FirmProductionDecision :=
    fun s => π (informationObservation .factorHidden s)
  have h_respects : KnowledgeRespectingPolicy
      (informationInterfaceKnowledge .factorHidden) () πstate := by
    intro s₁ s₂ hsame
    exact congrArg π hsame
  have h_required : firmRequiredDecision (false, false) ≠
      firmRequiredDecision (false, true) := by decide
  have h_impossible := no_knowledge_respecting_policy_across_conflict
    (informationInterfaceKnowledge .factorHidden) () πstate firmRequiredDecision
    (false, false) (false, true) (by rfl) h_required
  apply h_impossible
  exact ⟨h_respects, hall⟩


def firmInformationOutcome (org : FirmInformationInterface) (s : FirmInformationState) : Bool → ℕ :=
  let decision := informationPolicy org (informationObservation org s)
  fun m =>
    if !m then
      if decision.2 = firmFactor s ∧ decision.1 = firmDemand s then 4 else 0
    else if decision.2 = firmFactor s ∧ decision.1 ≠ firmDemand s then 1 else 0

/-- `b1` meets the receipt threshold and `b2` does not. -/
def FirmSaleReceiptProfileGain (b1 b2 : Bool → ℕ) : Prop :=
  3 ≤ b1 false ∧ b2 false < 3

/-- Each hidden-signal profile matches the full-signal profile or has a greater receipt. -/
theorem both_signals_receipt_order (org : FirmInformationInterface) (s : FirmInformationState)
    (horg : org = .demandHidden ∨ org = .factorHidden) :
    firmInformationOutcome org s = firmInformationOutcome .bothSignals s ∨
      FirmSaleReceiptProfileGain (firmInformationOutcome .bothSignals s)
        (firmInformationOutcome org s) := by
  cases horg with
  | inl horg =>
    cases horg
    rcases s with ⟨d, f⟩
    cases d <;> cases f
    · left
      funext m
      cases m <;> rfl
    · left
      funext m
      cases m <;> rfl
    · right
      exact ⟨by decide, by decide⟩
    · right
      exact ⟨by decide, by decide⟩
  | inr horg =>
    cases horg
    rcases s with ⟨d, f⟩
    cases d <;> cases f
    · left
      funext m
      cases m <;> rfl
    · right
      exact ⟨by decide, by decide⟩
    · left
      funext m
      cases m <;> rfl
    · right
      exact ⟨by decide, by decide⟩

/-- Passive retention preserves the two opening cash units and creates no output. -/
def firmRetainedOutcome : Bool → ℕ := fun m => if !m then 2 else 0

/-- The `bothSignals` policy meets the receipt threshold in every state. -/
theorem both_signals_produce_requested_sale (s : FirmInformationState) :
    3 ≤ firmInformationOutcome .bothSignals s false ∧
    firmInformationOutcome .bothSignals s true = 0 := by
  cases s with
  | mk demand factor => cases demand <;> cases factor <;>
      simp [firmInformationOutcome, informationPolicy, informationObservation,
        firmDemand, firmFactor]


theorem firm_information_boundary_policy_witness :
    (∀ s, PolicyCorrect .bothSignals s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .demandHidden s) = firmRequiredDecision s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .factorHidden s) = firmRequiredDecision s) ∧
    (∀ s, PolicyCorrect .demandRestored s) ∧
    (∀ s, PolicyCorrect .factorRestored s) := by
  refine ⟨both_signals_policy_correct, ?_, ?_, demand_restored_policy_correct,
    factor_restored_policy_correct⟩
  · rintro ⟨π, hπ⟩
    exact demand_hidden_policy_conflict π hπ
  · rintro ⟨π, hπ⟩
    exact factor_hidden_policy_conflict π hπ


theorem vertical_integration_stage_count_fallacy_refuted
    (L K : ℕ) (_h_complete_integration : K = L) :
    (∀ s, PolicyCorrect .bothSignals s) ∧
    (∀ s, PolicyCorrect .factorRestored s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .factorHidden s) = firmRequiredDecision s) ∧
    (¬ ∃ π : Bool × Bool → FirmProductionDecision,
      ∀ s, π (informationObservation .demandHidden s) = firmRequiredDecision s) := by
  refine ⟨both_signals_policy_correct, factor_restored_policy_correct, ?_, ?_⟩
  · rintro ⟨π, hπ⟩
    exact factor_hidden_policy_conflict π hπ
  · rintro ⟨π, hπ⟩
    exact demand_hidden_policy_conflict π hπ

section EntrepreneurialActionFrame

variable [W : ActionFrame]
variable {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}

section FirmTrace

variable [BilateralExchangeFrame W]

structure FirmTraceSaleRecipe {i : W.Agent} {α : W.Action}
    {t : W.Moment} {h' : W.History} {hh' : h' ∈ W.MinPlausible i t}
    (R : ProjectedInventoryTrace W i α t h' hh')
    (mCash mProduct : W.Means) (profile : Bool → ℕ) where
  no_production_cash_output : R.run.totalProductionYield mCash = 0
  cash_balance : projectedInitialStock W i α t h' mCash +
      R.run.totalTradeYield mCash = R.run.totalUse mCash + profile false
  no_trade_product_output : R.run.totalTradeYield mProduct = 0
  product_balance : projectedInitialStock W i α t h' mProduct +
      R.run.totalProductionYield mProduct = R.run.totalUse mProduct + profile true

/-- The projected cash and product stocks equal the recipe values. -/
theorem FirmTraceSaleRecipe.stock_values
    {i : Agent} {α : Action} {t : Moment}
    {h' : History} {hh' : h' ∈ W.MinPlausible i t}
    {R : ProjectedInventoryTrace W i α t h' hh'}
    {mCash mProduct : W.Means} {profile : Bool → ℕ}
    (recipe : FirmTraceSaleRecipe R mCash mProduct profile) :
    projectedStock W i α t h' mCash = profile false ∧
      projectedStock W i α t h' mProduct = profile true := by
  constructor
  · change W.omega i
      (W.ExpectedMaturation i α (W.tau i t h')
        (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h') mCash = profile false
    have hbalance := R.run.inventory_balance mCash
    rw [R.run.totalYield_eq_production_add_trade, recipe.no_production_cash_output]
      at hbalance
    have hsum : W.omega i
        (W.ExpectedMaturation i α (W.tau i t h')
          (W.sigma i (W.tau i t h') α h'))
        (W.sigma i (W.tau i t h') α h') mCash + R.run.totalUse mCash =
        profile false + R.run.totalUse mCash := by
      calc
        _ = projectedInitialStock W i α t h' mCash + R.run.totalTradeYield mCash := by
          simpa [projectedInitialStock] using hbalance
        _ = R.run.totalUse mCash + profile false := recipe.cash_balance
        _ = _ := Nat.add_comm _ _
    exact Nat.add_right_cancel hsum
  · change W.omega i
      (W.ExpectedMaturation i α (W.tau i t h')
        (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h') mProduct = profile true
    have hbalance := R.run.inventory_balance mProduct
    rw [R.run.totalYield_eq_production_add_trade, recipe.no_trade_product_output]
      at hbalance
    have hsum : W.omega i
        (W.ExpectedMaturation i α (W.tau i t h')
          (W.sigma i (W.tau i t h') α h'))
        (W.sigma i (W.tau i t h') α h') mProduct + R.run.totalUse mProduct =
        profile true + R.run.totalUse mProduct := by
      calc
        _ = projectedInitialStock W i α t h' mProduct +
            R.run.totalProductionYield mProduct := by
          simpa [projectedInitialStock] using hbalance
        _ = R.run.totalUse mProduct + profile true := recipe.product_balance
        _ = _ := Nat.add_comm _ _
    exact Nat.add_right_cancel hsum

end FirmTrace

/-- Embed the two complementary resources in an arbitrary ActionFrame's means sort. -/
def embedFirmBundle (mA mB : Means) (background : Means → ℕ)
    (b : Bool → ℕ) : Means → ℕ :=
  fun m => if m = mA then b false else if m = mB then b true else background m

/-- The embedded bundle uses the recipe values for the two selected resources. -/
theorem ProjectedInventoryTrace.projectedStock_eq_embedded
    {i : Agent} {α : Action} {t : Moment}
    {h' : W.History} {hh' : h' ∈ W.MinPlausible i t}
    (mA mB : Means) (b : Bool → ℕ)
    (hA : projectedStock W i α t h' mA = b false)
    (hB : projectedStock W i α t h' mB = b true) :
    projectedStock W i α t h' =
      embedFirmBundle mA mB (projectedStock W i α t h') b := by
  have _ : h' ∈ W.MinPlausible i t := hh'
  funext m
  by_cases hmA : m = mA
  · subst m
    simp [embedFirmBundle, hA]
  · by_cases hmB : m = mB
    · subst m
      simp [embedFirmBundle, hmA, hB]
    · simp [embedFirmBundle, hmA, hmB]

/-- The first bundle has at least three cash units; the second has fewer. -/
def FirmSaleReceiptGain (mCash : Means) (b1 b2 : Means → ℕ) : Prop :=
  3 ≤ b1 mCash ∧ b2 mCash < 3

/-- The finite outcome profile entails a physical sale-receipt gain after embedding. -/
theorem embed_firm_sale_receipt_gain (mCash mUnsold : Means)
    (background : Means → ℕ)
    (b1 b2 : Bool → ℕ)
    (hgood : 3 ≤ b1 false) (hbad : b2 false < 3) :
    FirmSaleReceiptGain mCash
      (embedFirmBundle mCash mUnsold background b1)
      (embedFirmBundle mCash mUnsold background b2) := by
  constructor
  · simpa [FirmSaleReceiptGain, embedFirmBundle] using hgood
  · simpa [FirmSaleReceiptGain, embedFirmBundle] using hbad


theorem receipt_end_induces_subjective_bundle_dominance
    (i : Agent) (t : Moment) (h : History) (e : W.Ends)
    (mCash : W.Means)
    (q : ℕ)
    (b1 b2 : W.Means → ℕ)
    (hw : W.ValuedEnd i t h e)
    (honly : ∀ e', W.ValuedEnd i t h e' → e' = e)
    (hreq : ∀ m, W.requirement e m = if m = mCash then q else 0)
    (hgood : q ≤ b1 mCash)
    (hbad : b2 mCash < q) :
    W.SubjectiveTeleologicalDominates i t h b1 b2 := by
  constructor
  · intro S hvalued _hatt
    have hsub : S ⊆ ({e} : Finset W.Ends) := by
      intro w' hw'
      rw [honly w' (hvalued w' hw')]
      simp
    rcases Finset.subset_singleton_iff.mp hsub with hempty | hsingle
    · subst S
      intro m
      simp
    · subst S
      intro m
      by_cases hm : m = mCash
      · simpa [JointlyAttains, hreq, hm] using hgood
      · simp [hreq, hm]
  · refine ⟨{e}, ?_, ?_, ?_⟩
    · intro e' he'
      have heq : e' = e := Finset.mem_singleton.mp he'
      subst e'
      exact hw
    · intro m
      by_cases hm : m = mCash
      · simpa [JointlyAttains, hreq, hm] using hgood
      · simp [hreq, hm]
    · intro hatt
      have hreqCash : W.requirement e mCash = q := by simpa using hreq mCash
      have hbound := hatt mCash
      simp [hreqCash] at hbound
      omega

/-- The embedded bundles preserve the comparison of the two selected resources. -/
theorem embed_firm_bundle_physical_dominance (mA mB : Means) (hne : mA ≠ mB)
    (background : Means → ℕ)
    (b1 b2 : Bool → ℕ)
    (hle : ∀ r, b2 r ≤ b1 r)
    (hstrict : ∃ r, b2 r < b1 r) :
    PhysicalBundleDominates (embedFirmBundle mA mB background b1)
      (embedFirmBundle mA mB background b2) := by
  constructor
  · intro m
    by_cases hmA : m = mA
    · subst m
      simpa [embedFirmBundle] using hle false
    · by_cases hmB : m = mB
      · subst m
        simpa [embedFirmBundle, hmA] using hle true
      · simp [embedFirmBundle, hmA, hmB]
  · rcases hstrict with ⟨r, hr⟩
    cases r
    · refine ⟨mA, ?_⟩
      simpa [embedFirmBundle] using hr
    · refine ⟨mB, ?_⟩
      simpa [embedFirmBundle, hne.symm] using hr

/-- Equal stock profiles have equal embeddings. -/
theorem embed_firm_bundle_eq (mA mB : Means) (b1 b2 : Bool → ℕ)
    (background : Means → ℕ) (h : b1 = b2) :
    embedFirmBundle mA mB background b1 = embedFirmBundle mA mB background b2 := by
  subst b1
  rfl

section InformationGroundedFirm

variable [BilateralExchangeFrame W]

structure InformationGroundedFirmDecision (i : Agent) (t : Moment) (h : History)
    (L K K_min grid_step : ℕ) (ΔP_out R1 R2 db_int db_u : ℕ) where
  α_split : Action
  α_merge : Action
  α_complete : Action
  e_split : Ends
  e_merge : Ends
  e_complete : Ends
  e_retain : Ends
  h_action_end_split : End_of i α_split t h = e_split
  h_action_end_merge : End_of i α_merge t h = e_merge
  h_action_end_complete : End_of i α_complete t h = e_complete
  h_action_end_retain : End_of i α₀ t h = e_retain
  h_feas_split : α_split ∈ A_feas i t h
  h_feas_merge : α_merge ∈ A_feas i t h
  h_feas_complete : α_complete ∈ A_feas i t h
  h_exec_merge : Exec i t α_merge h
  h_at_node : W.mem_hist t h
  h_projected_feasibility : W.ProjectedFeasibility
  h_stock_grounding : ActionFrame.OutcomesGroundedInEndowmentsFor W i
  resourceA : Means
  resourceB : Means
  h_resources_distinct : resourceA ≠ resourceB
  stateOf : History → FirmInformationState
  /-- Observation for each information channel and history. -/
  observationRecord : FirmInformationInterface → History → Bool × Bool


  observation_record_follows_channel : ∀ org h',
    observationRecord org h' = informationObservation org (stateOf h')
  instructionAction : FirmProductionDecision → Action
  state_coverage : ∀ s, ∃ h' ∈ W.MinPlausible i t, stateOf h' = s
  actual_history_plausible : h ∈ W.MinPlausible i t
  trace_split : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    ProjectedInventoryTrace W i α_split t h' hh'
  trace_merge : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    ProjectedInventoryTrace W i α_merge t h' hh'
  trace_complete : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    ProjectedInventoryTrace W i α_complete t h' hh'
  trace_retain : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    ProjectedInventoryTrace W i W.alpha_zero t h' hh'



  recipe_split : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    FirmTraceSaleRecipe (trace_split h' hh') resourceA resourceB
      (firmInformationOutcome .demandHidden (stateOf h'))
  recipe_merge : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    FirmTraceSaleRecipe (trace_merge h' hh') resourceA resourceB
      (firmInformationOutcome .bothSignals (stateOf h'))
  recipe_complete : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    FirmTraceSaleRecipe (trace_complete h' hh') resourceA resourceB
      (firmInformationOutcome .factorHidden (stateOf h'))
  recipe_retain : ∀ h' (hh' : h' ∈ W.MinPlausible i t),
    FirmTraceSaleRecipe (trace_retain h' hh') resourceA resourceB firmRetainedOutcome



  same_inventory_split : ∀ h' (_hh' : h' ∈ W.MinPlausible i t),
    firmInformationOutcome .bothSignals (stateOf h') =
      firmInformationOutcome .demandHidden (stateOf h') →
    projectedStock W i α_merge t h' = projectedStock W i α_split t h'
  same_inventory_complete : ∀ h' (_hh' : h' ∈ W.MinPlausible i t),
    firmInformationOutcome .bothSignals (stateOf h') =
      firmInformationOutcome .factorHidden (stateOf h') →
    projectedStock W i α_merge t h' = projectedStock W i α_complete t h'
  revenueEnd : W.Ends
  h_revenue_end_valued : W.ValuedEnd i t h revenueEnd
  h_only_revenue_end : ∀ w', W.ValuedEnd i t h w' → w' = revenueEnd
  h_revenue_end_requirement : ∀ m,
    W.requirement revenueEnd m = if m = resourceA then 3 else 0
  h_step : 0 < grid_step
  h_pos1 : 1 ≤ R1
  h_pos2 : 1 ≤ R2
  h_crit_low : R1 * R2 * db_u < ΔP_out
  h_crit_high : ΔP_out ≤ R1 * db_int + R1 * R2 * db_u
  h_K_min : 2 ≤ K_min
  h_K_ge : K_min ≤ K
  coalescenceGeometry : FirmCoalescenceGeometry L K
  h_menu : ∀ β ∈ A_feas i t h, β ≠ α_merge →
    End_of i β t h = e_split ∨ End_of i β t h = e_complete ∨ End_of i β t h = e_retain

/-- A veridical projection certificate for firm decisions: asserts that the actual
history `h` is among the plausible scenarios appraised by agent `i` at decision moment `t`.
This bridge is explicit and optional, ensuring that conjectured stocks are never
implicitly equated with actual physical inventory without stating this veridical condition. -/
structure VeridicalFirmProjection (W : ActionFrame) (i : W.Agent)
    (t : W.Moment) (h : W.History) : Prop where
  actual_is_plausible : h ∈ W.MinPlausible i t

/-- Every InformationGroundedFirmDecision carries an explicit veridical projection
certificate for the actual decision history. -/
theorem InformationGroundedFirmDecision.veridical_projection
    (dec : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u) :
    VeridicalFirmProjection W i t h :=
  ⟨dec.actual_history_plausible⟩




theorem InformationGroundedFirmDecision.same_opening_inventory
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (h' : History) (hh' : h' ∈ W.MinPlausible i t) (m : Means) :
    projectedInitialStock W i V.α_merge t h' m =
      projectedInitialStock W i W.alpha_zero t h' m :=
  ProjectedInventoryTrace.common_initial_stock
    (V.trace_merge h' hh') (V.trace_retain h' hh') m

/-- The split policy's stock equals the embedded outcome for its demand-hidden observation. -/
theorem InformationGroundedFirmDecision.stock_split
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (h' : History) (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i V.α_split t h' =
      embedFirmBundle V.resourceA V.resourceB
        (projectedStock W i V.α_split t h')
        (firmInformationOutcome .demandHidden (V.stateOf h')) := by
  have hvalues := (V.recipe_split h' hh').stock_values
  exact ProjectedInventoryTrace.projectedStock_eq_embedded
    (hh' := hh') V.resourceA V.resourceB
    (firmInformationOutcome .demandHidden (V.stateOf h'))
    hvalues.1 hvalues.2

theorem InformationGroundedFirmDecision.stock_merge
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (h' : History) (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i V.α_merge t h' =
      embedFirmBundle V.resourceA V.resourceB
        (projectedStock W i V.α_merge t h')
        (firmInformationOutcome .bothSignals (V.stateOf h')) := by
  have hvalues := (V.recipe_merge h' hh').stock_values
  exact ProjectedInventoryTrace.projectedStock_eq_embedded
    (hh' := hh') V.resourceA V.resourceB
    (firmInformationOutcome .bothSignals (V.stateOf h'))
    hvalues.1 hvalues.2

theorem InformationGroundedFirmDecision.stock_complete
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (h' : History) (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i V.α_complete t h' =
      embedFirmBundle V.resourceA V.resourceB
        (projectedStock W i V.α_complete t h')
        (firmInformationOutcome .factorHidden (V.stateOf h')) := by
  have hvalues := (V.recipe_complete h' hh').stock_values
  exact ProjectedInventoryTrace.projectedStock_eq_embedded
    (hh' := hh') V.resourceA V.resourceB
    (firmInformationOutcome .factorHidden (V.stateOf h'))
    hvalues.1 hvalues.2

theorem InformationGroundedFirmDecision.stock_retain
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (h' : History) (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i W.alpha_zero t h' =
      embedFirmBundle V.resourceA V.resourceB
        (projectedStock W i W.alpha_zero t h') firmRetainedOutcome := by
  have hvalues := (V.recipe_retain h' hh').stock_values
  exact ProjectedInventoryTrace.projectedStock_eq_embedded
    (hh' := hh') V.resourceA V.resourceB firmRetainedOutcome hvalues.1 hvalues.2

/-- The maturation end is the bundle end of the projected stock. -/
theorem information_grounded_maturation_end (V : InformationGroundedFirmDecision i t h
    L K K_min grid_step ΔP_out R1 R2 db_int db_u) (α : Action) (h' : History) :
    W.MaturationEnd i α t h' = W.BundleEnd (projectedStock W i α t h') := by
  change W.OutcomeOf i α (W.tau i t h')
      (W.ExpectedMaturation i α (W.tau i t h')
        (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h') =
    W.BundleEnd (W.omega i
      (W.ExpectedMaturation i α (W.tau i t h')
        (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h'))
  exact V.h_stock_grounding α (W.tau i t h')
    (W.ExpectedMaturation i α (W.tau i t h')
      (W.sigma i (W.tau i t h') α h'))
    (W.sigma i (W.tau i t h') α h')

/-- The merged action has equal stock or a sale-receipt gain relative to the split action. -/
theorem information_stock_order_over_split (V : InformationGroundedFirmDecision i t h
    L K K_min grid_step ΔP_out R1 R2 db_int db_u) (h' : History)
    (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i V.α_merge t h' = projectedStock W i V.α_split t h' ∨
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i V.α_split t h') := by
  have horder := both_signals_receipt_order .demandHidden (V.stateOf h') (Or.inl rfl)
  rcases horder with heq | ⟨hgood, hbad⟩
  · left
    have hsame := V.same_inventory_split h' hh' heq.symm
    exact hsame
  · rw [V.stock_merge h' hh', V.stock_split h' hh']
    apply Or.inr
    constructor
    · simpa [FirmSaleReceiptGain, embedFirmBundle] using hgood
    · simpa [FirmSaleReceiptGain, embedFirmBundle] using hbad


theorem information_stock_order_over_complete (V : InformationGroundedFirmDecision i t h
    L K K_min grid_step ΔP_out R1 R2 db_int db_u) (h' : History)
    (hh' : h' ∈ W.MinPlausible i t) :
    projectedStock W i V.α_merge t h' = projectedStock W i V.α_complete t h' ∨
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i V.α_complete t h') := by
  have horder := both_signals_receipt_order .factorHidden (V.stateOf h') (Or.inr rfl)
  rcases horder with heq | ⟨hgood, hbad⟩
  · left
    have hsame := V.same_inventory_complete h' hh' heq.symm
    exact hsame
  · rw [V.stock_merge h' hh', V.stock_complete h' hh']
    apply Or.inr
    constructor
    · simpa [FirmSaleReceiptGain, embedFirmBundle] using hgood
    · simpa [FirmSaleReceiptGain, embedFirmBundle] using hbad


theorem information_firm_preference_from_stock_order
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u)
    (β : Action) (eβ : Ends)
    (h_endβ : W.End_of i β t h = eβ)
    (h_feasβ : β ∈ W.A_feas i t h)
    (h_order : ∀ h' ∈ W.MinPlausible i t,
      projectedStock W i V.α_merge t h' = projectedStock W i β t h' ∨
        FirmSaleReceiptGain V.resourceA
          (projectedStock W i V.α_merge t h')
          (projectedStock W i β t h'))
    (h_strict : ∃ h' ∈ W.MinPlausible i t,
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i β t h')) :
    W.Preference i t h V.e_merge eβ := by
  have h_app (α : W.Action) (hα : α ∈ W.A_feas i t h) :
      W.ProjectedAppraisable i t α := by
    intro h' hh'
    exact projected_feasibility V.h_projected_feasibility i t h h' α
      V.h_at_node hh' hα
  have h_weak : ∀ h' ∈ W.MinPlausible i t,
      W.MaturationEnd i V.α_merge t h' = W.MaturationEnd i β t h' ∨
        W.Preference i t h (W.MaturationEnd i V.α_merge t h')
          (W.MaturationEnd i β t h') := by
    intro h' hh'
    rcases h_order h' hh' with heq | hdom
    · left
      calc
        W.MaturationEnd i V.α_merge t h' =
            W.BundleEnd (projectedStock W i V.α_merge t h') :=
          information_grounded_maturation_end V V.α_merge h'
        _ = W.BundleEnd (projectedStock W i β t h') := congrArg W.BundleEnd heq
        _ = W.MaturationEnd i β t h' :=
          (information_grounded_maturation_end V β h').symm
    · right
      have happraisal := receipt_end_induces_subjective_bundle_dominance
        i t h V.revenueEnd V.resourceA 3
        (projectedStock W i V.α_merge t h') (projectedStock W i β t h')
        V.h_revenue_end_valued V.h_only_revenue_end
        V.h_revenue_end_requirement hdom.1 hdom.2
      have hpref := W.teleological_bundle_dominance_induces_preference i t h _ _ happraisal
      rw [information_grounded_maturation_end V V.α_merge h',
        information_grounded_maturation_end V β h']
      exact hpref
  rcases h_strict with ⟨h', hh', hdom⟩
  have happraisal := receipt_end_induces_subjective_bundle_dominance
    i t h V.revenueEnd V.resourceA 3
    (projectedStock W i V.α_merge t h') (projectedStock W i β t h')
    V.h_revenue_end_valued V.h_only_revenue_end
    V.h_revenue_end_requirement hdom.1 hdom.2
  have h_strict_outcome :
      W.Preference i t h (W.MaturationEnd i V.α_merge t h') (W.MaturationEnd i β t h') := by
    have hpref := W.teleological_bundle_dominance_induces_preference i t h _ _ happraisal
    rw [information_grounded_maturation_end V V.α_merge h',
      information_grounded_maturation_end V β h']
    exact hpref
  have h_pref := W.doxastic_sure_thing_bridge i V.α_merge β t h
    (by
      intro h' hh'
      exact ⟨h_app V.α_merge V.h_feas_merge h' hh', h_app β h_feasβ h' hh'⟩)
    h_weak ⟨h', hh', h_strict_outcome⟩
  simpa [V.h_action_end_merge, h_endβ] using h_pref


theorem information_grounded_firm_preferences
    (V : InformationGroundedFirmDecision i t h L K K_min grid_step ΔP_out R1 R2 db_int db_u) :
    W.Preference i t h V.e_merge V.e_split ∧
    W.Preference i t h V.e_merge V.e_complete ∧
    W.Preference i t h V.e_merge V.e_retain := by
  have h_split_strict : ∃ h' ∈ W.MinPlausible i t,
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i V.α_split t h') := by
    obtain ⟨h', hh', hs⟩ := V.state_coverage (true, false)
    have hprofile : FirmSaleReceiptProfileGain
        (firmInformationOutcome .bothSignals (true, false))
        (firmInformationOutcome .demandHidden (true, false)) := by
      norm_num [FirmSaleReceiptProfileGain, firmInformationOutcome,
        informationPolicy, informationObservation, firmDemand, firmFactor]
    refine ⟨h', hh', ?_⟩
    have hmerge := congrFun (V.stock_merge h' hh') V.resourceA
    have hsplit := congrFun (V.stock_split h' hh') V.resourceA
    simp only [embedFirmBundle] at hmerge hsplit
    change 3 ≤ projectedStock W i V.α_merge t h' V.resourceA ∧
      projectedStock W i V.α_split t h' V.resourceA < 3
    constructor
    · rw [hmerge, hs]
      exact hprofile.1
    · rw [hsplit, hs]
      exact hprofile.2
  have h_complete_strict : ∃ h' ∈ W.MinPlausible i t,
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i V.α_complete t h') := by
    obtain ⟨h', hh', hs⟩ := V.state_coverage (false, true)
    have hprofile : FirmSaleReceiptProfileGain
        (firmInformationOutcome .bothSignals (false, true))
        (firmInformationOutcome .factorHidden (false, true)) := by
      norm_num [FirmSaleReceiptProfileGain, firmInformationOutcome,
        informationPolicy, informationObservation, firmDemand, firmFactor]
    refine ⟨h', hh', ?_⟩
    have hmerge := congrFun (V.stock_merge h' hh') V.resourceA
    have hcomplete := congrFun (V.stock_complete h' hh') V.resourceA
    simp only [embedFirmBundle] at hmerge hcomplete
    change 3 ≤ projectedStock W i V.α_merge t h' V.resourceA ∧
      projectedStock W i V.α_complete t h' V.resourceA < 3
    constructor
    · rw [hmerge, hs]
      exact hprofile.1
    · rw [hcomplete, hs]
      exact hprofile.2
  have h_retain_order : ∀ h' ∈ W.MinPlausible i t,
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i W.alpha_zero t h') := by
    intro h' hh'
    have hbase := both_signals_produce_requested_sale (V.stateOf h')
    have hmerge := congrFun (V.stock_merge h' hh') V.resourceA
    have hretain := congrFun (V.stock_retain h' hh') V.resourceA
    simp only [embedFirmBundle] at hmerge
    simp only [embedFirmBundle, firmRetainedOutcome] at hretain
    exact ⟨by rw [hmerge]; exact hbase.1,
      by rw [hretain]; norm_num [firmRetainedOutcome]⟩
  have h_split := information_firm_preference_from_stock_order V V.α_split V.e_split
    V.h_action_end_split V.h_feas_split
    (fun h' hh' => information_stock_order_over_split V h' hh') h_split_strict
  have h_complete := information_firm_preference_from_stock_order V V.α_complete V.e_complete
    V.h_action_end_complete V.h_feas_complete
    (fun h' hh' => information_stock_order_over_complete V h' hh')
    h_complete_strict
  have h_retain_strict : ∃ h' ∈ W.MinPlausible i t,
      FirmSaleReceiptGain V.resourceA
        (projectedStock W i V.α_merge t h')
        (projectedStock W i W.alpha_zero t h') := by
    obtain ⟨h', hh'⟩ := W.min_plausible_nonempty i t
    exact ⟨h', hh', h_retain_order h' hh'⟩
  have h_retain := information_firm_preference_from_stock_order V W.alpha_zero V.e_retain
    V.h_action_end_retain (W.alpha_zero_feasible i t h)
    (fun h' hh' => Or.inr (h_retain_order h' hh')) h_retain_strict
  exact ⟨h_split, h_complete, h_retain⟩

theorem purposeful_firm_coalescence_from_information
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : InformationGroundedFirmDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u) :
    (¬ PurposefulAct i t h dec.α_split) ∧
    (¬ PurposefulAct i t h dec.α_complete) ∧
    PurposefulAct i t h dec.α_merge ∧
    (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
     SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
     CoalescedQuantizationNoise dec.coalescenceGeometry.external grid_step <
       TotalQuantizationNoise L grid_step ∧
     0 < dec.coalescenceGeometry.external.remaining) := by
  have hpref := information_grounded_firm_preferences dec
  have h_win := viable_coalescence_critical_attenuation_window
    L K K_min grid_step ΔP_out R1 R2 db_int db_u
    dec.h_step dec.h_pos1 dec.h_pos2
    dec.h_crit_low dec.h_crit_high dec.h_K_min dec.h_K_ge dec.coalescenceGeometry
  have h_pref_split : Preference i t h dec.e_merge dec.e_split := hpref.1
  have h_pref_soc : Preference i t h dec.e_merge dec.e_complete := hpref.2.1
  have h_pref_retain : Preference i t h dec.e_merge dec.e_retain := hpref.2.2
  have h_no_split : ¬ PurposefulAct i t h dec.α_split := by
    intro h_purp
    have h_undom := h_purp.2.2.2 dec.α_merge dec.h_feas_merge
    have h_pref := h_pref_split
    rw [← dec.h_action_end_merge, ← dec.h_action_end_split] at h_pref
    exact h_undom h_pref
  have h_no_complete : ¬ PurposefulAct i t h dec.α_complete := by
    intro h_purp
    have h_undom := h_purp.2.2.2 dec.α_merge dec.h_feas_merge
    have h_pref := h_pref_soc
    rw [← dec.h_action_end_merge, ← dec.h_action_end_complete] at h_pref
    exact h_undom h_pref
  have h_purp_merge : PurposefulAct i t h dec.α_merge := by
    refine ⟨dec.h_feas_merge, dec.h_exec_merge, ?_, ?_⟩
    · rw [dec.h_action_end_merge, dec.h_action_end_retain]
      exact Or.inr h_pref_retain
    · intro β hβ h_pref_beta
      by_cases h_eq : β = dec.α_merge
      · subst h_eq
        exact pref_irrefl i t h (End_of i dec.α_merge t h) h_pref_beta
      · rcases dec.h_menu β hβ h_eq with h_is_split | h_is_soc | h_is_ret
        · rw [dec.h_action_end_merge, h_is_split] at h_pref_beta
          exact pref_asymm i t h h_pref_split h_pref_beta
        · rw [dec.h_action_end_merge, h_is_soc] at h_pref_beta
          exact pref_asymm i t h h_pref_soc h_pref_beta
        · rw [dec.h_action_end_merge, h_is_ret] at h_pref_beta
          exact pref_asymm i t h h_pref_retain h_pref_beta
  exact ⟨h_no_split, h_no_complete, h_purp_merge, h_win⟩

end InformationGroundedFirm


structure PrimitiveEndDominanceFirmAppraisal (i : Agent) (t : Moment) (h : History) where
  α_split : W.Action
  α_merge : W.Action
  α_soc : W.Action
  e_split : W.Ends
  e_merge : W.Ends
  e_soc : W.Ends
  e_retain : W.Ends
  h_action_end_split : W.End_of i α_split t h = e_split
  h_action_end_merge : W.End_of i α_merge t h = e_merge
  h_action_end_soc : W.End_of i α_soc t h = e_soc
  h_action_end_retain : W.End_of i W.alpha_zero t h = e_retain
  h_feas_split : α_split ∈ W.A_feas i t h
  h_feas_merge : α_merge ∈ W.A_feas i t h
  h_feas_soc : α_soc ∈ W.A_feas i t h
  h_at_node : W.mem_hist t h
  h_projected_feasibility : W.ProjectedFeasibility
  h_stock_grounding : W.OutcomesGroundedInEndowments
  merge_dominates_split : ∀ h' ∈ W.MinPlausible i t,
    W.SubjectiveTeleologicalDominates i t h
      (projectedStock W i α_merge t h') (projectedStock W i α_split t h')
  merge_dominates_soc : ∀ h' ∈ W.MinPlausible i t,
    W.SubjectiveTeleologicalDominates i t h
      (projectedStock W i α_merge t h') (projectedStock W i α_soc t h')
  merge_dominates_retain : ∀ h' ∈ W.MinPlausible i t,
    W.SubjectiveTeleologicalDominates i t h
      (projectedStock W i α_merge t h') (projectedStock W i α₀ t h')

/-- Valued-end dominance implies the three listed preference comparisons. -/
theorem firm_preference_deduced_from_primitive_end_dominance
    {i : Agent} {t : Moment} {h : History}
    (V : PrimitiveEndDominanceFirmAppraisal i t h) :
    W.Preference i t h V.e_merge V.e_split ∧
    W.Preference i t h V.e_merge V.e_soc ∧
    W.Preference i t h V.e_merge V.e_retain := by
  have h_app (α : W.Action) (hα : α ∈ W.A_feas i t h) :
      W.ProjectedAppraisable i t α := by
    intro h' hh'
    exact projected_feasibility V.h_projected_feasibility i t h h' α
      V.h_at_node hh' hα
  have h_ground (α : W.Action) : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.IsPhysicallyGroundedAt i α t'
        (W.ExpectedMaturation i α t' (W.sigma i t' α h')) (W.sigma i t' α h') := by
    intro h' _
    change W.OutcomeOf i α (W.tau i t h')
      (W.ExpectedMaturation i α (W.tau i t h') (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h') =
        W.BundleEnd (W.omega i
          (W.ExpectedMaturation i α (W.tau i t h') (W.sigma i (W.tau i t h') α h'))
          (W.sigma i (W.tau i t h') α h'))
    exact V.h_stock_grounding i α (W.tau i t h')
      (W.ExpectedMaturation i α (W.tau i t h') (W.sigma i (W.tau i t h') α h'))
      (W.sigma i (W.tau i t h') α h')
  have h_split := W.teleological_dominance_induces_preference
    i V.α_merge V.α_split t h ⟨h_app V.α_merge V.h_feas_merge,
      h_app V.α_split V.h_feas_split⟩ (h_ground V.α_merge) (h_ground V.α_split)
      V.merge_dominates_split
  have h_soc := W.teleological_dominance_induces_preference
    i V.α_merge V.α_soc t h ⟨h_app V.α_merge V.h_feas_merge,
      h_app V.α_soc V.h_feas_soc⟩ (h_ground V.α_merge) (h_ground V.α_soc)
      V.merge_dominates_soc
  have h_retain := W.teleological_dominance_induces_preference
    i V.α_merge W.alpha_zero t h ⟨h_app V.α_merge V.h_feas_merge,
      h_app W.alpha_zero (W.alpha_zero_feasible i t h)⟩ (h_ground V.α_merge)
      (h_ground W.alpha_zero) V.merge_dominates_retain
  rw [V.h_action_end_merge, V.h_action_end_split] at h_split
  rw [V.h_action_end_merge, V.h_action_end_soc] at h_soc
  rw [V.h_action_end_merge, V.h_action_end_retain] at h_retain
  exact ⟨h_split, h_soc, h_retain⟩


structure AppraisedEntrepreneurialFirmDecision (i : Agent) (t : Moment) (h : History)
    (L K K_min grid_step : ℕ) (ΔP_out R1 R2 db_int db_u : ℕ)
    extends PrimitiveEndDominanceFirmAppraisal i t h where
  h_step : 0 < grid_step
  h_pos1 : 1 ≤ R1
  h_pos2 : 1 ≤ R2
  h_crit_low : R1 * R2 * db_u < ΔP_out
  h_crit_high : ΔP_out ≤ R1 * db_int + R1 * R2 * db_u
  h_K_min : 2 ≤ K_min
  h_K_ge : K_min ≤ K
  coalescenceGeometry : FirmCoalescenceGeometry L K
  h_menu : ∀ β ∈ A_feas i t h, β ≠ α_merge →
    End_of i β t h = e_split ∨ End_of i β t h = e_soc ∨ End_of i β t h = e_retain

theorem purposeful_firm_coalescence_from_valued_ends
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : AppraisedEntrepreneurialFirmDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u) :
    (∃ h_merge, mem_hist t h_merge ∧ Exec i t dec.α_merge h_merge ∧
      ¬ PurposefulAct i t h_merge dec.α_split ∧
      ¬ PurposefulAct i t h_merge dec.α_soc ∧
      PurposefulAct i t h_merge dec.α_merge) ∧
    (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
     SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
     CoalescedQuantizationNoise dec.coalescenceGeometry.external grid_step <
       TotalQuantizationNoise L grid_step ∧
     0 < dec.coalescenceGeometry.external.remaining) := by
  have hpref := firm_preference_deduced_from_primitive_end_dominance
    dec.toPrimitiveEndDominanceFirmAppraisal
  have h_exec_merge := W.sigma_realization i t h h dec.h_at_node
    dec.h_feas_merge dec.h_at_node
  let h_merge := W.sigma i t dec.α_merge h
  have h_merge_incident : mem_hist t h_merge := h_exec_merge.1
  have h_exec_at_merge : Exec i t dec.α_merge h_merge :=
    ⟨h_merge_incident, h_exec_merge.2⟩
  have h_menus_equal : A_feas i t h = A_feas i t h_merge :=
    W.A_feas_bundle_invariant i t dec.h_at_node h_merge_incident
  have h_pref_eq := W.Preference_bundle_invariant i t dec.h_at_node h_merge_incident
  have h_pref_eq_split := congrFun (congrFun h_pref_eq dec.e_merge) dec.e_split
  have h_pref_eq_soc := congrFun (congrFun h_pref_eq dec.e_merge) dec.e_soc
  have h_pref_eq_retain := congrFun (congrFun h_pref_eq dec.e_merge) dec.e_retain
  have h_pref_merge_split : Preference i t h_merge dec.e_merge dec.e_split := by
    change W.Preference i t h_merge dec.e_merge dec.e_split
    exact Eq.mp h_pref_eq_split hpref.1
  have h_pref_merge_soc : Preference i t h_merge dec.e_merge dec.e_soc := by
    change W.Preference i t h_merge dec.e_merge dec.e_soc
    exact Eq.mp h_pref_eq_soc hpref.2.1
  have h_pref_merge_retain : Preference i t h_merge dec.e_merge dec.e_retain := by
    change W.Preference i t h_merge dec.e_merge dec.e_retain
    exact Eq.mp h_pref_eq_retain hpref.2.2
  have h_end_split_merge : W.End_of i dec.α_split t h_merge = dec.e_split := by
    calc
      W.End_of i dec.α_split t h_merge = W.End_of i dec.α_split t h :=
        (W.End_of_bundle_invariant i dec.α_split t dec.h_at_node h_merge_incident).symm
      _ = dec.e_split := dec.h_action_end_split
  have h_end_merge_merge : W.End_of i dec.α_merge t h_merge = dec.e_merge := by
    calc
      W.End_of i dec.α_merge t h_merge = W.End_of i dec.α_merge t h :=
        (W.End_of_bundle_invariant i dec.α_merge t dec.h_at_node h_merge_incident).symm
      _ = dec.e_merge := dec.h_action_end_merge
  have h_end_soc_merge : W.End_of i dec.α_soc t h_merge = dec.e_soc := by
    calc
      W.End_of i dec.α_soc t h_merge = W.End_of i dec.α_soc t h :=
        (W.End_of_bundle_invariant i dec.α_soc t dec.h_at_node h_merge_incident).symm
      _ = dec.e_soc := dec.h_action_end_soc
  have h_end_retain_merge : W.End_of i W.alpha_zero t h_merge = dec.e_retain := by
    calc
      W.End_of i W.alpha_zero t h_merge = W.End_of i W.alpha_zero t h :=
        (W.End_of_bundle_invariant i W.alpha_zero t dec.h_at_node h_merge_incident).symm
      _ = dec.e_retain := dec.h_action_end_retain
  have h_win := viable_coalescence_critical_attenuation_window
    L K K_min grid_step ΔP_out R1 R2 db_int db_u
    dec.h_step dec.h_pos1 dec.h_pos2
    dec.h_crit_low dec.h_crit_high dec.h_K_min dec.h_K_ge dec.coalescenceGeometry
  have h_no_split : ¬ PurposefulAct i t h_merge dec.α_split := by
    intro h_purp
    have h_undom := h_purp.2.2.2 dec.α_merge (h_menus_equal ▸ dec.h_feas_merge)
    have h_pref := h_pref_merge_split
    rw [← h_end_merge_merge, ← h_end_split_merge] at h_pref
    exact h_undom h_pref
  have h_no_soc : ¬ PurposefulAct i t h_merge dec.α_soc := by
    intro h_purp
    have h_undom := h_purp.2.2.2 dec.α_merge (h_menus_equal ▸ dec.h_feas_merge)
    have h_pref := h_pref_merge_soc
    rw [← h_end_merge_merge, ← h_end_soc_merge] at h_pref
    exact h_undom h_pref
  have h_purp_merge : PurposefulAct i t h_merge dec.α_merge := by
    refine ⟨h_menus_equal ▸ dec.h_feas_merge, h_exec_at_merge, ?_, ?_⟩
    · right
      have h_pref := h_pref_merge_retain
      rw [← h_end_merge_merge, ← h_end_retain_merge] at h_pref
      exact h_pref
    · intro β hβ h_pref_beta
      by_cases h_eq : β = dec.α_merge
      · subst h_eq
        exact pref_irrefl i t h_merge (End_of i dec.α_merge t h_merge) h_pref_beta
      · have hβ_at_h : β ∈ A_feas i t h := h_menus_equal.symm ▸ hβ
        rcases dec.h_menu β hβ_at_h h_eq with h_is_split | h_is_soc | h_is_ret
        · have h_end_beta : End_of i β t h_merge = dec.e_split := by
            calc End_of i β t h_merge = End_of i β t h :=
                   (W.End_of_bundle_invariant i β t dec.h_at_node h_merge_incident).symm
                 _ = dec.e_split := h_is_split
          have h_pref := h_pref_merge_split
          rw [← h_end_merge_merge, ← h_end_beta] at h_pref
          exact pref_asymm i t h_merge h_pref h_pref_beta
        · have h_end_beta : End_of i β t h_merge = dec.e_soc := by
            calc End_of i β t h_merge = End_of i β t h :=
                   (W.End_of_bundle_invariant i β t dec.h_at_node h_merge_incident).symm
                 _ = dec.e_soc := h_is_soc
          have h_pref := h_pref_merge_soc
          rw [← h_end_merge_merge, ← h_end_beta] at h_pref
          exact pref_asymm i t h_merge h_pref h_pref_beta
        · have h_end_beta : End_of i β t h_merge = dec.e_retain := by
            calc End_of i β t h_merge = End_of i β t h :=
                   (W.End_of_bundle_invariant i β t dec.h_at_node h_merge_incident).symm
                 _ = dec.e_retain := h_is_ret
          have h_pref := h_pref_merge_retain
          rw [← h_end_merge_merge, ← h_end_beta] at h_pref
          exact pref_asymm i t h_merge h_pref h_pref_beta
  exact ⟨⟨h_merge, h_merge_incident, h_exec_at_merge, h_no_split,
    h_no_soc, h_purp_merge⟩, h_win⟩

section OperationalFirmBoundary

variable [BilateralExchangeFrame W]

structure OperationalFirmBoundaryDecision (i : Agent) (t : Moment) (h : History)
    (L K K_min grid_step : ℕ) (ΔP_out R1 R2 db_int db_u : ℕ) where
  information : InformationGroundedFirmDecision i t h L K K_min grid_step
    ΔP_out R1 R2 db_int db_u
  vocabulary : DelegationVocabulary W
  bargaining : MarketBargainingMeaning W
  proposal : DelegationProposal vocabulary
  execution : DelegationExecution proposal
  compensation : DelegationCompensationEvidence proposal execution
  principal_instructs_task : @PurposefulAct W proposal.principal execution.instructionMoment
    proposal.history execution.instruction
  instruction_matches_observed_policy : execution.instruction =
    information.instructionAction
      (informationPolicy .bothSignals
        (information.observationRecord .bothSignals h))
  operator_accepts : @PurposefulAct W proposal.operator proposal.decisionMoment
    proposal.history proposal.acceptance
  operator_executes : @PurposefulAct W proposal.operator execution.workMoment
    proposal.history execution.task
  market : IndependentMarketInterface vocabulary bargaining
  selected_assignment : proposal.principal = i ∧ proposal.decisionMoment = t ∧
    proposal.history = h ∧ proposal.assignment = information.α_merge
  firm_seller : proposal.principal = market.sellerPrincipal
  same_history : proposal.history = market.history
  market_history_is_decision_history : market.history = h
  compensation_after_task : W.Precedence execution.workMoment compensation.transferMoment
  instruction_is_timely : W.Precedence proposal.decisionMoment execution.instructionMoment
  instruction_precedes_work : W.Precedence execution.instructionMoment execution.workMoment
  finishingAction : Action
  finishingMoment : Moment
  finishing_history : W.mem_hist finishingMoment h
  finishing_is_purposeful : @PurposefulAct W i finishingMoment h finishingAction
  compensation_before_finishing : W.Precedence compensation.transferMoment finishingMoment
  finishing_before_sale : W.Precedence finishingMoment market.moment
  finishing_is_nontrade_production : ¬ W.IsTradeAction finishingAction
  finishingInput : Means
  finishingCapacity : Means
  finishing_input_is_delivered_intermediate : finishingInput = compensation.deliveredGood
  finishing_inputs_distinct : finishingInput ≠ information.resourceB ∧
    finishingCapacity ≠ information.resourceB ∧ finishingInput ≠ finishingCapacity
  finishing_uses_input : 0 < W.use_means finishingAction finishingInput
  finishing_uses_capacity : 0 < W.use_means finishingAction finishingCapacity
  finishing_input_available : W.use_means finishingAction finishingInput ≤
    W.omega i finishingMoment h finishingInput
  finishing_capacity_available : W.use_means finishingAction finishingCapacity ≤
    W.omega i finishingMoment h finishingCapacity
  finishing_produces_sale_good : 0 < W.yield_means finishingAction information.resourceB
  finishing_output_covers_sale : market.qA ≤
    W.yield_means finishingAction information.resourceB
  internal_delivery_in_merge_trace :
    InventoryRun.containsMatchedAcceptAt
      (information.trace_merge h information.actual_history_plausible).run
      compensation.transferMoment proposal.operator compensation.deliveredQuantity
      compensation.deliveredGood compensation.compensationQuantity compensation.compensationGood
  instruction_in_merge_trace :
    InventoryRun.containsActionAt
      (information.trace_merge h information.actual_history_plausible).run
      execution.instructionMoment execution.instruction
  finishing_production_in_merge_trace :
    InventoryRun.containsProductionAt
      (information.trace_merge h information.actual_history_plausible).run
      finishingMoment finishingAction
  sale_actor_is_principal : market.seller = i
  sale_product_is_tracked_output : market.mA = information.resourceB
  sale_payment_is_tracked_cash : market.mB = information.resourceA
  sale_amount_matches_receipt_profile : market.qB =
    firmInformationOutcome .bothSignals (information.stateOf h) false
  sale_quantities_positive : 0 < market.qA ∧ 0 < market.qB
  sale_goods_available : market.qA ≤ W.omega i market.moment h market.mA
  customer_payment_available : market.qB ≤
    W.omega market.buyer market.moment h market.mB
  sale_occurs_in_merge_trace :
    InventoryRun.containsMatchedOfferAt
      (information.trace_merge h information.actual_history_plausible).run
      market.moment market.buyer market.qA market.mA market.qB market.mB

/-- The work moment precedes the sale moment. -/
theorem OperationalFirmBoundaryDecision.work_precedes_sale
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u) :
    W.Precedence dec.execution.workMoment dec.market.moment := by
  exact W.moment_lt_trans dec.compensation.work_precedes_transfer
    (W.moment_lt_trans dec.compensation_before_finishing dec.finishing_before_sale)


def OperationalFirmBoundaryDecision.organizationNetwork
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u)
    (hprincipal : @PurposefulAct W dec.proposal.principal dec.proposal.decisionMoment
      dec.proposal.history dec.proposal.assignment) :
    OrganizationNetwork dec.vocabulary dec.bargaining :=
  let D := AcceptedDelegation.ofEvidence dec.proposal dec.execution hprincipal
    dec.principal_instructs_task dec.operator_accepts dec.operator_executes
  threeStageFirmNetwork D dec.market dec.firm_seller
    dec.same_history dec.work_precedes_sale


theorem OperationalFirmBoundaryDecision.organizationNetwork_retains_evidence
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u)
    (hprincipal : @PurposefulAct W dec.proposal.principal dec.proposal.decisionMoment
      dec.proposal.history dec.proposal.assignment) :
    (∃ hd : (dec.organizationNetwork hprincipal).internallyDirected (0 : Fin 3) (1 : Fin 3),
      (dec.organizationNetwork hprincipal).accepted_direction hd =
        AcceptedDelegation.ofEvidence dec.proposal dec.execution hprincipal
          dec.principal_instructs_task dec.operator_accepts dec.operator_executes) ∧
    (∃ hm : (dec.organizationNetwork hprincipal).marketInterface (1 : Fin 3) (2 : Fin 3),
      (dec.organizationNetwork hprincipal).market_evidence hm = dec.market) ∧
    dec.proposal.history = dec.market.history ∧
    W.Precedence dec.execution.workMoment dec.market.moment := by
  let D := AcceptedDelegation.ofEvidence dec.proposal dec.execution hprincipal
    dec.principal_instructs_task dec.operator_accepts dec.operator_executes
  have hwork_sale := dec.work_precedes_sale
  have hedges := threeStageFirmNetwork_edges_retain_certificates D dec.market
    dec.firm_seller dec.same_history hwork_sale
  exact ⟨by simpa [OperationalFirmBoundaryDecision.organizationNetwork, D] using hedges.1,
    by simpa [OperationalFirmBoundaryDecision.organizationNetwork] using hedges.2,
    dec.same_history, hwork_sale⟩


def OperationalFirmBoundaryConclusion {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u) : Prop :=
    (¬ PurposefulAct i t h dec.information.α_split ∧
      ¬ PurposefulAct i t h dec.information.α_complete ∧
      PurposefulAct i t h dec.information.α_merge ∧
      (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
      SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
      CoalescedQuantizationNoise dec.information.coalescenceGeometry.external grid_step <
        TotalQuantizationNoise L grid_step ∧
      0 < dec.information.coalescenceGeometry.external.remaining)) ∧
    ∃ hprincipal : @PurposefulAct W dec.proposal.principal dec.proposal.decisionMoment
      dec.proposal.history dec.proposal.assignment,
      (dec.organizationNetwork hprincipal).HasFirmStructure ∧
      Nonempty (DelegatedInternalTransfer
        (AcceptedDelegation.ofEvidence dec.proposal dec.execution hprincipal
          dec.principal_instructs_task dec.operator_accepts dec.operator_executes))

theorem purposeful_operational_firm_boundary
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u) : OperationalFirmBoundaryConclusion dec := by
  rcases dec.selected_assignment with
    ⟨hprincipal_eq, hdecision_eq, hhistory_eq, hassignment_eq⟩
  have h_choice := purposeful_firm_coalescence_from_information dec.information
  have hmerge : PurposefulAct i t h dec.information.α_merge := h_choice.2.2.1
  have hprincipal_act : @PurposefulAct W dec.proposal.principal dec.proposal.decisionMoment
      dec.proposal.history dec.proposal.assignment := by
    rw [hprincipal_eq, hdecision_eq, hhistory_eq, hassignment_eq]
    exact hmerge
  let D := AcceptedDelegation.ofEvidence dec.proposal dec.execution hprincipal_act
    dec.principal_instructs_task dec.operator_accepts dec.operator_executes
  have h_firm_seller : D.principal = dec.market.sellerPrincipal := by
    change dec.proposal.principal = dec.market.sellerPrincipal
    exact dec.firm_seller
  have h_structure := threeStageFirmNetwork_has_firm_structure D dec.market
    h_firm_seller dec.same_history dec.work_precedes_sale
  let internalTransfer := DelegatedInternalTransfer.ofEvidence dec.proposal dec.execution
    hprincipal_act dec.principal_instructs_task dec.operator_accepts dec.operator_executes
    dec.compensation
  refine ⟨h_choice, ⟨hprincipal_act, ?_, ⟨internalTransfer⟩⟩⟩
  change (threeStageFirmNetwork D dec.market h_firm_seller
    dec.same_history dec.work_precedes_sale).HasFirmStructure
  exact h_structure


theorem purposeful_operational_firm_boundary_from_observed_prices
    {i : Agent} {t : Moment} {h : History}
    {L K K_min grid_step : ℕ} {ΔP_out R1 R2 db_int db_u : ℕ}
    (dec : OperationalFirmBoundaryDecision i t h L K K_min grid_step
      ΔP_out R1 R2 db_int db_u)
    (quotes : ObservedUnitPriceSpread dec.vocabulary dec.bargaining dec.proposal.principal
      dec.information.resourceB dec.information.resourceA t h)
    (_h_positive_baseline : 0 < quotes.lowerRecord.price)
    (h_spread : ΔP_out = quotes.spread) :
    OperationalFirmBoundaryConclusion dec ∧
    ΔP_out = quotes.spread ∧
    (∀ h' (_hh' : h' ∈ W.MinPlausible i t),
      firmPriceSignalObservation
        (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u)) (dec.information.stateOf h') =
          dec.information.observationRecord .demandHidden h' ∧
      firmPriceSignalObservation
        (SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u)) (dec.information.stateOf h') =
          dec.information.observationRecord .bothSignals h') := by
  refine ⟨purposeful_operational_firm_boundary dec, h_spread, ?_⟩
  intro h' hh'
  have hsignals := critical_attenuation_observation_equivalences ΔP_out R1 R2 db_int db_u
    dec.information.h_pos1 dec.information.h_pos2 dec.information.h_crit_low
    dec.information.h_crit_high (dec.information.stateOf h')
  rcases hsignals with ⟨hsplit, hmerge⟩
  constructor
  · calc
      firmPriceSignalObservation
        (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u)) (dec.information.stateOf h') =
          informationObservation .demandHidden (dec.information.stateOf h') := hsplit
      _ = dec.information.observationRecord .demandHidden h' :=
        (dec.information.observation_record_follows_channel .demandHidden h').symm
  · calc
      firmPriceSignalObservation
        (SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u)) (dec.information.stateOf h') =
          informationObservation .bothSignals (dec.information.stateOf h') := hmerge
      _ = dec.information.observationRecord .bothSignals h' :=
        (dec.information.observation_record_follows_channel .bothSignals h').symm

end OperationalFirmBoundary

theorem ordinal_firm_boundary_tradeoff
    (i : Agent) (t : Moment) (h : History)
    (α_firm α_market α_universal_firm : Action)
    (h_diff_mkt : α_firm ≠ α_market)
    (h_feas_firm : α_firm ∈ A_feas i t h)
    (h_feas_mkt : α_market ∈ A_feas i t h)
    (h_feas_univ : α_universal_firm ∈ A_feas i t h)
    (h_exec_firm : Exec i t α_firm h)
    (h_pref_firm_retain : Preference i t h (End_of i α_firm t h) (End_of i α₀ t h))
    (h_pref_firm_mkt : Preference i t h (End_of i α_firm t h) (End_of i α_market t h))
    (h_pref_firm_univ : Preference i t h (End_of i α_firm t h) (End_of i α_universal_firm t h))
    (h_menu : ∀ β ∈ A_feas i t h, β = α₀ ∨ β = α_firm ∨ β = α_market ∨ β = α_universal_firm) :
    PurposefulAct i t h α_firm ∧
    DemonstratedPref i t h α_firm α_market ∧
    ¬ PurposefulAct i t h α_market ∧
    ¬ PurposefulAct i t h α_universal_firm ∧
    ¬ PurposefulAct i t h α₀ := by
  have h_undom : ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) (End_of i α_firm t h) := by
    intro β hβ
    rcases h_menu β hβ with rfl | rfl | rfl | rfl
    · intro h_rev; exact pref_asymm i t h h_pref_firm_retain h_rev
    · intro h_self; exact pref_irrefl i t h _ h_self
    · intro h_rev; exact pref_asymm i t h h_pref_firm_mkt h_rev
    · intro h_rev; exact pref_asymm i t h h_pref_firm_univ h_rev
  have h_purp_firm : PurposefulAct i t h α_firm :=
    ⟨h_feas_firm, h_exec_firm, Or.inr h_pref_firm_retain, h_undom⟩
  have h_dem_pref : DemonstratedPref i t h α_firm α_market := by
    dsimp [DemonstratedPref]
    refine ⟨h_purp_firm, ?_⟩
    rw [Finset.mem_erase]
    exact ⟨h_diff_mkt.symm, h_feas_mkt⟩
  have h_no_mkt : ¬ PurposefulAct i t h α_market := by
    intro h_purp
    have h_undom_mkt := h_purp.2.2.2 α_firm h_feas_firm
    exact h_undom_mkt h_pref_firm_mkt
  have h_no_univ : ¬ PurposefulAct i t h α_universal_firm := by
    intro h_purp
    have h_undom_univ := h_purp.2.2.2 α_firm h_feas_firm
    exact h_undom_univ h_pref_firm_univ
  have h_no_retain : ¬ PurposefulAct i t h α₀ := by
    intro h_purp
    have h_undom_ret := h_purp.2.2.2 α_firm h_feas_firm
    exact h_undom_ret h_pref_firm_retain
  exact ⟨h_purp_firm, h_dem_pref, h_no_mkt, h_no_univ, h_no_retain⟩

end EntrepreneurialActionFrame


-- Section 4: Credit Expansion and Firm Scope


theorem credit_expansion_expands_hop_horizon
    (ΔP R_credit R_nat deadband : ℕ)
    (_h_pos_cred : 0 < R_credit)
    (h_crit_low : R_credit * deadband < ΔP)
    (h_crit_high : ΔP ≤ R_nat * deadband) :
    ReturnAtMost ΔP R_nat deadband 0 ∧
    ReturnAbove ΔP R_credit deadband 0 := by
  exact ⟨by simpa [ReturnAtMost] using h_crit_high,
    by simpa [ReturnAbove, Nat.zero_add] using h_crit_low⟩


theorem artificial_conglomeration_firm_boundary_distortion
    (ΔP_boom R_nat R_credit db_comp V_safe : ℕ)
    (upstream_blur joint_cost_blur ext_opp_loss W_nat grid_step Δz_abs : ℕ)
    (_h_pos_cred : 0 < R_credit)
    (h_pos_vol : 0 < Δz_abs)
    (h_cred_boom : R_credit * (V_safe + db_comp) < ΔP_boom)
    (h_nat_restraint : ΔP_boom ≤ R_nat * (V_safe + db_comp))
    (h_internal_blindness : W_nat + grid_step < upstream_blur + joint_cost_blur + ext_opp_loss) :
    ReturnAbove ΔP_boom R_credit db_comp V_safe ∧
    ReturnAtMost ΔP_boom R_nat db_comp V_safe ∧
    SpotMarketUncertainty W_nat grid_step Δz_abs <
      InternalFirmUncertainty upstream_blur joint_cost_blur ext_opp_loss Δz_abs := by
  refine ⟨?_, ?_, ?_⟩
  · exact h_cred_boom
  · exact h_nat_restraint
  · dsimp [SpotMarketUncertainty, InternalFirmUncertainty]
    exact Nat.mul_lt_mul_of_pos_right h_internal_blindness h_pos_vol


/-- A finite ActionFrame witness for the stated purposefulness alternatives,
paired with numeric coalescence-signal inequalities. The signal parameters
and this branching choice frame are separate inputs; this witness does not
derive the choice technology from the signal calculation. -/
theorem purposeful_firm_coalescence_separate_choice_and_signal_witness :
    ∃ (i : FiniteBranchingModel.Agent)
      (t : FiniteBranchingModel.Moment)
      (h : FiniteBranchingModel.History) (L K _K_min grid_step : ℕ)
      (ΔP_out R1 R2 db_int db_u : ℕ)
      (α_split α_merge α_socialize : FiniteBranchingModel.Action)
      (geom : FirmCoalescenceGeometry L K),
      (¬ @PurposefulAct FiniteBranchingModel i t h α_split) ∧
      (¬ @PurposefulAct FiniteBranchingModel i t h α_socialize) ∧
      (@PurposefulAct FiniteBranchingModel i t h α_merge) ∧
      (SignalSplit ΔP_out (SplitSignalThreshold R1 R2 db_int db_u) = false ∧
       SignalMerge ΔP_out (MergeSignalThreshold R1 R2 db_u) = true ∧
       CoalescedQuantizationNoise geom.external grid_step <
         TotalQuantizationNoise L grid_step ∧
       0 < geom.external.remaining) := by
  let : ActionFrame := FiniteBranchingModel
  let geom : FirmCoalescenceGeometry 4 2 := {
    external := ⟨2, by decide⟩
    internalizedPositive := by decide
    externalPositive := by decide
  }
  have h_not_split :
      ¬ @PurposefulAct FiniteBranchingModel (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        ModelAction.defer := by
    intro hp
    have h_feas : ModelAction.consume ∈ A_feas (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) := by decide
    have hpref : Preference (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        (End_of (0 : Fin 2) ModelAction.consume (0 : Fin 4) (1 : Fin 3))
        (End_of (0 : Fin 2) ModelAction.defer (0 : Fin 4) (1 : Fin 3)) := by
      change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 1) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
      decide
    exact hp.2.2.2 ModelAction.consume h_feas hpref
  have h_not_soc :
      ¬ @PurposefulAct FiniteBranchingModel (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        ModelAction.idle := by
    intro hp
    have h_feas : ModelAction.consume ∈ A_feas (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) := by decide
    have hpref : Preference (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        (End_of (0 : Fin 2) ModelAction.consume (0 : Fin 4) (1 : Fin 3))
        (End_of (0 : Fin 2) ModelAction.idle (0 : Fin 4) (1 : Fin 3)) := by
      change end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
      decide
    exact hp.2.2.2 ModelAction.consume h_feas hpref
  have h_merge :
      @PurposefulAct FiniteBranchingModel (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        ModelAction.consume := by
    have h_feas : ModelAction.consume ∈ A_feas (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) := by decide
    have h_exec : Exec (0 : Fin 2) (0 : Fin 4) ModelAction.consume (1 : Fin 3) := by
      change (branch_incidence 0 1 ∧
        (if (0 : Fin 3) = 0 then
          if (1 : Fin 3) = 0 then ModelAction.idle
          else if (1 : Fin 3) = 1 then ModelAction.consume
          else ModelAction.defer
        else ModelAction.idle) = ModelAction.consume)
      refine ⟨by decide, rfl⟩
    have h_pref_ret : Preference (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
        (End_of (0 : Fin 2) ModelAction.consume (0 : Fin 4) (1 : Fin 3))
        (End_of (0 : Fin 2) α₀ (0 : Fin 4) (1 : Fin 3)) := by
      change end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
      decide
    refine ⟨h_feas, h_exec, Or.inr h_pref_ret, ?_⟩
    intro β hβ hpref
    change β ∈
      ({ModelAction.idle, ModelAction.consume, ModelAction.defer} : Finset ModelAction) at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl
    · change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) at hpref
      revert hpref; decide
    · exact pref_irrefl (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) _ hpref
    · change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 1) at hpref
      revert hpref; decide
  refine ⟨(0 : Fin 2), (0 : Fin 4), (1 : Fin 3), 4, 2, 2, 10, 50, 2, 2, 10, 10,
    ModelAction.defer, ModelAction.consume, ModelAction.idle, geom,
    h_not_split, h_not_soc, h_merge, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide⟩


-- Section 8: Price Box Widening and Indeterminate Pairs


/-- An indeterminate pair is incomparable coordinatewise. -/
theorem indeterminacy_pair_is_antichain (d : ℕ) (B : OrdinalPriceBox d) (x y : InputVec d)
    (h : InIndeterminacyCone d B.low B.high x y) :
    ¬ (∀ r, x r ≤ y r) ∧ ¬ (∀ r, y r ≤ x r) := by
  constructor
  · intro h_le
    exact robust_dominance_excludes_indeterminacy d B.low B.high x y h_le h
  · intro h_ge
    rcases h with ⟨P1, _, _, _, hc1_lt, _⟩
    have h_le_each : ∀ r : Fin d, P1 r * y r ≤ P1 r * x r := by
      intro r
      exact Nat.mul_le_mul_left (P1 r) (h_ge r)
    have h_cost_le : Cost d P1 y ≤ Cost d P1 x := by
      dsimp [Cost]
      apply Finset.sum_le_sum
      intro r _
      exact h_le_each r
    omega

/-- The set of indeterminate plan pairs within a finite candidate menu `Menu`. -/
noncomputable def IndeterminacyPairSet (d : ℕ) (B : OrdinalPriceBox d)
    (Menu : Finset (InputVec d)) :
    Finset (InputVec d × InputVec d) := by
  classical
  exact (Menu ×ˢ Menu).filter
    (fun ⟨x, y⟩ => InIndeterminacyCone d B.low B.high x y)

/-- Number of ordered indeterminate pairs in `Menu`. -/
noncomputable def IndeterminacyAntichainWidth (d : ℕ) (B : OrdinalPriceBox d)
    (Menu : Finset (InputVec d)) : ℕ :=
  (IndeterminacyPairSet d B Menu).card

/-- Indeterminate pairs under `B1` remain indeterminate under `B2`. -/
theorem box_coarsening_pair_subset (d : ℕ) (B1 B2 : OrdinalPriceBox d)
    (h_coarsen : BoxCoarsening B1 B2) (Menu : Finset (InputVec d)) :
    IndeterminacyPairSet d B1 Menu ⊆ IndeterminacyPairSet d B2 Menu := by
  classical
  intro ⟨x, y⟩ h_mem
  rw [IndeterminacyPairSet, Finset.mem_filter] at h_mem ⊢
  exact ⟨h_mem.1,
    box_coarsening_widens_indeterminacy_cone B1 B2 h_coarsen x y h_mem.2⟩

/-- Widening the box weakly increases the number of indeterminate pairs. -/
theorem box_widening_antichain_card_le (d : ℕ) (B1 B2 : OrdinalPriceBox d)
    (h_coarsen : BoxCoarsening B1 B2) (Menu : Finset (InputVec d)) :
    IndeterminacyAntichainWidth d B1 Menu ≤ IndeterminacyAntichainWidth d B2 Menu := by
  dsimp [IndeterminacyAntichainWidth]
  exact Finset.card_le_card (box_coarsening_pair_subset d B1 B2 h_coarsen Menu)

/-- A newly indeterminate pair makes the count strictly larger. -/
theorem box_widening_expands_antichain_width (d : ℕ) (B1 B2 : OrdinalPriceBox d)
    (h_coarsen : BoxCoarsening B1 B2) (Menu : Finset (InputVec d))
    (x y : InputVec d) (hx : x ∈ Menu) (hy : y ∈ Menu)
    (h_not_in_B1 : ¬ InIndeterminacyCone d B1.low B1.high x y)
    (h_in_B2 : InIndeterminacyCone d B2.low B2.high x y) :
    IndeterminacyAntichainWidth d B1 Menu < IndeterminacyAntichainWidth d B2 Menu := by
  classical
  dsimp [IndeterminacyAntichainWidth]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨box_coarsening_pair_subset d B1 B2 h_coarsen Menu, ?_⟩
  intro h_eq
  have h_pair : (x, y) ∈ IndeterminacyPairSet d B2 Menu := by
    rw [IndeterminacyPairSet, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, h_in_B2⟩
  have h_in1 : (x, y) ∈ IndeterminacyPairSet d B1 Menu := by
    rw [h_eq]
    exact h_pair
  rw [IndeterminacyPairSet, Finset.mem_filter] at h_in1
  exact h_not_in_B1 h_in1.2

/-- An operator that widens each price box. -/
structure StageCoarseningMap (d : ℕ) where
  coarsen : OrdinalPriceBox d → OrdinalPriceBox d
  coarsening : ∀ B : OrdinalPriceBox d, BoxCoarsening B (coarsen B)

/-- Apply the widening operator `n` times. -/
def iterateCoarsening (d : ℕ) (m : StageCoarseningMap d) : ℕ → OrdinalPriceBox d → OrdinalPriceBox d
  | 0, B => B
  | n + 1, B => m.coarsen (iterateCoarsening d m n B)

/-- Each iterate contains the input price intervals. -/
theorem iterate_coarsening_widens (d : ℕ) (m : StageCoarseningMap d)
    (n : ℕ) (B : OrdinalPriceBox d) :
    BoxCoarsening B (iterateCoarsening d m n B) := by
  induction n with
  | zero =>
    constructor <;> intro r <;> rfl
  | succ n ih =>
    have h_step := m.coarsening (iterateCoarsening d m n B)
    constructor
    · intro r
      exact le_trans (h_step.1 r) (ih.1 r)
    · intro r
      exact le_trans (ih.2 r) (h_step.2 r)

/-- Iterated widening weakly increases the number of indeterminate pairs. -/
theorem stage_coarsening_expands_antichain_width (d : ℕ) (m : StageCoarseningMap d) (n : ℕ)
    (B : OrdinalPriceBox d) (Menu : Finset (InputVec d)) :
    IndeterminacyAntichainWidth d B Menu ≤
      IndeterminacyAntichainWidth d (iterateCoarsening d m n B) Menu :=
  box_widening_antichain_card_le d B (iterateCoarsening d m n B)
    (iterate_coarsening_widens d m n B) Menu


theorem order_theoretic_firm_boundary_tradeoff (d : ℕ)
    (B_internal B_market : OrdinalPriceBox d) (Menu : Finset (InputVec d)) :
    IndeterminacyAntichainWidth d B_internal Menu < IndeterminacyAntichainWidth d B_market Menu ↔
      (IndeterminacyPairSet d B_internal Menu).card < (IndeterminacyPairSet d B_market Menu).card :=
  Iff.rfl


theorem order_theoretic_firm_boundary_non_vacuous :
    ∃ (d : ℕ) (B_int B_mkt : OrdinalPriceBox d) (Menu : Finset (InputVec d)),
      BoxCoarsening B_int B_mkt ∧
      IndeterminacyAntichainWidth d B_int Menu < IndeterminacyAntichainWidth d B_mkt Menu := by
  classical
  let x : InputVec 2 := ![1, 3]
  let y : InputVec 2 := ![3, 1]
  let Menu : Finset (InputVec 2) := {x, y}
  let B_int : OrdinalPriceBox 2 := {
    low := ![5, 1]
    high := ![6, 2]
    le := by intro r; fin_cases r <;> decide
  }
  let B_mkt : OrdinalPriceBox 2 := {
    low := ![1, 1]
    high := ![6, 6]
    le := by intro r; fin_cases r <;> decide
  }
  have h_wide : BoxCoarsening B_int B_mkt := by
    constructor <;> intro r <;> fin_cases r <;> decide
  have hx : x ∈ Menu := Finset.mem_insert_self x {y}
  have hy : y ∈ Menu := Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have h_not_in_B1 : ¬ InIndeterminacyCone 2 B_int.low B_int.high x y := by
    intro ⟨_, P2, _, hP2, _, hc2⟩
    have hp2_0_low := (hP2 0).1
    have hp2_0_high := (hP2 0).2
    have hp2_1_low := (hP2 1).1
    have hp2_1_high := (hP2 1).2
    dsimp [B_int] at hp2_0_low hp2_0_high hp2_1_low hp2_1_high
    dsimp [Cost, x, y] at hc2
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at hc2
    dsimp at hc2
    omega
  have h_in_B2 : InIndeterminacyCone 2 B_mkt.low B_mkt.high x y := by
    refine ⟨![5, 1], ![1, 5], ?_, ?_, ?_, ?_⟩
    · intro r; fin_cases r <;> decide
    · intro r; fin_cases r <;> decide
    · dsimp [Cost, x, y]; rw [Fin.sum_univ_two, Fin.sum_univ_two]; decide
    · dsimp [Cost, x, y]; rw [Fin.sum_univ_two, Fin.sum_univ_two]; decide
  refine ⟨2, B_int, B_mkt, Menu, h_wide, ?_⟩
  exact box_widening_expands_antichain_width 2 B_int B_mkt h_wide Menu x y hx hy h_not_in_B1 h_in_B2


theorem firm_coalescence_shrinks_indeterminacy_width (d : ℕ)
    (C_firm C_mkt : StageCoarseningMap d) (B : OrdinalPriceBox d) (Menu : Finset (InputVec d))
    (h_coarsen : BoxCoarsening (C_firm.coarsen B) (C_mkt.coarsen B)) :
    IndeterminacyAntichainWidth d (C_firm.coarsen B) Menu ≤
    IndeterminacyAntichainWidth d (C_mkt.coarsen B) Menu :=
  box_widening_antichain_card_le d (C_firm.coarsen B) (C_mkt.coarsen B) h_coarsen Menu

/-- If the wider supplied box adds an indeterminate pair, the ordered-pair count rises strictly. -/
theorem firm_coalescence_strictly_shrinks_indeterminacy_width (d : ℕ)
    (C_firm C_mkt : StageCoarseningMap d) (B : OrdinalPriceBox d) (Menu : Finset (InputVec d))
    (h_coarsen : BoxCoarsening (C_firm.coarsen B) (C_mkt.coarsen B))
    (x y : InputVec d) (hx : x ∈ Menu) (hy : y ∈ Menu)
    (h_not_firm : ¬ InIndeterminacyCone d (C_firm.coarsen B).low (C_firm.coarsen B).high x y)
    (h_in_mkt : InIndeterminacyCone d (C_mkt.coarsen B).low (C_mkt.coarsen B).high x y) :
    IndeterminacyAntichainWidth d (C_firm.coarsen B) Menu <
    IndeterminacyAntichainWidth d (C_mkt.coarsen B) Menu :=
  box_widening_expands_antichain_width d (C_firm.coarsen B) (C_mkt.coarsen B)
    h_coarsen Menu x y hx hy h_not_firm h_in_mkt

end Praxeology

end

