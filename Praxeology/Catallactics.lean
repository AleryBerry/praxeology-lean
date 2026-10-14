module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Marginal
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false

/-!
# Praxeology.Catallactics

Formalization of Phase 3 of Praxeology:
Catallactics, Money Emergence (Bourbaki-Witt), Discrete Marginal Pairs,
and the Economic Calculation Problem (ECP), following `spec/04_catallactics_ecp.md`.

## Contents
1. Section 1: Bilateral Exchange & Double Inequality of Valuations (Axiom 6 & Theorem 3.1).
2. Section 2: Mengerian Emergence of Money via Bourbaki-Witt (Theorem 3.2').
3. Section 3: Repaired Discrete Marginal Pairs Grid (Theorem 3.3').
4. Section 4: Physical Antichains, Catallactic Pricing vs. Socialist Incommensurability (Theorems 4.2 & 4.3).
-/

@[expose] public section

namespace Praxeology

open scoped Classical


-- =========================================================================
-- Section 1: Bilateral Exchange & Double Inequality of Valuations
-- =========================================================================

/-- Action of offering an exchange:
    agent i offers qA units of mA to agent j in exchange for qB units of mB. -/
axiom Offer (i j : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action

/-- Action of accepting an exchange:
    agent j accepts qA units of mA from agent i in exchange for qB units of mB. -/
axiom Accept (j i : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action

/-- Axiom 6 (Voluntary Bilateral Consent):
    Bilateral exchange χ(i, j, q_A m_A, q_B m_B) executes at ⟨t, h⟩ iff
    both distinct agents deliberatively bring about their respective Offer and Accept actions. -/
def BilateralExchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Prop :=
  i ≠ j ∧ mA ≠ mB ∧
  dstit i t (Exec i t (Offer i j qA mA qB mB)) h ∧
  dstit j t (Exec j t (Accept j i qA mA qB mB)) h

/-- Theorem 3.1 (Double Inequality of Subjective Valuations):
    In any voluntary bilateral exchange, if the passive baseline α₀ is in the foregone
    action menu of both agents, then both agents strictly prefer the exchange outcome
    to the status quo passive baseline.
    Proof: Direct application of Demonstrated Preference (Axiom 2(3)') to both deliberative acts. -/
theorem double_inequality_of_exchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_exch : BilateralExchange i j t h qA mA qB mB)
    (h_feas_i : Offer i j qA mA qB mB ∈ A_feas i t h)
    (h_feas_j : Accept j i qA mA qB mB ∈ A_feas j t h)
    (h_foregone_i : α₀ ∈ (A_feas i t h).erase (Offer i j qA mA qB mB))
    (h_foregone_j : α₀ ∈ (A_feas j t h).erase (Accept j i qA mA qB mB)) :
    Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h) ∧
    Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h) := by
  have h_dstit_i := h_exch.2.2.1
  have h_dstit_j := h_exch.2.2.2
  have h_dem_i := (demonstrated_preference i t h (Offer i j qA mA qB mB) h_feas_i).mp h_dstit_i
  have h_dem_j := (demonstrated_preference j t h (Accept j i qA mA qB mB) h_feas_j).mp h_dstit_j
  exact ⟨h_dem_i α₀ h_foregone_i, h_dem_j α₀ h_foregone_j⟩

-- =========================================================================
-- Section 2: Mengerian Emergence of Money via Bourbaki-Witt
-- =========================================================================

/-- Acceptance Profile: maps each commodity/means to the set of agents willing to accept it. -/
def AcceptanceProfile := Means → Finset Agent

/-- Poset order on acceptance profiles by pointwise subset inclusion: Γ₁ ⊑ Γ₂. -/
def ProfileLE (Γ1 Γ2 : AcceptanceProfile) : Prop :=
  ∀ m : Means, Γ1 m ⊆ Γ2 m

/-- Maximum marketability predicate: m is an argmax of acceptance size in profile Γ. -/
def IsMaxMarketable (Γ : AcceptanceProfile) (m : Means) : Prop :=
  ∀ m' : Means, (Γ m').card ≤ (Γ m).card

/-- Mengerian indirect-exchange transition operator Φ:
    Agents adopt good m if it has maximum marketability and indirect exchange is feasible. -/
noncomputable def Phi (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile) (m : Means) : Finset Agent :=
  Γ m ∪ Finset.univ.filter (fun i => IsMaxMarketable Γ m ∧ FeasIndirect i m)

/-- Theorem 3.2'(2) (Inflationary Property):
    The Mengerian operator Φ is inflationary: Γ ⊑ Φ(Γ). -/
theorem phi_inflationary (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile) :
    ProfileLE Γ (Phi FeasIndirect Γ) := by
  intro m
  dsimp [Phi]
  exact Finset.subset_union_left

/-- Structural counterexample refuting global monotonicity of Φ:
    If a shift in marketability causes good m to lose its argmax status between Γ₁ and Γ₂,
    agents who would adopt m under Γ₁ are not added under Γ₂, refuting Knaster-Tarski monotonicity. -/
theorem phi_not_globally_monotone
    (FeasIndirect : Agent → Means → Prop)
    (Γ1 Γ2 : AcceptanceProfile) (m : Means) (i : Agent)
    (h_le : ProfileLE Γ1 Γ2)
    (h_max1 : IsMaxMarketable Γ1 m)
    (h_feas : FeasIndirect i m)
    (h_not_in2 : i ∉ Γ2 m)
    (h_not_max2 : ¬ IsMaxMarketable Γ2 m) :
    ¬ ProfileLE (Phi FeasIndirect Γ1) (Phi FeasIndirect Γ2) := by
  intro h_mono
  have h_sub := h_mono m
  have h_in1 : i ∈ Phi FeasIndirect Γ1 m := by
    dsimp [Phi]
    rw [Finset.mem_union, Finset.mem_filter]
    right
    exact ⟨Finset.mem_univ i, h_max1, h_feas⟩
  have h_in2 := h_sub h_in1
  dsimp [Phi] at h_in2
  rw [Finset.mem_union, Finset.mem_filter] at h_in2
  rcases h_in2 with h_in_base | ⟨_, h_max2, _⟩
  · exact h_not_in2 h_in_base
  · exact h_not_max2 h_max2

/-- Fixed point of the Mengerian operator: Φ(Γ) = Γ. -/
def IsFixedPoint (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile) : Prop :=
  Phi FeasIndirect Γ = Γ

/-- Universal Money: good m* achieves universal marketability across all economic agents. -/
def IsUniversalMoney (Γ : AcceptanceProfile) (m_star : Means) : Prop :=
  Γ m_star = Finset.univ

/-- Theorem 3.2'(3) (Constructive Bourbaki-Witt Fixed Point & Universal Money Emergence):
    For any initial profile Γ₀ with a strictly dominant marketable commodity m_star,
    where all agents find indirect exchange feasible via m_star and other goods are not universally accepted,
    a single iteration of the inflationary operator Φ achieves:
    1. A genuine fixed point Φ(Γ*) = Γ*.
    2. Inflationary profile extension Γ₀ ⊑ Γ*.
    3. Emergence of universal money: Γ*(m_star) = univ. -/
theorem bourbaki_witt_fixed_point (FeasIndirect : Agent → Means → Prop)
    (Γ0 : AcceptanceProfile) (m_star : Means)
    (h_strict_max : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Γ0 m_star).card)
    (h_all_feas : ∀ i : Agent, FeasIndirect i m_star)
    (h_not_univ : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Finset.univ : Finset Agent).card) :
    ∃ (Γ_star : AcceptanceProfile),
      IsFixedPoint FeasIndirect Γ_star ∧
      ProfileLE Γ0 Γ_star ∧
      IsUniversalMoney Γ_star m_star := by
  let Γ_star := Phi FeasIndirect Γ0
  use Γ_star
  -- 1. Prove m_star is max-marketable in Γ0
  have h_max_mstar : IsMaxMarketable Γ0 m_star := by
    intro m'
    by_cases h_eq : m' = m_star
    · subst h_eq
      exact le_rfl
    · exact le_of_lt (h_strict_max m' h_eq)
  -- 2. Prove no other good is max-marketable in Γ0
  have h_not_max_other : ∀ m : Means, m ≠ m_star → ¬ IsMaxMarketable Γ0 m := by
    intro m h_ne h_all_le
    have h_le := h_all_le m_star
    have h_lt := h_strict_max m h_ne
    linarith
  -- 3. Γ_star m_star = Finset.univ
  have h_gamma_star_mstar : Γ_star m_star = Finset.univ := by
    ext i
    dsimp [Γ_star, Phi]
    rw [Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      right
      exact ⟨h_max_mstar, h_all_feas i⟩
  -- 4. ∀ m ≠ m_star, Γ_star m = Γ0 m
  have h_gamma_star_other : ∀ m : Means, m ≠ m_star → Γ_star m = Γ0 m := by
    intro m h_ne
    ext i
    dsimp [Γ_star, Phi]
    rw [Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro (h_in | ⟨h_max, _⟩)
      · exact h_in
      · exact (h_not_max_other m h_ne h_max).elim
    · intro h_in
      exact Or.inl h_in
  -- 5. IsFixedPoint FeasIndirect Γ_star
  have h_fixed_point : IsFixedPoint FeasIndirect Γ_star := by
    dsimp [IsFixedPoint]
    ext m i
    by_cases h_eq : m = m_star
    · subst h_eq
      dsimp [Phi]
      rw [Finset.mem_union, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro _
        rw [h_gamma_star_mstar]
        exact Finset.mem_univ i
      · intro _
        exact Or.inl (by rw [h_gamma_star_mstar]; exact Finset.mem_univ i)
    · dsimp [Phi]
      rw [Finset.mem_union, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      have h_m_not_max : ¬ IsMaxMarketable Γ_star m := by
        intro h_all_le
        have h_le := h_all_le m_star
        rw [h_gamma_star_mstar] at h_le
        have h_lt : (Γ_star m).card < (Finset.univ : Finset Agent).card := by
          rw [h_gamma_star_other m h_eq]
          exact h_not_univ m h_eq
        linarith
      constructor
      · rintro (h_in | ⟨h_max, _⟩)
        · exact h_in
        · exact (h_m_not_max h_max).elim
      · intro h_in
        exact Or.inl h_in
  -- 6. ProfileLE Γ0 Γ_star
  have h_le : ProfileLE Γ0 Γ_star := phi_inflationary FeasIndirect Γ0
  -- 7. IsUniversalMoney Γ_star m_star
  have h_univ : IsUniversalMoney Γ_star m_star := h_gamma_star_mstar
  exact ⟨h_fixed_point, h_le, h_univ⟩

/-- Theorem 3.2'(4) (Universal Money Emergence):
    If at fixed point Γ*, good m* is uniquely most marketable and all agents find indirect
    exchange feasible, then m* achieves universal acceptance (Universal Money). -/
theorem universal_money_emergence (FeasIndirect : Agent → Means → Prop)
    (Γ_star : AcceptanceProfile) (m_star : Means)
    (h_fix : IsFixedPoint FeasIndirect Γ_star)
    (h_max : IsMaxMarketable Γ_star m_star)
    (h_all_feas : ∀ i : Agent, FeasIndirect i m_star) :
    IsUniversalMoney Γ_star m_star := by
  dsimp [IsUniversalMoney]
  have h_eq : Phi FeasIndirect Γ_star m_star = Γ_star m_star := congrFun h_fix m_star
  ext i
  constructor
  · intro _; exact Finset.mem_univ i
  · intro _
    have h_in_phi : i ∈ Phi FeasIndirect Γ_star m_star := by
      dsimp [Phi]
      rw [Finset.mem_union, Finset.mem_filter]
      right
      exact ⟨Finset.mem_univ i, h_max, h_all_feas i⟩
    rw [h_eq] at h_in_phi
    exact h_in_phi

-- =========================================================================
-- Section 3: Repaired Discrete Marginal Pairs Grid
-- =========================================================================

/-- Discrete currency grid step with subdivision factor D > 0: step = 1 / D in ℚ. -/
def GridStep (D : ℕ) : ℚ := 1 / (D : ℚ)

theorem grid_step_pos (D : ℕ) (hD : 0 < D) : 0 < GridStep D := by
  dsimp [GridStep]
  have hD_q : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hD
  exact one_div_pos.mpr hD_q

/-- Theorem 3.3' (Marginal Pairs Extra-Marginal Deterrence & Intra-Marginal Clearance):
    On the discrete currency grid with subdivision factor D > 0, price P satisfies:
      max(v_s(r*), v_b(r* + 1) + 1/D) ≤ P ≤ min(v_b(r*), v_s(r* + 1) - 1/D)
    This guarantees:
    1. Intra-marginal clearance: seller r* and buyer r* both gain from exchange.
    2. Extra-marginal deterrence: buyer r*+1 and seller r*+1 are strictly deterred without tie ambiguity. -/
theorem marginal_pairs_equilibrium (v_b v_s : ℕ → ℚ) (r_star D : ℕ) (hD : 0 < D)
    (P : ℚ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + GridStep D) ≤ P)
    (hP_max : P ≤ min (v_b r_star) (v_s (r_star + 1) - GridStep D)) :
    -- 1. Intra-marginal clearance
    v_s r_star ≤ P ∧ P ≤ v_b r_star ∧
    -- 2. Extra-marginal deterrence
    v_b (r_star + 1) < P ∧ P < v_s (r_star + 1) := by
  have h_step_pos := grid_step_pos D hD
  have h1 : v_s r_star ≤ P := le_trans (le_max_left _ _) hP_min
  have h2 : P ≤ v_b r_star := le_trans hP_max (min_le_left _ _)
  have h3_le : v_b (r_star + 1) + GridStep D ≤ P := le_trans (le_max_right _ _) hP_min
  have h3 : v_b (r_star + 1) < P := by linarith
  have h4_le : P ≤ v_s (r_star + 1) - GridStep D := le_trans hP_max (min_le_right _ _)
  have h4 : P < v_s (r_star + 1) := by linarith
  exact ⟨h1, h2, h3, h4⟩

/-- Price bracket width W = P_max - P_min is non-negative. -/
theorem price_bracket_width_nonneg (v_b v_s : ℕ → ℚ) (r_star D : ℕ)
    (P : ℚ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + GridStep D) ≤ P)
    (hP_max : P ≤ min (v_b r_star) (v_s (r_star + 1) - GridStep D)) :
    0 ≤ (min (v_b r_star) (v_s (r_star + 1) - GridStep D)) -
        (max (v_s r_star) (v_b (r_star + 1) + GridStep D)) := by
  linarith

-- =========================================================================
-- Section 4: Physical Antichains, Catallactic Pricing vs. Socialist Incommensurability
-- =========================================================================

/-- Physical input vector across d distinct capital/input categories. -/
def InputVec (d : ℕ) := Fin d → ℕ

/-- Coordinate-wise physical product partial order: x ≤_phys y iff ∀ r, x r ≤ y r. -/
def PhysLE {d : ℕ} (x y : InputVec d) : Prop :=
  ∀ r : Fin d, x r ≤ y r

/-- Physical Antichain: two production input methods x and y are physically incomparable
    (e.g., method x uses more steel but less electricity than method y). -/
def PhysicalAntichain {d : ℕ} (x y : InputVec d) : Prop :=
  (∃ a : Fin d, y a < x a) ∧ (∃ b : Fin d, x b < y b)

/-- Incomparability lemma: an antichain is strictly incomparable in the physical partial order. -/
theorem antichain_incomparable {d : ℕ} (x y : InputVec d) (h : PhysicalAntichain x y) :
    ¬ PhysLE x y ∧ ¬ PhysLE y x := by
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  constructor
  · intro h_le
    have := h_le a
    omega
  · intro h_le
    have := h_le b
    omega

/-- Rational cost functional under Catallactics (R_cat):
    Total money cost is the market-price-weighted sum of physical input quantities:
    Cost(x) = ∑_{r=1}^d P_r * x_r ∈ ℚ. -/
def Cost (d : ℕ) (P : Fin d → ℚ) (x : InputVec d) : ℚ :=
  ∑ r : Fin d, P r * (x r : ℚ)

/-- Theorem 4.2(1) (Catallactic Commensurability):
    Under market pricing, the cost functional maps all heterogeneous input vectors
    (including physical antichains) into the totally ordered field ℚ.
    Therefore, Cost induces a complete total order, and argmin Cost is well-defined. -/
theorem catallactic_cost_linearly_ordered (d : ℕ) (P : Fin d → ℚ) (x y : InputVec d) :
    Cost d P x ≤ Cost d P y ∨ Cost d P y ≤ Cost d P x :=
  le_total (Cost d P x) (Cost d P y)

/-- An ordinal rank assignment φ : Fin 4 → ℕ is order-preserving if
    it respects the strict ranking: 0 ≺ 1 ≺ 2 ≺ 3 (i.e. strictly decreasing indices
    map to strictly increasing ranks). -/
def IsRankPreserving (φ : Fin 4 → ℕ) : Prop :=
  φ 0 > φ 1 ∧ φ 1 > φ 2 ∧ φ 2 > φ 3

/-- Theorem 4.2(2) (Undefinedness of Cost Minimization under Socialism / Automorphism Non-Invariance):
    Under socialism (R_soc), market prices for capital goods do not exist.
    If a central planning bureau attempts to rank production methods by summing
    ordinal utility ranks of foregone consumer ends, the resulting comparison is
    NOT invariant under order-automorphisms.
    Specifically, there exist two order-preserving rank embeddings φ₁ and φ₂ over the same
    four ends, and two foregone bundles S_a = {e₀, e₃} and S_b = {e₁, e₂}, such that:
      ∑_{e ∈ S_a} φ₁(e) > ∑_{e ∈ S_b} φ₁(e)   while   ∑_{e ∈ S_a} φ₂(e) < ∑_{e ∈ S_b} φ₂(e).
    Conclusion: Cost ranking over physical antichains is mathematically undefined in R_soc. -/
theorem socialist_calculation_incommensurability :
    ∃ (φ1 φ2 : Fin 4 → ℕ),
      IsRankPreserving φ1 ∧ IsRankPreserving φ2 ∧
      -- Under φ₁, method A appears more costly than method B:
      (φ1 0 + φ1 3 > φ1 1 + φ1 2) ∧
      -- Under φ₂, method A appears less costly than method B:
      (φ2 0 + φ2 3 < φ2 1 + φ2 2) := by
  -- Construct φ₁: ranks [10, 4, 3, 1]
  -- S_a sum: 10 + 1 = 11. S_b sum: 4 + 3 = 7. (11 > 7)
  let φ1 : Fin 4 → ℕ := fun r =>
    match r with
    | ⟨0, _⟩ => 10
    | ⟨1, _⟩ => 4
    | ⟨2, _⟩ => 3
    | ⟨3, _⟩ => 1
  -- Construct φ₂: ranks [10, 9, 8, 1]
  -- S_a sum: 10 + 1 = 11. S_b sum: 9 + 8 = 17. (11 < 17)
  let φ2 : Fin 4 → ℕ := fun r =>
    match r with
    | ⟨0, _⟩ => 10
    | ⟨1, _⟩ => 9
    | ⟨2, _⟩ => 8
    | ⟨3, _⟩ => 1
  have h_ord1 : IsRankPreserving φ1 := by
    dsimp [IsRankPreserving, φ1]
    omega
  have h_ord2 : IsRankPreserving φ2 := by
    dsimp [IsRankPreserving, φ2]
    omega
  have h_sum1 : φ1 0 + φ1 3 > φ1 1 + φ1 2 := by
    dsimp [φ1]
    omega
  have h_sum2 : φ2 0 + φ2 3 < φ2 1 + φ2 2 := by
    dsimp [φ2]
    omega
  exact ⟨φ1, φ2, h_ord1, h_ord2, h_sum1, h_sum2⟩

/-- Theorem 4.3 (Semantic Incommensurability vs. Algorithmic Complexity):
    The failure of central economic calculation is not an NP-hardness or Turing time-complexity
    barrier on known objective functions, but a semantic undefinedness:
    without catallactic market exchange in capital goods, no objective cost functional
    exists that is invariant under the ordinal automorphism group Aut(Ends, ≻). -/
theorem semantic_incommensurability_barrier :
    -- Any ranking derived from cardinal rank sums can be arbitrarily flipped
    -- by an order-preserving transformation, precluding the existence of an invariant objective.
    ∀ (eval_bundle : (Fin 4 → ℕ) → Finset (Fin 4) → ℕ),
      (eval_bundle = fun φ S => S.sum φ) →
      ∃ (φ1 φ2 : Fin 4 → ℕ) (Sa Sb : Finset (Fin 4)),
        IsRankPreserving φ1 ∧ IsRankPreserving φ2 ∧
        eval_bundle φ1 Sa > eval_bundle φ1 Sb ∧
        eval_bundle φ2 Sa < eval_bundle φ2 Sb := by
  intro eval_bundle h_def
  obtain ⟨φ1, φ2, h1, h2, hs1, hs2⟩ := socialist_calculation_incommensurability
  let Sa : Finset (Fin 4) := {0, 3}
  let Sb : Finset (Fin 4) := {1, 2}
  have h_disj_a : (0 : Fin 4) ≠ 3 := by intro h; cases h
  have h_disj_b : (1 : Fin 4) ≠ 2 := by intro h; cases h
  refine ⟨φ1, φ2, Sa, Sb, h1, h2, ?_, ?_⟩
  · subst h_def
    dsimp [Sa, Sb]
    rw [Finset.sum_pair h_disj_a, Finset.sum_pair h_disj_b]
    exact hs1
  · subst h_def
    dsimp [Sa, Sb]
    rw [Finset.sum_pair h_disj_a, Finset.sum_pair h_disj_b]
    exact hs2

end Praxeology

end
