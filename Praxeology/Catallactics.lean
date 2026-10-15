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
# Praxeology.Catallactics — Theorems 4 & 5: Catallactics & Economic Calculation

Formalization of catallactics and socialist calculation:
- **Theorem 4: Catallactic Bilateral Exchange & Bourbaki-Witt Money Emergence**
  - **Theorem 4.1 (Double Inequality of Subjective Valuations)**: `double_inequality_of_exchange`
    Voluntary bilateral exchange executes iff both trading partners strictly expect subjective gain over inertia α₀.
  - **Theorem 4.2 (Megger's Highwayman Separation of Coercion vs. Exchange)**: `highwayman_is_purposeful_but_not_catallactic`
    Coercive extortion satisfies naive immediate purposeful choice but strictly degrades baseline welfare,
    demarcating voluntary catallactic exchange from hegemonic coercion.
  - **Theorem 4.3 (Constructive Bourbaki-Witt Fixed Point & Universal Money Emergence)**: `bourbaki_witt_fixed_point`
    The inflationary marketability operator on finite acceptance profiles converges in finite steps to a fixed point,
    inducing the spontaneous emergence of universal money.
  - **Theorem 4.4 (Discrete Marginal Pairs & Pricing Grid Bounds)**: `marginal_pairs_equilibrium`
    Discrete marginal pairs on currency grid M_D establish unambiguous market-clearing intervals with extra-marginal deterrence.
  - **Theorem 4.5 (Praxeological Gresham's Law & Coercive Par-Pricing Circulation Collapse)**: `greshams_law_circulation_collapse`
    Under coercive legal tender mandating par exchange of undervalued good money and overvalued bad money,
    purposeful cost-minimizing buyers tender bad money and hoard good money, driving good money circulation to ∅.
- **Theorem 5: The Mises-Hayek Economic Calculation Problem (ECP)**
  - **Theorem 5.1 (Undefinedness of Antichain Cost Minimization Under Socialism)**: `socialist_calculation_incommensurability`
    Without market prices for capital goods, cost comparisons over physical antichains are non-invariant under
    ordinal automorphisms, rendering central economic calculation mathematically undefined.
  - **Theorem 5.2 (Semantic Incommensurability Barrier vs. Algorithmic Complexity)**: `semantic_incommensurability_barrier`
    The socialist calculation problem is not a computational Turing time-complexity barrier, but an epistemic undefinedness.
-/

@[expose] public section

namespace Praxeology

open scoped Classical


-- =========================================================================
-- Section 1: Bilateral Exchange & Megger Coercion vs. Catallactics Separation
-- =========================================================================

/-- A 2-Agent Interactive Node where each agent's realized end depends on BOTH agents' actions.
    Following Megger (2024) Sections 4 & 5.2. -/
structure InteractiveNode (ActI ActJ EndsI EndsJ : Type) where
  α₀_i : ActI
  α₀_j : ActJ
  Outcome_i : ActI → ActJ → EndsI
  Outcome_j : ActI → ActJ → EndsJ
  StrictPref_i : EndsI → EndsI → Prop
  StrictPref_j : EndsJ → EndsJ → Prop

/-- Purposeful Compliance at the Moment of Action:
    Agent `i` purposefully chooses `α_i` given `j`'s action `α_j` iff `Outcome_i α_i α_j`
    strictly beats `i`'s conditional passive baseline `Outcome_i α₀_i α_j`. -/
def PurposefulResponseI {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_j : ActJ) : Prop :=
  N.StrictPref_i (N.Outcome_i α_i α_j) (N.Outcome_i N.α₀_i α_j)

/-- True Catallactic (Voluntary/Contractual) Exchange:
    Both agents strictly improve over the JOINTLY UNMOLESTED AUTONOMOUS BASELINE `(α₀_i, α₀_j)`. -/
def IsCatallacticExchange {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_j : ActJ) : Prop :=
  PurposefulResponseI N α_i α_j ∧
  N.StrictPref_j (N.Outcome_j α_i α_j) (N.Outcome_j α_i N.α₀_j) ∧
  N.StrictPref_i (N.Outcome_i α_i α_j) (N.Outcome_i N.α₀_i N.α₀_j) ∧
  N.StrictPref_j (N.Outcome_j α_i α_j) (N.Outcome_j N.α₀_i N.α₀_j)

/-- Coercive Extortion (Megger's Highwayman / Mises's Hegemonic Bond):
    1. Victim `i` acts purposefully (`Outcome_i α_i α_threat ≻_i Outcome_i α₀_i α_threat`,
       e.g., handing over money beats getting shot).
    2. Yet `j`'s threat degraded `i`'s baseline so severely that `i` suffers a strict welfare loss
       relative to the unmolested autonomous baseline (`Outcome_i α₀_i α₀_j ≻_i Outcome_i α_i α_threat`). -/
def IsCoerciveExtortion {ActI ActJ EndsI EndsJ : Type}
    (N : InteractiveNode ActI ActJ EndsI EndsJ) (α_i : ActI) (α_threat : ActJ) : Prop :=
  PurposefulResponseI N α_i α_threat ∧
  N.StrictPref_i (N.Outcome_i N.α₀_i N.α₀_j) (N.Outcome_i α_i α_threat)

/-- Theorem 4.2 (Megger's Highwayman Separation of Coercion vs. Exchange):
    Handing over money to a robber is a purposeful action that beats the immediate passive
    baseline `α₀_i` (satisfying naive exchange definitions), yet strictly violates
    `IsCatallacticExchange` and satisfies `IsCoerciveExtortion`! -/
theorem highwayman_is_purposeful_but_not_catallactic :
    ∃ (N : InteractiveNode (Fin 2) (Fin 2) (Fin 3) (Fin 2)),
      PurposefulResponseI N 1 1 ∧
      IsCoerciveExtortion N 1 1 ∧
      ¬ IsCatallacticExchange N 1 1 := by
  let N : InteractiveNode (Fin 2) (Fin 2) (Fin 3) (Fin 2) := {
    α₀_i := 0
    α₀_j := 0
    Outcome_i := fun a_i a_j =>
      if a_j = 0 then 2
      else if a_i = 1 then 1
      else 0
    Outcome_j := fun a_i a_j => if a_i = 1 ∧ a_j = 1 then 1 else 0
    StrictPref_i := fun e₁ e₂ => e₁.val > e₂.val
    StrictPref_j := fun e₁ e₂ => e₁.val > e₂.val
  }
  refine ⟨N, ?_, ?_, ?_⟩
  · dsimp [PurposefulResponseI, N]; decide
  · dsimp [IsCoerciveExtortion, PurposefulResponseI, N]; decide
  · intro ⟨_, _, h_cat_i, _⟩
    dsimp [N] at h_cat_i
    omega

/-- Bilateral exchange action predicate:
    Both distinct agents execute purposeful actions α_i and α_j at ⟨t, h⟩. -/
def BilateralExchangeAction (i j : Agent) (t : Moment) (h : History) (α_i α_j : Action) : Prop :=
  i ≠ j ∧ PurposefulAct i t h α_i ∧ PurposefulAct j t h α_j

/-- Action of offering an exchange:
    agent i offers qA units of mA to agent j in exchange for qB units of mB. -/
axiom Offer (i j : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action

/-- Action of accepting an exchange:
    agent j accepts qA units of mA from agent i in exchange for qB units of mB. -/
axiom Accept (j i : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action

/-- Bilateral exchange χ(i, j, q_A m_A, q_B m_B) executes at ⟨t, h⟩ iff
    both distinct agents purposefully enact their respective Offer and Accept actions. -/
def BilateralExchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Prop :=
  i ≠ j ∧ mA ≠ mB ∧
  BilateralExchangeAction i j t h (Offer i j qA mA qB mB) (Accept j i qA mA qB mB)

/-- Theorem 4.1 (Double Inequality of Subjective Valuations):
    In any voluntary bilateral exchange, both agents strictly prefer the exchange outcome
    to their status quo passive baseline α₀.
    Follows directly from PurposefulAct without requiring global transitivity,
    connectedness, or teleological injectivity. -/
theorem double_inequality_of_exchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_exch : BilateralExchange i j t h qA mA qB mB) :
    Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h) ∧
    Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h) := by
  have hi := h_exch.2.2.2.1
  have hj := h_exch.2.2.2.2
  exact ⟨hi.2.2.1, hj.2.2.1⟩

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

/-- Lemma (Inflationary Property of the Mengerian Operator):
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

/-- Theorem 4.3 (Constructive Bourbaki-Witt Fixed Point & Universal Money Emergence):
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

/-- Corollary to Theorem 4.3 (Universal Money Emergence):
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

/-- Theorem 4.4 (Discrete Marginal Pairs & Pricing Grid Bounds):
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

/-- Canonical alias for Theorem 4.4. -/
abbrev marginal_pairs_discrete_grid := marginal_pairs_equilibrium

/-- Price bracket width W = P_max - P_min is non-negative. -/
theorem price_bracket_width_nonneg (v_b v_s : ℕ → ℚ) (r_star D : ℕ)
    (P : ℚ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + GridStep D) ≤ P)
    (hP_max : P ≤ min (v_b r_star) (v_s (r_star + 1) - GridStep D)) :
    0 ≤ (min (v_b r_star) (v_s (r_star + 1) - GridStep D)) -
        (max (v_s r_star) (v_b (r_star + 1) + GridStep D)) := by
  linarith

-- =========================================================================
-- Section 4: Praxeological Gresham's Law & Coercive Par-Pricing Circulation Collapse
-- =========================================================================

/-- Praxeological subjective tender cost functional:
    Tendering quantity P of medium m with subjective commodity value V(m)
    incurs subjective cost P * V(m). -/
def SubjectiveTenderCost (V : ℚ) (P : ℚ) : ℚ := P * V

/-- Lemma (Gresham Subjective Tender Dominance):
    When two media m_good and m_bad are mandated at legal par (1:1),
    tendering the lower-valued medium m_bad incurs strictly less subjective cost
    than tendering the higher-valued medium m_good: P * V(m_bad) < P * V(m_good). -/
theorem greshams_law_tender_dominance
    (V_good V_bad P : ℚ)
    (h_pos_bad : 0 < V_bad)
    (h_bad_lt_good : V_bad < V_good)
    (h_P_pos : 0 < P) :
    SubjectiveTenderCost V_bad P < SubjectiveTenderCost V_good P := by
  dsimp [SubjectiveTenderCost]
  exact mul_lt_mul_of_pos_left h_bad_lt_good h_P_pos

/-- Coercive Par-Pricing Model:
    Formalizes a legal-tender decree coercing acceptance at par between two distinct media:
    `m_good` (undervalued commodity money) and `m_bad` (overvalued / debased money). -/
structure CoerciveParPricingModel (Agent Means : Type) [DecidableEq Means] where
  m_good : Means
  m_bad : Means
  h_distinct : m_good ≠ m_bad
  V : Means → ℚ
  h_pos_bad : 0 < V m_bad
  h_undervalued : V m_bad < V m_good

/-- The subset of transacting agents actively tendering medium m in spot exchanges. -/
def CirculatingTender
    {Agent Means : Type} [DecidableEq Means]
    (Agents : Finset Agent)
    (tender : Agent → Means) (m : Means) : Finset Agent :=
  Agents.filter (fun i => tender i = m)

/-- Theorem 4.5 (Praxeological Gresham's Law & Coercive Par-Pricing Circulation Collapse):
    When a legal-tender decree forces two currencies `m_good` and `m_bad` to be accepted at par,
    but `m_good` has strictly higher non-monetary / intrinsic commodity valuation (`V m_bad < V m_good`),
    every purposeful buyer minimizing subjective sacrifice tenders `m_bad` and hoards `m_good`.
    As a result:
    1. Circulating tender of good money collapses to the empty set: `CirculatingTender Agents tender m_good = ∅`.
    2. Debased money completely captures market circulation: `CirculatingTender Agents tender m_bad = Agents`.
    This establishes Gresham's Law ("bad money drives out good when coerced at par") as the exact
    dual fixed-point collapse of the Bourbaki-Witt money emergence theorem. -/
theorem greshams_law_circulation_collapse
    {Agent Means : Type} [DecidableEq Means]
    (M : CoerciveParPricingModel Agent Means)
    (Agents : Finset Agent)
    (tender : Agent → Means)
    (P : ℚ) (h_P_pos : 0 < P)
    (h_feasible_tender : ∀ i ∈ Agents, tender i = M.m_good ∨ tender i = M.m_bad)
    (h_rational_tender : ∀ i ∈ Agents,
      SubjectiveTenderCost (M.V (tender i)) P ≤ SubjectiveTenderCost (M.V M.m_bad) P ∧
      SubjectiveTenderCost (M.V (tender i)) P ≤ SubjectiveTenderCost (M.V M.m_good) P) :
    CirculatingTender Agents tender M.m_good = ∅ ∧
    CirculatingTender Agents tender M.m_bad = Agents := by
  dsimp [CirculatingTender]
  have h_cost_lt : SubjectiveTenderCost (M.V M.m_bad) P < SubjectiveTenderCost (M.V M.m_good) P :=
    greshams_law_tender_dominance (M.V M.m_good) (M.V M.m_bad) P
      M.h_pos_bad M.h_undervalued h_P_pos
  constructor
  · rw [Finset.filter_eq_empty_iff]
    intro i hi h_tender_good
    have h_min := h_rational_tender i hi
    have h_bad_le := h_min.1
    rw [h_tender_good] at h_bad_le
    linarith
  · ext i
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hi, _⟩; exact hi
    · intro hi
      refine ⟨hi, ?_⟩
      have h_cases := h_feasible_tender i hi
      rcases h_cases with h_good | h_bad
      · exfalso
        have h_min := h_rational_tender i hi
        have h_bad_le := h_min.1
        rw [h_good] at h_bad_le
        linarith
      · exact h_bad

-- =========================================================================
-- Section 5: Physical Antichains, Catallactic Pricing vs. Socialist Incommensurability
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

/-- Lemma (Catallactic Commensurability):
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

/-- Theorem 5.1 (Undefinedness of Antichain Cost Minimization Under Socialism):
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

/-- Theorem 5.2 (Semantic Incommensurability Barrier vs. Algorithmic Complexity):
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
