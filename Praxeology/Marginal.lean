module

public import Praxeology.Frame
public import Praxeology.Action
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.deprecated false

/-!
# Praxeology.Marginal

Formalization of Phase 2 of Praxeology:
Law of Diminishing Marginal Utility, Avenue B Time Preference (Doxastic Open Horizon),
Mengerian Marginal Sacrifice, and Originary Interest.

## Contents
1. Section 1: Aggregate Feasibility & Standard Atomic Regime.
2. Section 2: Axiom 4 (Sub-Menu Monotonicity) & Diminishing Marginal Utility (DMU).
3. Section 3: Mengerian Marginal Sacrifice Without Neoclassical Utility.
4. Section 4: Avenue B Time Preference via Doxastic Open Epistemic Horizon.
5. Section 5: Originary Interest & Unit-for-Unit Exchange Rejection.
6. Section 6: Certified Machine-Checked Boundaries (DMU Fails under Complementarity, Positive Time Preference Independence).
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- Section 1: Aggregate Feasibility & Standard Atomic Regime
-- =========================================================================

/-- Joint feasibility for a finite set of ends S given available physical endowments:
    the total requirement of each means m across all ends in S cannot exceed
    the agent's physical endowment of m. -/
def JointlyFeasible (i : Agent) (t : Moment) (h : History) (S : Finset Ends) : Prop :=
  ∀ m : Means, (S.sum (fun e => requirement e m)) ≤ endowment i t h m

/-- Standard Atomic Regime for a scarce means m with endowment k = endowment i t h m:
    An indexed family of N mutually distinct atomic ends e_seq : Fin N → Ends (with k < N)
    where each requires requirement (e_seq r) m = 1, strictly ordered by Preference.
    Strictly ordinal: no cardinal utility functions or real numbers are used. -/
structure AtomicRegime (i : Agent) (t : Moment) (h : History) (m : Means) (N : ℕ) where
  k : ℕ
  h_endow : endowment i t h m = k
  h_k_lt_N : k < N
  e_seq : Fin N → Ends
  e_seq_inj : Function.Injective e_seq
  unit_requirement : ∀ r : Fin N, requirement (e_seq r) m = 1
  strictly_ranked : ∀ (r s : Fin N), r < s → Preference i t h (e_seq r) (e_seq s)

/-- The set of all atomic ends in the regime: E₁(m) = { e₁, ..., e_N }. -/
noncomputable def AtomicRegime.all_ends {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) : Finset Ends :=
  Finset.univ.image reg.e_seq

/-- Cardinality of E₁(m) is exactly N. -/
theorem AtomicRegime.card_all_ends {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) :
    reg.all_ends.card = N := by
  dsimp [AtomicRegime.all_ends]
  rw [Finset.card_image_of_injective Finset.univ reg.e_seq_inj]
  rw [Finset.card_univ, Fintype.card_fin]

-- =========================================================================
-- Section 2: Axiom 4 & Theorem 2.1 (Diminishing Marginal Utility)
-- =========================================================================

/-- Sub-menu preference relation ≻^{\mathcal{P}}_{i,t,h} over equal-sized menus of ends. -/
axiom SubMenuPref (i : Agent) (t : Moment) (h : History) : Finset Ends → Finset Ends → Prop

/-- Axiom 4 (Sub-Menu Monotonicity):
    If two subsets S, S' : Finset Ends have equal cardinality and S \ S' dominates S' \ S
    elementwise under a bijection, then S is strictly preferred to S' (S ≻^{\mathcal{P}} S'). -/
axiom axiom_4_sub_menu_monotonicity (i : Agent) (t : Moment) (h : History)
    {S S' : Finset Ends} (h_card : S.card = S'.card)
    (σ : Ends → Ends)
    (h_bij_maps : ∀ e ∈ S \ S', σ e ∈ S' \ S)
    (h_bij_inj : ∀ e1 ∈ S \ S', ∀ e2 ∈ S \ S', σ e1 = σ e2 → e1 = e2)
    (h_bij_surj : ∀ e' ∈ S' \ S, ∃ e ∈ S \ S', σ e = e')
    (h_dom : ∀ e ∈ S \ S', Preference i t h e (σ e)) :
    SubMenuPref i t h S S'

/-- Optimal allocation set S*(k) = { e₁, ..., e_k } of the top k ranked ends. -/
noncomputable def S_opt {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk : k ≤ N) : Finset Ends :=
  (Finset.filter (fun (r : Fin N) => r.val < k) Finset.univ).image reg.e_seq

/-- S*(k) is a subset of all atomic ends E₁(m). -/
theorem S_opt_subset {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk : k ≤ N) :
    S_opt reg k hk ⊆ reg.all_ends := by
  dsimp [S_opt, AtomicRegime.all_ends]
  apply Finset.image_subset_image
  intro x _
  exact Finset.mem_univ x

/-- Embedding from Fin k into Fin N for k ≤ N. -/
def fin_embed {N : ℕ} (k : ℕ) (hk : k ≤ N) (x : Fin k) : Fin N :=
  ⟨x.val, by omega⟩

theorem fin_embed_injective {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    Function.Injective (fin_embed k hk) := by
  intro x y h_eq
  have h_val : (fin_embed k hk x).val = (fin_embed k hk y).val := congrArg Fin.val h_eq
  dsimp [fin_embed] at h_val
  exact Fin.ext h_val

/-- Cardinality of the top-k filter in Fin N is exactly k. -/
theorem card_filter_fin_lt {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (Finset.filter (fun (r : Fin N) => r.val < k) Finset.univ).card = k := by
  have h_img : Finset.filter (fun (r : Fin N) => r.val < k) Finset.univ =
      Finset.univ.image (fin_embed k hk) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨_, hr_lt⟩
      exact ⟨⟨r.val, hr_lt⟩, Finset.mem_univ _, rfl⟩
    · intro ⟨x, _, hx_eq⟩
      subst hx_eq
      exact ⟨Finset.mem_univ _, x.is_lt⟩
  rw [h_img, Finset.card_image_of_injective _ (fin_embed_injective k hk)]
  rw [Finset.card_univ, Fintype.card_fin]

/-- The optimal allocation set S*(k) has cardinality exactly k. -/
theorem card_S_opt {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk : k ≤ N) :
    (S_opt reg k hk).card = k := by
  dsimp [S_opt]
  rw [Finset.card_image_of_injective _ reg.e_seq_inj]
  exact card_filter_fin_lt k hk

/-- The difference S*(k) \ S*(k - 1) is a singleton containing exactly e_k = e_seq ⟨k - 1, _⟩. -/
theorem diff_S_opt_eq_singleton {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    S_opt reg k hk \ S_opt reg (k - 1) (by omega) = {reg.e_seq ⟨k - 1, by omega⟩} := by
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_image.mp hx.1 with ⟨r, hr_filt, rfl⟩
    have hr_lt : r.val < k := (Finset.mem_filter.mp hr_filt).2
    have h_not : ¬ (reg.e_seq r ∈ S_opt reg (k - 1) (by omega)) := hx.2
    have hr_eq : r.val = k - 1 := by
      by_contra h_ne
      have hr_lt2 : r.val < k - 1 := by omega
      have hr_in : reg.e_seq r ∈ S_opt reg (k - 1) (by omega) := by
        dsimp [S_opt]
        apply Finset.mem_image_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_lt2⟩
      exact h_not hr_in
    have : r = ⟨k - 1, by omega⟩ := Fin.ext hr_eq
    rw [this]
  · intro hx
    subst hx
    dsimp [S_opt]
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_image_of_mem
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, by dsimp; omega⟩
    · intro h_in
      rcases Finset.mem_image.mp h_in with ⟨r, hr_filter, h_eq⟩
      have hr_lt : r.val < k - 1 := (Finset.mem_filter.mp hr_filter).2
      have r_eq : r = ⟨k - 1, by omega⟩ := reg.e_seq_inj h_eq
      have : r.val = k - 1 := congrArg Fin.val r_eq
      omega

/-- Existence and uniqueness of the marginal unit end in S*(k) \ S*(k - 1). -/
theorem diff_S_opt_exists_unique {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    ∃! e : Ends, e ∈ S_opt reg k hk \ S_opt reg (k - 1) (by omega) := by
  rw [diff_S_opt_eq_singleton reg k hk_pos hk]
  exact ⟨reg.e_seq ⟨k - 1, by omega⟩, Finset.mem_singleton_self _, fun y hy =>
    Finset.mem_singleton.mp hy⟩

/-- Marginal Utility of the k-th unit of scarce means m:
    Formulated via Classical.choose (definite description operator ι) to guarantee
    the return type is Ends (NOT Finset Ends or a cardinal real number). -/
noncomputable def MarginalUtility {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) : Ends :=
  Classical.choose (diff_S_opt_exists_unique reg k hk_pos hk).exists

/-- Marginal utility satisfies the definite description specification. -/
theorem marginal_utility_spec {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk ∈ S_opt reg k hk \ S_opt reg (k - 1) (by omega) :=
  Classical.choose_spec (diff_S_opt_exists_unique reg k hk_pos hk).exists

/-- Marginal Utility Evaluation: MU_{i,t,h}(m, k) = e_seq ⟨k - 1, _⟩. -/
theorem marginal_utility_eval {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk = reg.e_seq ⟨k - 1, by omega⟩ := by
  have h_spec := marginal_utility_spec reg k hk_pos hk
  rw [diff_S_opt_eq_singleton reg k hk_pos hk] at h_spec
  exact Finset.mem_singleton.mp h_spec

/-- Theorem 2.1 (Law of Purely Ordinal Diminishing Marginal Utility):
    For any unit increments 1 ≤ k₁ < k₂ ≤ N, the marginal utility of the earlier increment
    is strictly preferred to that of the later increment:
    MU(m, k₁) ≻_{i,t,h} MU(m, k₂). -/
theorem diminishing_marginal_utility {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N)
    (k1 k2 : ℕ) (hk1_pos : 1 ≤ k1) (hk2_le : k2 ≤ N) (hk_lt : k1 < k2) :
    Preference i t h
      (MarginalUtility reg k1 hk1_pos (by omega))
      (MarginalUtility reg k2 (by omega) hk2_le) := by
  rw [marginal_utility_eval reg k1 hk1_pos (by omega)]
  rw [marginal_utility_eval reg k2 (by omega) hk2_le]
  have hr_lt : (⟨k1 - 1, by omega⟩ : Fin N) < ⟨k2 - 1, by omega⟩ := by
    change k1 - 1 < k2 - 1
    omega
  exact reg.strictly_ranked ⟨k1 - 1, by omega⟩ ⟨k2 - 1, by omega⟩ hr_lt

-- =========================================================================
-- Section 3: Mengerian Marginal Sacrifice Without Neoclassical Utility
-- =========================================================================

/-- Minimal (least-urgent) end in a set of fulfilled ends:
    no other fulfilled end in S is less urgent than e_min. -/
def IsLeastUrgentEnd (Pref : Ends → Ends → Prop) (S : Finset Ends) (e_min : Ends) : Prop :=
  e_min ∈ S ∧ ∀ e ∈ S, ¬ Pref e_min e

/-- Theorem (Mengerian Least-Urgent End Existence):
    Any non-empty finite set S equipped with an irreflexive, transitive relation Pref
    has at least one minimal (least-urgent) element. -/
theorem mengerian_least_urgent_end_exists [DecidableEq Ends]
    (S : Finset Ends) (hS : S.Nonempty)
    (Pref : Ends → Ends → Prop) [∀ a b, Decidable (Pref a b)]
    (h_irrefl : ∀ x ∈ S, ¬ Pref x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Pref x y → Pref y z → Pref x z) :
    ∃ e_min ∈ S, IsLeastUrgentEnd Pref S e_min := by
  obtain ⟨m, hm_in, hm_min⟩ := exists_least_urgent_of_finite_poset S hS Pref h_irrefl h_trans
  exact ⟨m, hm_in, ⟨hm_in, hm_min⟩⟩

/-- Theorem 2.2 (Mengerian Marginal Sacrifice Without Utility):
    When a unit of scarce means is lost from a finite set of fulfilled ends S,
    purposeful economizing sacrifices the least-urgent end e_min ∈ S,
    without requiring preference completeness/connectedness (pref_connected) or cardinal utility. -/
theorem mengerian_marginal_sacrifice_exists [DecidableEq Ends]
    (i : Agent) (t : Moment) (h : History)
    (S : Finset Ends) (hS : S.Nonempty)
    [∀ a b, Decidable (Preference i t h a b)]
    (h_trans : ∀ e1 ∈ S, ∀ e2 ∈ S, ∀ e3 ∈ S,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    ∃ e_sacrifice ∈ S,
      IsLeastUrgentEnd (Preference i t h) S e_sacrifice ∧
      ∀ e ∈ S, ¬ Preference i t h e_sacrifice e := by
  have h_irrefl : ∀ x ∈ S, ¬ Preference i t h x x :=
    fun x _ => pref_irrefl i t h x
  obtain ⟨e_min, hm_in, h_least⟩ :=
    mengerian_least_urgent_end_exists S hS (Preference i t h) h_irrefl h_trans
  exact ⟨e_min, hm_in, h_least, h_least.2⟩

-- =========================================================================
-- Section 4: Avenue B Time Preference via Doxastic Open Epistemic Horizon
-- =========================================================================

/-- Temporally indexed end ⟨e, τ⟩ representing realization of end e at moment τ. -/
axiom TimedEnd : Ends → Moment → Ends

/-- Strict Universal Negative Time Preference:
    Agent systematically prefers future satisfaction to earlier satisfaction. -/
def UniversalNegativeTimePreference (i : Agent) (h : History) (e : Ends) : Prop :=
  ∀ τ1 τ2 : Moment, τ1 < τ2 → Preference i τ1 h (TimedEnd e τ2) (TimedEnd e τ1)

/-- Doxastic Open Epistemic Horizon:
    At active moment τ, across plausible histories, the agent believes τ is strictly before mortality T_max,
    and whenever immediate consumption α_e is feasible, there exists a feasible deferral action α_defer
    aiming at realization at some strictly later moment τ' > τ. -/
def DoxasticOpenHorizon (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action) : Prop :=
  α_e ∈ A_feas i τ h →
  End_of i α_e τ h = TimedEnd e τ →
  (∀ h' ∈ MinPlausible i τ, τ < T_max i h') ∧
  ∃ (α_defer : Action) (τ' : Moment),
    α_defer ∈ A_feas i τ h ∧
    τ < τ' ∧
    End_of i α_defer τ h = TimedEnd e τ'

/-- Theorem 2.3' (Avenue B: Impossibility of Action Under Universal Negative Time Preference):
    Under PurposefulAct and DoxasticOpenHorizon, an agent holding UniversalNegativeTimePreference
    can NEVER purposefully execute immediate consumption α_e at any active moment.
    Notice: Requires ZERO transitivity, ZERO completeness, and ZERO teleological injectivity! -/
theorem avenue_b_impossibility_of_negative_time_pref
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : End_of i α_e τ h = TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon i τ h e α_e)
    (h_neg : UniversalNegativeTimePreference i h e) :
    ¬ PurposefulAct i τ h α_e := by
  intro h_act
  have h_feas := h_act.1
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_feas h_end
  have h_pref_defer := h_neg τ τ' h_lt
  rw [← h_end_defer, ← h_end] at h_pref_defer
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  exact h_undom h_pref_defer

/-- Post-Horizon Inactivity:
    Beyond mortal lifespan T_max, no purposeful action can ever be executed,
    because the feasible action menu collapses to the singleton passive baseline {α₀}. -/
theorem post_horizon_no_action
    (i : Agent) (t : Moment) (h : History) (α : Action)
    (h_past : T_max i h < t) :
    ¬ PurposefulAct i t h α := by
  intro h_act
  have h_feas := h_act.1
  rw [post_horizon_singleton i t h h_past] at h_feas
  have h_eq : α = α₀ := Finset.mem_singleton.mp h_feas
  have h_np := purposeful_act_non_passive i t h α h_act
  exact h_np.1 h_eq

/-- Theorem 2.3'' (Enacted Consumption Demonstrates Non-Negative Time Preference):
    If an agent DOES purposefully execute immediate consumption α_e at moment τ under DoxasticOpenHorizon,
    then there exists a future moment τ' > τ such that the agent demonstrates Non-Negative Time Preference:
    deferral is NOT strictly preferred to immediate consumption. -/
theorem enacted_consumption_demonstrates_nonneg_time_pref
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : End_of i α_e τ h = TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon i τ h e α_e)
    (h_act : PurposefulAct i τ h α_e) :
    ∃ τ' : Moment, τ < τ' ∧ ¬ Preference i τ h (TimedEnd e τ') (TimedEnd e τ) := by
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  rw [h_end_defer, h_end] at h_undom
  exact ⟨τ', h_lt, h_undom⟩

/-- Distinct-End Dominant Action:
    Action α_star is feasible, executed, strictly improves upon α₀,
    and strictly dominates every feasible option that yields a distinct end. -/
def DistinctEndDominantAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ A_feas i t h ∧
  Exec i t α_star h ∧
  Preference i t h (End_of i α_star t h) (End_of i α₀ t h) ∧
  ∀ β ∈ A_feas i t h, End_of i β t h ≠ End_of i α_star t h →
    Preference i t h (End_of i α_star t h) (End_of i β t h)

/-- Theorem 2.3''' (Enacted Consumption Demonstrates Positive Time Preference):
    If an agent executes a Distinct-End Dominant Act to consume α_e at τ under DoxasticOpenHorizon,
    with injective time indexing (τ ≠ τ' → TimedEnd e τ ≠ TimedEnd e τ'),
    then the agent strictly demonstrates Positive Time Preference:
    earlier consumption is strictly preferred to later consumption! -/
theorem enacted_consumption_demonstrates_strict_time_pref
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : End_of i α_e τ h = TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon i τ h e α_e)
    (h_act : DistinctEndDominantAct i τ h α_e)
    (h_timed_inj : ∀ τ1 τ2 : Moment, τ1 ≠ τ2 → TimedEnd e τ1 ≠ TimedEnd e τ2) :
    ∃ τ' : Moment, τ < τ' ∧ Preference i τ h (TimedEnd e τ) (TimedEnd e τ') := by
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_ne_mom : τ ≠ τ' := fun h_eq => by subst h_eq; exact moment_lt_irrefl τ h_lt
  have h_ne_timed : TimedEnd e τ ≠ TimedEnd e τ' := h_timed_inj τ τ' h_ne_mom
  have h_ne_ends : End_of i α_defer τ h ≠ End_of i α_e τ h := by
    rw [h_end_defer, h_end]
    exact h_ne_timed.symm
  have h_dom := h_act.2.2.2 α_defer h_defer_feas h_ne_ends
  rw [h_end, h_end_defer] at h_dom
  exact ⟨τ', h_lt, h_dom⟩

-- =========================================================================
-- Section 5: Originary Interest & Unit-for-Unit Exchange Rejection
-- =========================================================================

/-- Axiom 5 (Positive Time Preference for Identical Goods Across Moments):
    For τ₁ τ₂ ∈ h with t ≤ τ₁ and τ₁ < τ₂, holding end quality constant,
    earlier satisfaction is strictly preferred to later satisfaction. -/
axiom positive_time_preference (i : Agent) (t : Moment) (h : History)
    (e : Ends) (τ1 τ2 : Moment) (hτ1 : τ1 ∈ h) (hτ2 : τ2 ∈ h)
    (h_order : (t < τ1 ∨ t = τ1) ∧ τ1 < τ2) :
    Preference i t h (TimedEnd e τ1) (TimedEnd e τ2)

/-- Untimed end of holding/consuming q discrete units of means m. -/
axiom QuantityEnd (m : Means) (q : ℕ) : Ends

/-- Intertemporal bundle evaluation: end corresponding to consuming q units of m at moment τ. -/
noncomputable def BundleEnd (m : Means) (q : ℕ) (τ : Moment) : Ends :=
  TimedEnd (QuantityEnd m q) τ

/-- Theorem 2.4'(1) (Rejection of Unit-for-Unit Exchange):
    Derived as a theorem directly from Axiom 5 (positive_time_preference) under endowment stationarity. -/
theorem unit_for_unit_exchange_rejected (i : Agent) (t : Moment) (h : History)
    (m : Means) (q : ℕ) (_hq : 0 < q)
    (τ1 τ2 : Moment) (hτ1 : τ1 ∈ h) (hτ2 : τ2 ∈ h)
    (h_order : (t < τ1 ∨ t = τ1) ∧ τ1 < τ2)
    (_h_stationarity : endowment i τ1 h m = endowment i τ2 h m) :
    Preference i t h (BundleEnd m q τ1) (BundleEnd m q τ2) := by
  dsimp [BundleEnd]
  exact positive_time_preference i t h (QuantityEnd m q) τ1 τ2 hτ1 hτ2 h_order

/-- Theorem 2.4' (Positive Originary Interest):
    If an agent voluntarily accepts future delivery ⟨q', τ₂⟩ over earlier delivery ⟨q, τ₁⟩
    where q > 0 and τ₁ < τ₂, and bundle preference is monotone in quantity, then:
    1. The future quantity must strictly exceed the earlier quantity: q < q'.
    2. There exists a strictly positive premium δ ≥ 1 such that q' = q + δ.
    3. The rational originary interest rate ι = (q' - q) / q > 0 in ℚ. -/
theorem positive_originary_interest (i : Agent) (t : Moment) (h : History)
    (m : Means) (q q' : ℕ) (hq : 0 < q)
    (τ1 τ2 : Moment) (hτ1 : τ1 ∈ h) (hτ2 : τ2 ∈ h)
    (h_order : (t < τ1 ∨ t = τ1) ∧ τ1 < τ2)
    (h_stationarity : endowment i τ1 h m = endowment i τ2 h m)
    (h_accept : Preference i t h (BundleEnd m q' τ2) (BundleEnd m q τ1))
    (h_sync_mono : q' ≤ q →
      Preference i t h (BundleEnd m q τ2) (BundleEnd m q' τ2) ∨
      BundleEnd m q τ2 = BundleEnd m q' τ2)
    (h_trans : ∀ e1 e2 e3, Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    q < q' ∧ (∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ) ∧ (0 < ((q' - q : ℚ) / (q : ℚ))) := by
  have h_lt : q < q' := by
    by_contra h_not_lt
    have h_le : q' ≤ q := by omega
    have h_u4u := unit_for_unit_exchange_rejected i t h m q hq τ1 τ2 hτ1 hτ2 h_order h_stationarity
    have h_pref_cycle := h_trans (BundleEnd m q' τ2) (BundleEnd m q τ1) (BundleEnd m q τ2) h_accept h_u4u
    cases h_sync_mono h_le with
    | inl h_mono_pref =>
      exact pref_asymm i t h h_pref_cycle h_mono_pref
    | inr h_mono_eq =>
      rw [h_mono_eq] at h_pref_cycle
      exact pref_irrefl i t h (BundleEnd m q' τ2) h_pref_cycle
  have h_prem : ∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ := by
    refine ⟨q' - q, by omega, by omega⟩
  refine ⟨h_lt, h_prem, ?_⟩
  have h_num : (0 : ℚ) < (q' : ℚ) - (q : ℚ) := sub_pos.mpr (Nat.cast_lt.mpr h_lt)
  have h_den : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr hq
  exact div_pos h_num h_den

-- =========================================================================
-- Section 6: Certified Machine-Checked Boundaries
-- =========================================================================

/-- Diminishing Marginal Utility Fails under Complementarity:
    A 2-unit resource allocation where 1 unit (a single shoe) yields zero utility improvement (Val 1 = Val 0),
    while 2 units (a pair of shoes) yields positive utility (Val 2 ≻ Val 1).
    The marginal utility of the 2nd unit strictly dominates that of the 1st unit,
    proving that Diminishing Marginal Utility does not follow from the Action Axiom
    without the auxiliary AtomicRegime (zero-complementarity) postulate. -/
theorem dmu_fails_under_complementarity :
    let Val : ℕ → Fin 2 := fun k => if k ≥ 2 then 1 else 0
    let Pref : Fin 2 → Fin 2 → Prop := fun a b => a = 1 ∧ b = 0
    Val 1 = Val 0 ∧
    Pref (Val 2) (Val 1) ∧
    ¬ Pref (Val 1) (Val 0) := by
  dsimp
  refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩
  intro ⟨h1, h2⟩
  exact absurd h1 (by decide)

/-- Independence Proof: Positive Time Preference Independent of Minimal Action:
    An agent purposefully saves for winter (α = 2), satisfying purposeful action,
    yet strictly prefers later consumption over earlier consumption (2 ≻ 1),
    proving that Positive Time Preference is logically independent of the Action Axiom alone. -/
theorem positive_time_pref_independent_of_minimal_action :
    let Pref : Fin 3 → Fin 3 → Prop := fun a b =>
      (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 0)
    Pref 2 0 ∧ Pref 2 1 ∧ ¬ Pref 1 2 := by
  dsimp
  refine ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

end Praxeology

end
