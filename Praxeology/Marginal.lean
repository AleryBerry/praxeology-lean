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

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Praxeology.Marginal

Formalization of Phase 2 of Praxeology:
Law of Marginal Utility, Time Preference, and Originary Interest,
following `spec/03_intertemporal_marginal.md`.

## Contents
1. Section 1: Aggregate Feasibility & Standard Atomic Regime.
2. Section 2: Axiom 4 (Sub-Menu Monotonicity) & Theorem 2.1 (Purely Ordinal Diminishing Marginal Utility).
3. Section 3: Temporal Horizon, Axiom 5 (Positive Time Preference), & Theorem 2.3' (Action Impossibility under Negative Time Preference).
4. Section 4: Theorem 2.4' (Positive Originary Interest with Baseline Endowment Stationarity).
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
  intro e he
  rcases Finset.mem_image.mp he with ⟨r, _, rfl⟩
  exact Finset.mem_image_of_mem reg.e_seq (Finset.mem_univ r)

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

/-- For 1 ≤ k ≤ N, the difference S*(k) \ S*(k - 1) is a singleton containing e_seq ⟨k - 1, _⟩. -/
theorem diff_S_opt_eq_singleton {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    S_opt reg k hk \ S_opt reg (k - 1) (by omega) = { reg.e_seq ⟨k - 1, by omega⟩ } := by
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    dsimp [S_opt] at hx
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
    the return type is Ends (NOT Finset Ends or a cardinal real number).
    MU_{i,t,h}(m, k) := ι e ∈ E₁(m), (e ∈ S*(k) \ S*(k - 1)). -/
noncomputable def MarginalUtility {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) : Ends :=
  Classical.choose (diff_S_opt_exists_unique reg k hk_pos hk).exists

/-- Marginal utility satisfies the definite description specification. -/
theorem marginal_utility_spec {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk ∈ S_opt reg k hk \ S_opt reg (k - 1) (by omega) :=
  Classical.choose_spec (diff_S_opt_exists_unique reg k hk_pos hk).exists

/-- Theorem 2.1(2) (Marginal Utility Evaluation):
    MU_{i,t,h}(m, k) = e_seq ⟨k - 1, _⟩. -/
theorem marginal_utility_eval {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : AtomicRegime i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk = reg.e_seq ⟨k - 1, by omega⟩ := by
  have h_spec := marginal_utility_spec reg k hk_pos hk
  rw [diff_S_opt_eq_singleton reg k hk_pos hk] at h_spec
  exact Finset.mem_singleton.mp h_spec

/-- Theorem 2.1(3) (Law of Purely Ordinal Diminishing Marginal Utility):
    For any unit increments 1 ≤ k₁ < k₂ ≤ N, the marginal utility of the earlier increment
    is strictly preferred to that of the later increment:
    MU(m, k₁) ≻_{i,t,h} MU(m, k₂).
    Proof: Direct consequence of transitivity on the underlying ordering of E₁(m). -/
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
-- Section 3: Temporal Horizon, Axiom 5, & Theorem 2.3'
-- =========================================================================

/-- Biological/operational lifespan horizon of agent i on history h. -/
axiom T_max : Agent → History → Moment

/-- The lifespan boundary moment belongs to history h. -/
axiom T_max_mem (i : Agent) (h : History) : T_max i h ∈ h

/-- Definition 2.3'(1) (Post-Horizon Singleton Menu):
    Beyond lifespan T_max(i, h), the feasible action menu collapses to the singleton
    passive/inertial baseline {α₀}, maintaining non-emptiness without active agency. -/
axiom post_horizon_singleton (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) :
  T_max i h < t → A_feas i t h = {α₀}

/-- Temporally indexed end ⟨e, τ⟩ representing realization of end e at moment τ. -/
axiom TimedEnd : Ends → Moment → Ends

/-- Axiom 5 (Positive Time Preference):
    For τ₁ τ₂ ∈ h with t ≤ τ₁ and τ₁ < τ₂, holding end quality constant,
    earlier satisfaction is strictly preferred to later satisfaction:
    Preference i t h (TimedEnd e τ₁) (TimedEnd e τ₂). -/
axiom positive_time_preference (i : Agent) (t : Moment) (h : History)
    (e : Ends) (τ1 τ2 : Moment) (hτ1 : τ1 ∈ h) (hτ2 : τ2 ∈ h)
    (h_order : (t < τ1 ∨ t = τ1) ∧ τ1 < τ2) :
    Preference i t h (TimedEnd e τ1) (TimedEnd e τ2)

/-- Universal Negative Time Preference hypothesis:
    Agent systematically prefers later satisfaction to earlier satisfaction. -/
def UniversalNegativeTimePreference (i : Agent) (h : History) (e : Ends) : Prop :=
  ∀ τ1 τ2 : Moment, τ1 ∈ h → τ2 ∈ h → τ1 < τ2 →
    Preference i τ1 h (TimedEnd e τ2) (TimedEnd e τ1)

/-- Open Epistemic Horizon condition for end e at active moments:
    At any moment τ ∈ h with τ ≤ T_max i h where action α_e aims to realize e at τ,
    there exists a feasible alternative deferral action α_defer ∈ A_feas \ {α_e}
    aiming at realization at a strictly later moment τ' ∈ h. -/
def OpenEpistemicHorizon (i : Agent) (h : History) (e : Ends) (α_e : Action) : Prop :=
  ∀ τ ∈ h, (τ < T_max i h ∨ τ = T_max i h) →
    α_e ∈ A_feas i τ h →
    End_of i α_e τ h = TimedEnd e τ →
    ∃ (α_defer : Action) (τ' : Moment),
      α_defer ∈ (A_feas i τ h).erase α_e ∧
      τ' ∈ h ∧ τ < τ' ∧
      End_of i α_defer τ h = TimedEnd e τ'

/-- Theorem 2.3' (Action Impossibility Under Non-Positive Time Preference):
    If an agent holds universal negative time preference under an Open Epistemic Horizon,
    deliberative execution of immediate consumption α_e is impossible across all active moments.
    Proof: At every node, deferral strictly dominates realization, preventing execution prior to death. -/
theorem action_impossibility_under_negative_time_pref (i : Agent) (h : History) (e : Ends) (α_e : Action)
    (h_neg : UniversalNegativeTimePreference i h e)
    (h_oeh : OpenEpistemicHorizon i h e α_e)
    (τ : Moment) (hτ : τ ∈ h) (h_active : τ < T_max i h ∨ τ = T_max i h)
    (h_feas : α_e ∈ A_feas i τ h)
    (h_end : End_of i α_e τ h = TimedEnd e τ) :
    ¬ dstit i τ (Exec i τ α_e) h := by
  intro h_dstit
  have h_dem := (demonstrated_preference i τ h α_e h_feas).mp h_dstit
  obtain ⟨α_defer, τ', h_defer_in, hτ', h_lt, h_end_defer⟩ := h_oeh τ hτ h_active h_feas h_end
  have h_pref_defer : Preference i τ h (End_of i α_e τ h) (End_of i α_defer τ h) :=
    h_dem α_defer h_defer_in
  rw [h_end, h_end_defer] at h_pref_defer
  have h_neg_pref : Preference i τ h (TimedEnd e τ') (TimedEnd e τ) :=
    h_neg τ τ' hτ hτ' h_lt
  exact pref_asymm i τ h h_pref_defer h_neg_pref

-- =========================================================================
-- Section 4: Theorem 2.4' (Positive Originary Interest with Stationarity)
-- =========================================================================

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
      BundleEnd m q τ2 = BundleEnd m q' τ2) :
    q < q' ∧ (∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ) ∧ (0 < ((q' - q : ℚ) / (q : ℚ))) := by
  have h_lt : q < q' := by
    by_contra h_not_lt
    have h_le : q' ≤ q := by omega
    have h_u4u := unit_for_unit_exchange_rejected i t h m q hq τ1 τ2 hτ1 hτ2 h_order h_stationarity
    have h_pref_cycle := pref_trans i t h h_accept h_u4u
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



end Praxeology

end
