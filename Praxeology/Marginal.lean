/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Production
public import Praxeology.ExactNat
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum



/-!
# Marginal Utility and Intertemporal Choice

Law of diminishing marginal utility, Mengerian marginal sacrifice, roundabout production,
and pure time preference grounded in purposeful action.
-/

@[expose] public section

namespace Praxeology

/-- An exact cross-multiplied test that a spread exceeds a benchmark after an
uncertainty or delay allowance. The rate is required to be positive by the
evidence record that interprets this predicate economically. -/
def ReturnAbove (spread rate allowance benchmark : ℕ) : Prop :=
  rate * (benchmark + allowance) < spread

/-- An exact cross-multiplied test that a spread is at or below a benchmark
after an uncertainty or delay allowance. -/
def ReturnAtMost (spread rate allowance benchmark : ℕ) : Prop :=
  spread ≤ rate * (benchmark + allowance)

theorem returnAbove_iff_not_returnAtMost
    (spread rate allowance benchmark : ℕ) :
    ReturnAbove spread rate allowance benchmark ↔
      ¬ ReturnAtMost spread rate allowance benchmark := by
  dsimp [ReturnAbove, ReturnAtMost]
  omega

theorem returnAtMost_iff_not_returnAbove
    (spread rate allowance benchmark : ℕ) :
    ReturnAtMost spread rate allowance benchmark ↔
      ¬ ReturnAbove spread rate allowance benchmark := by
  dsimp [ReturnAbove, ReturnAtMost]
  omega

namespace ReturnAbove

theorem spread_mono {s₁ s₂ rate allowance benchmark : ℕ}
    (hspread : s₁ ≤ s₂) (hreturn : ReturnAbove s₁ rate allowance benchmark) :
    ReturnAbove s₂ rate allowance benchmark :=
  lt_of_lt_of_le hreturn hspread

theorem threshold_antitone {spread rate₁ rate₂ allowance₁ allowance₂
    benchmark₁ benchmark₂ : ℕ}
    (hthreshold : rate₁ * (benchmark₁ + allowance₁) ≤
      rate₂ * (benchmark₂ + allowance₂))
    (hreturn : ReturnAbove spread rate₂ allowance₂ benchmark₂) :
    ReturnAbove spread rate₁ allowance₁ benchmark₁ :=
  lt_of_le_of_lt hthreshold hreturn

end ReturnAbove

namespace ReturnAtMost

theorem threshold_mono {spread rate₁ rate₂ allowance₁ allowance₂
    benchmark₁ benchmark₂ : ℕ}
    (hthreshold : rate₁ * (benchmark₁ + allowance₁) ≤
      rate₂ * (benchmark₂ + allowance₂))
    (hreturn : ReturnAtMost spread rate₁ allowance₁ benchmark₁) :
    ReturnAtMost spread rate₂ allowance₂ benchmark₂ :=
  le_trans hreturn hthreshold

theorem spread_antitone {s₁ s₂ rate allowance benchmark : ℕ}
    (hspread : s₁ ≤ s₂) (hreturn : ReturnAtMost s₂ rate allowance benchmark) :
    ReturnAtMost s₁ rate allowance benchmark :=
  le_trans hspread hreturn

end ReturnAtMost

/-- Regression: a non-divisible spread is compared exactly by cross
multiplication (`13` exceeds `4 × (2 + 1)`). -/
theorem return_above_nondivisible_regression : ReturnAbove 13 4 1 2 := by
  norm_num [ReturnAbove]

/-- Regression: equality at the cross-multiplied threshold belongs to the
at-most case (`21 = 7 × (2 + 1)`). -/
theorem return_at_most_exact_threshold_regression : ReturnAtMost 21 7 1 2 := by
  norm_num [ReturnAtMost]

/-- A projected spread of twenty lies inside the natural-rate deadband and
above the credit-rate threshold for rates seven and four. -/
theorem return_deadband_credit_flip_regression :
    ReturnAtMost 20 7 1 2 ∧ ReturnAbove 20 4 1 2 := by
  norm_num [ReturnAtMost, ReturnAbove]

/-- The strict return predicate excludes equality at its scaled threshold. -/
theorem return_above_rejects_exact_threshold : ¬ ReturnAbove 12 4 1 2 := by
  norm_num [ReturnAbove]

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

section DMU_TimePreference

variable [W : ActionFrame]


-- Section 1: Feasibility and Unit Requirements


def JointlyFeasible (i : Agent) (t : Moment) (h : History) (S : Finset Ends) : Prop :=
  ∀ m : Means, (S.sum (fun e => requirement e m)) ≤ endowment i t h m


structure UnitRequirementSchedule (i : Agent) (t : Moment) (h : History) (m : Means) (N : ℕ) where
  k : ℕ
  h_endow : endowment i t h m = k
  h_k_lt_N : k < N
  e_seq : Fin N → Ends
  e_seq_inj : Function.Injective e_seq
  unit_requirement : ∀ r : Fin N, requirement (e_seq r) m = 1
  strictly_ranked : ∀ (r s : Fin N), r < s → Preference i t h (e_seq r) (e_seq s)

/-- All ends in the unit-requirement schedule. -/
def UnitRequirementSchedule.all_ends {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) : Finset Ends :=
  Finset.univ.image reg.e_seq

/-- The schedule contains `N` ends. -/
theorem UnitRequirementSchedule.card_all_ends
    {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) :
    reg.all_ends.card = N := by
  dsimp [UnitRequirementSchedule.all_ends]
  rw [Finset.card_image_of_injective Finset.univ reg.e_seq_inj]
  rw [Finset.card_univ, Fintype.card_fin]


-- Section 2: Ranked Ends and Feasible Bundles


/-- The first `k` ranked ends. -/
def S_opt {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (_hk : k ≤ N) : Finset Ends :=
  (Finset.filter (fun (r : Fin N) => r.val < k) Finset.univ).image reg.e_seq

/-- The selected ends belong to the schedule. -/
theorem S_opt_subset {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N) :
    S_opt reg k hk ⊆ reg.all_ends := by
  dsimp [S_opt, UnitRequirementSchedule.all_ends]
  apply Finset.image_subset_image
  intro x _
  exact Finset.mem_univ x


/-- The selected set has `k` members. -/
theorem card_S_opt {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N) :
    (S_opt reg k hk).card = k := by
  dsimp [S_opt]
  rw [Finset.card_image_of_injective _ reg.e_seq_inj]
  exact card_filter_fin_lt k hk

/-- Each subset of the schedule requires one unit per end. -/
theorem atomic_bundle_requirement_eq_card {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (S : Finset Ends) (hS : S ⊆ reg.all_ends) :
    (S.sum (fun e => requirement e m)) = S.card := by
  have h_const : ∀ e ∈ S, requirement e m = 1 := by
    intro e he
    have he_all : e ∈ reg.all_ends := hS he
    dsimp [UnitRequirementSchedule.all_ends] at he_all
    rcases Finset.mem_image.mp he_all with ⟨r, _, rfl⟩
    exact reg.unit_requirement r
  have h_sum := Finset.sum_congr rfl h_const
  rw [h_sum, ← Finset.card_eq_sum_ones]

/-- The first `k` ends require `k` units of `m`. -/
theorem S_opt_requirement_eq_k {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N) :
    ((S_opt reg k hk).sum (fun e => requirement e m)) = k := by
  rw [atomic_bundle_requirement_eq_card reg (S_opt reg k hk) (S_opt_subset reg k hk)]
  exact card_S_opt reg k hk

/-- The first `k` ends fit within the endowment of `m`. -/
theorem S_opt_is_jointly_feasible_on_m {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N)
    (h_le_endow : k ≤ endowment i t h m) :
    ((S_opt reg k hk).sum (fun e => requirement e m)) ≤ endowment i t h m := by
  rw [S_opt_requirement_eq_k reg k hk]
  exact h_le_endow

/-- Any feasible subset has at most `reg.k` ends. -/
theorem jointly_feasible_card_le_k {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (S : Finset Ends) (hS : S ⊆ reg.all_ends)
    (h_feas : (S.sum (fun e => requirement e m)) ≤ endowment i t h m) :
    S.card ≤ reg.k := by
  rw [atomic_bundle_requirement_eq_card reg S hS] at h_feas
  rw [reg.h_endow] at h_feas
  exact h_feas


theorem S_opt_dominates_suboptimal_bundle {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N)
    (S : Finset Ends) (hS_sub : S ⊆ reg.all_ends)
    (hS_card : S.card ≤ k) (hS_ne : S ≠ S_opt reg k hk) :
    (S_opt reg k hk \ S).Nonempty ∧
    (∀ e_in ∈ S_opt reg k hk \ S, ∀ e_out ∈ S \ S_opt reg k hk, Preference i t h e_in e_out) := by
  have h_nonempty : (S_opt reg k hk \ S).Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_sub : S_opt reg k hk ⊆ S := by
      intro x hx
      by_contra hx_not_in
      have : x ∈ S_opt reg k hk \ S := Finset.mem_sdiff.mpr ⟨hx, hx_not_in⟩
      rw [h_empty] at this
      cases this
    have h_card_opt : (S_opt reg k hk).card = k := card_S_opt reg k hk
    have h_eq : S_opt reg k hk = S := Finset.eq_of_subset_of_card_le h_sub (by omega)
    exact hS_ne h_eq.symm
  refine ⟨h_nonempty, ?_⟩
  intro e_in he_in e_out he_out
  rw [Finset.mem_sdiff] at he_in he_out
  have he_in_opt := he_in.1
  have he_out_s := he_out.1
  dsimp [S_opt] at he_in_opt
  rcases Finset.mem_image.mp he_in_opt with ⟨r, hr_filt, rfl⟩
  have hr_lt : r.val < k := (Finset.mem_filter.mp hr_filt).2
  have he_out_all : e_out ∈ reg.all_ends := hS_sub he_out_s
  dsimp [UnitRequirementSchedule.all_ends] at he_out_all
  rcases Finset.mem_image.mp he_out_all with ⟨s, _, rfl⟩
  have hs_not_opt := he_out.2
  have hs_ge : k ≤ s.val := by
    by_contra h_contra
    have hs_lt : s.val < k := by omega
    have hs_in_opt : reg.e_seq s ∈ S_opt reg k hk := by
      dsimp [S_opt]
      apply Finset.mem_image_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs_lt⟩
    exact hs_not_opt hs_in_opt
  have h_r_lt_s : r < s := by
    apply Fin.mk_lt_mk.mpr
    omega
  exact reg.strictly_ranked r s h_r_lt_s


structure BundleAllocationMenu (i : Agent) (t : Moment) (h : History) {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N) where
  bundle_of : Action → Finset Ends
  bundle_all : ∀ α ∈ A_feas i t h, α ≠ α₀ →
    bundle_of α ⊆ reg.all_ends ∧ ((bundle_of α).sum (fun e => requirement e m)) ≤ k
  α_opt : Action
  h_opt_feas : α_opt ∈ A_feas i t h
  h_opt_bundle : bundle_of α_opt = S_opt reg k hk
  bundle_stock : Action → (Means → ℕ)
  h_end_eq_bundle : ∀ α, End_of i α t h = W.BundleEnd (bundle_stock α)
  h_opt_dominates : ∀ α ∈ A_feas i t h, bundle_of α ≠ S_opt reg k hk →
    W.SubjectiveTeleologicalDominates i t h (bundle_stock α_opt) (bundle_stock α)

theorem BundleAllocationMenu.mengerian_preference
    {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    {reg : UnitRequirementSchedule i t h m N} {k : ℕ} {hk : k ≤ N}
    (sys : BundleAllocationMenu i t h reg k hk)
    (α : Action) (h_feas : α ∈ A_feas i t h) (h_sub : sys.bundle_of α ≠ S_opt reg k hk) :
    Preference i t h (End_of i sys.α_opt t h) (End_of i α t h) := by
  rw [sys.h_end_eq_bundle sys.α_opt, sys.h_end_eq_bundle α]
  exact W.teleological_bundle_dominance_induces_preference i t h
    (sys.bundle_stock sys.α_opt) (sys.bundle_stock α) (sys.h_opt_dominates α h_feas h_sub)

/-- A bundle requiring at most `k` units has at most `k` ends. -/
theorem atomic_bundle_card_le_of_req_le {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (S : Finset Ends) (hS : S ⊆ reg.all_ends) (k : ℕ)
    (h_feas : (S.sum (fun e => requirement e m)) ≤ k) :
    S.card ≤ k := by
  rw [atomic_bundle_requirement_eq_card reg S hS] at h_feas
  exact h_feas


theorem purposeful_act_forces_S_opt {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk : k ≤ N)
    (sys : BundleAllocationMenu i t h reg k hk)
    (α_star : Action)
    (h_purp : PurposefulAct i t h α_star)
    (_h_active : α_star ≠ α₀) :
    sys.bundle_of α_star = S_opt reg k hk := by
  have h_feas := h_purp.1
  by_contra h_ne
  have h_pref := sys.mengerian_preference α_star h_feas h_ne
  have h_undom := h_purp.2.2.2 sys.α_opt sys.h_opt_feas
  exact h_undom h_pref


theorem purposeful_act_forces_S_opt_from_physical_endowment
    {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (hk : reg.k ≤ N)
    (sys : BundleAllocationMenu i t h reg reg.k hk)
    (α_star : Action)
    (h_purp : PurposefulAct i t h α_star)
    (_h_active : α_star ≠ α₀) :
    sys.bundle_of α_star = S_opt reg reg.k hk := by
  have h_feas := h_purp.1
  by_contra h_ne
  have h_pref := sys.mengerian_preference α_star h_feas h_ne
  have h_undom := h_purp.2.2.2 sys.α_opt sys.h_opt_feas
  exact h_undom h_pref

/-- The difference set contains only the end at index `k - 1`. -/
theorem diff_S_opt_eq_singleton {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
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

/-- There is a unique end in the difference set. -/
theorem diff_S_opt_exists_unique {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    ∃! e : Ends, e ∈ S_opt reg k hk \ S_opt reg (k - 1) (by omega) := by
  rw [diff_S_opt_eq_singleton reg k hk_pos hk]
  exact ⟨reg.e_seq ⟨k - 1, by omega⟩, Finset.mem_singleton_self _, fun y hy =>
    Finset.mem_singleton.mp hy⟩


def MarginalUtility {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) : Ends :=
  reg.e_seq ⟨k - 1, by omega⟩

/-- The marginal utility end belongs to the difference set. -/
theorem marginal_utility_spec {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk ∈ S_opt reg k hk \ S_opt reg (k - 1) (by omega) := by
  rw [diff_S_opt_eq_singleton reg k hk_pos hk]
  exact Finset.mem_singleton_self _

/-- The marginal utility end is the `(k - 1)` indexed schedule entry. -/
theorem marginal_utility_eval {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    MarginalUtility reg k hk_pos hk = reg.e_seq ⟨k - 1, by omega⟩ :=
  rfl


theorem diminishing_marginal_utility {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N)
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


theorem purposeful_diminishing_marginal_utility
    {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N)
    (k1 k2 : ℕ) (hk1_pos : 1 ≤ k1) (hk2_le : k2 ≤ N) (hk_lt : k1 < k2)
    (sys1 : BundleAllocationMenu i t h reg k1 (by omega))
    (sys2 : BundleAllocationMenu i t h reg k2 hk2_le)
    (α1 α2 : Action)
    (h_purp1 : PurposefulAct i t h α1)
    (h_purp2 : PurposefulAct i t h α2)
    (h_active1 : α1 ≠ α₀)
    (h_active2 : α2 ≠ α₀) :
    sys1.bundle_of α1 = S_opt reg k1 (by omega) ∧
    sys2.bundle_of α2 = S_opt reg k2 hk2_le ∧
    Preference i t h
      (MarginalUtility reg k1 hk1_pos (by omega))
      (MarginalUtility reg k2 (by omega) hk2_le) := by
  have h_eq1 := purposeful_act_forces_S_opt reg k1 (by omega) sys1 α1 h_purp1 h_active1
  have h_eq2 := purposeful_act_forces_S_opt reg k2 hk2_le sys2 α2 h_purp2 h_active2
  have h_dmu := diminishing_marginal_utility reg k1 k2 hk1_pos hk2_le hk_lt
  exact ⟨h_eq1, h_eq2, h_dmu⟩


theorem sunk_cost_irrelevant_to_purposeful_act
    (i : Agent) (t : Moment) (h : History)
    (α_boondoggle : Action)
    (h_ne : α_boondoggle ≠ α₀)
    (h_no_unease : ¬ Preference i t h (End_of i α_boondoggle t h) (End_of i α₀ t h)) :
    ¬ PurposefulAct i t h α_boondoggle := by
  intro h_purp
  rcases h_purp.2.2.1 with rfl | h_pref
  · exact h_ne rfl
  · exact h_no_unease h_pref


theorem mengerian_backward_value_imputation
    {i : Agent} {t : Moment} {h : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t h m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N)
    (sys : BundleAllocationMenu i t h reg k hk)
    (α_lose_factor : Action)
    (h_lose_feas : α_lose_factor ∈ A_feas i t h)
    (h_lose_bundle : sys.bundle_of α_lose_factor = S_opt reg (k - 1) (by omega)) :
    (sys.bundle_of sys.α_opt \ sys.bundle_of α_lose_factor) = {MarginalUtility reg k hk_pos hk} ∧
    Preference i t h (End_of i sys.α_opt t h) (End_of i α_lose_factor t h) := by
  have h_diff : sys.bundle_of sys.α_opt \ sys.bundle_of α_lose_factor =
      {MarginalUtility reg k hk_pos hk} := by
    rw [sys.h_opt_bundle, h_lose_bundle]
    exact diff_S_opt_eq_singleton reg k hk_pos hk
  refine ⟨h_diff, ?_⟩
  have h_ne : sys.bundle_of α_lose_factor ≠ S_opt reg k hk := by
    intro h_eq
    have h_card1 : (sys.bundle_of α_lose_factor).card = k - 1 := by
      rw [h_lose_bundle, card_S_opt reg (k - 1) (by omega)]
    have h_card2 : (S_opt reg k hk).card = k := card_S_opt reg k hk
    rw [h_eq, h_card2] at h_card1
    omega
  exact sys.mengerian_preference α_lose_factor h_lose_feas h_ne


theorem intertemporal_capital_value_imputation
    {i : Agent} {t0 t1 t2 : Moment} {h_build h_cons : History} {m : Means} {N : ℕ}
    (reg : UnitRequirementSchedule i t1 h_build m N) (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N)
    (sys : BundleAllocationMenu i t1 h_build reg k hk)
    (α_build α_nonbuild α_lose_factor : Action)
    (h_next_build : IsNextMoment Precedence W.mem_hist t0 t1 h_build)
    (h_next_cons : IsNextMoment Precedence W.mem_hist t0 t2 h_cons)
    (h_branches_separate : ∀ u, Precedence t0 u →
      ¬ (W.mem_hist u h_build ∧ W.mem_hist u h_cons))
    (h_not_tr_b : ¬ W.IsTradeAction α_build := by intro h; cases h)
    (h_not_tr_c : ¬ W.IsTradeAction α_nonbuild := by intro h; cases h)
    (h_exec_build : enacted i t0 h_build = α_build)
    (h_exec_cons : enacted i t0 h_cons = α_nonbuild)
    (h_init_build : W.omega i t0 h_build m = k - 1)
    (h_init_cons : W.omega i t0 h_cons m = k - 1)
    (h_use_build : W.use_means α_build m = 0)
    (h_yield_build : W.yield_means α_build m = 1)
    (h_use_nonbuild : W.use_means α_nonbuild m = 0)
    (h_yield_nonbuild : W.yield_means α_nonbuild m = 0)
    (h_opt_req : W.use_means sys.α_opt m = k)
    (h_lose_feas : α_lose_factor ∈ A_feas i t1 h_build)
    (h_lose_bundle : sys.bundle_of α_lose_factor = S_opt reg (k - 1) (by omega)) :
    t1 ≠ t2 ∧
    W.omega i t1 h_build m = k ∧
    W.omega i t2 h_cons m = k - 1 ∧
    sys.α_opt ∉ A_feas i t2 h_cons ∧
    (sys.bundle_of sys.α_opt \ sys.bundle_of α_lose_factor) = {MarginalUtility reg k hk_pos hk} ∧
    Preference i t1 h_build
      (End_of i sys.α_opt t1 h_build) (End_of i α_lose_factor t1 h_build) := by
  have ht_distinct : t1 ≠ t2 := by
    intro h_eq
    subst t2
    exact h_branches_separate t1 h_next_build.2.2.1
      ⟨h_next_build.2.1, h_next_cons.2.1⟩
  have h_tr_b :=
    W.law_in_re_transition i t0 t1 h_build α_build m h_not_tr_b h_exec_build h_next_build
  rw [h_use_build, h_init_build, h_yield_build, Nat.add_zero] at h_tr_b
  have h_om_b : W.omega i t1 h_build m = k := by omega
  have h_tr_c :=
    W.law_in_re_transition i t0 t2 h_cons α_nonbuild m h_not_tr_c h_exec_cons h_next_cons
  rw [h_use_nonbuild, h_init_cons, h_yield_nonbuild, Nat.add_zero, Nat.add_zero] at h_tr_c
  have h_om_c : W.omega i t2 h_cons m = k - 1 := by omega
  have h_infeas : sys.α_opt ∉ A_feas i t2 h_cons := by
    apply infeasible_of_insufficient_endowment i t2 h_cons sys.α_opt m
    change W.omega i t2 h_cons m < W.use_means sys.α_opt m
    rw [h_tr_c, h_opt_req]
    omega
  have ⟨h_diff, h_pref⟩ :=
    mengerian_backward_value_imputation reg k hk_pos hk sys α_lose_factor h_lose_feas h_lose_bundle
  exact ⟨ht_distinct, h_om_b, h_om_c, h_infeas, h_diff, h_pref⟩


theorem intertemporal_consumption_stock_and_service
    {Service : Type} {i : W.Agent} {t t' : W.Moment} {h : W.History}
    {m : W.Means} (A : ServiceAccounting W Service)
    (α_consume : W.Action) (k : ℕ) (s : Service)
    (h_not_trade : ¬ W.IsTradeAction α_consume)
    (h_execute : W.enacted i t h = α_consume)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_stock : W.omega i t h m = k)
    (h_use : W.use_means α_consume m = 1)
    (h_yield : W.yield_means α_consume m = 0)
    (h_service : A.yield_service α_consume s = 1) :
    W.omega i t' h m + 1 = k ∧
    (InventoryRun.step
      (InventoryStep.production α_consume h_execute h_not_trade h_next)
      (InventoryRun.done t')).totalService A s = 1 := by
  have h_stock_law := W.law_in_re_transition i t t' h α_consume m
    h_not_trade h_execute h_next
  rw [h_use, h_yield, h_stock] at h_stock_law
  exact ⟨h_stock_law, by
    simp [InventoryRun.totalService, InventoryStep.action, h_service]⟩


theorem mengerian_factor_specificity_dichotomy
    (i : Agent) (t : Moment) (h : History)
    (α_spec α_prim α_alt : Action)
    (e₀ e_spec e_prim e_alt : Ends)
    (h_end₀ : End_of i α₀ t h = e₀)
    (h_end_spec : End_of i α_spec t h = e_spec)
    (h_end_prim : End_of i α_prim t h = e_prim)
    (h_end_alt : End_of i α_alt t h = e_alt)
    (h_ne_spec : α_spec ≠ α₀)
    (h_ne_prim : α_prim ≠ α₀)
    -- Neither primary end is preferred to the baseline.
    (h_spec_collapses : ¬ Preference i t h e_spec e₀)
    (h_prim_collapses : ¬ Preference i t h e_prim e₀)
    -- The alternative end is feasible, preferred to baseline, and undominated.
    (h_alt_feas : α_alt ∈ A_feas i t h)
    (h_alt_exec : Exec i t α_alt h)
    (h_alt_unease : Preference i t h e_alt e₀)
    (h_alt_undom : ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) e_alt) :
    (¬ PurposefulAct i t h α_spec) ∧
    (¬ PurposefulAct i t h α_prim) ∧
    (PurposefulAct i t h α_alt) := by
  have h_not_spec : ¬ PurposefulAct i t h α_spec := by
    intro h_purp
    rcases h_purp.2.2.1 with rfl | h_u
    · exact h_ne_spec rfl
    · rw [h_end_spec, h_end₀] at h_u
      exact h_spec_collapses h_u
  have h_not_prim : ¬ PurposefulAct i t h α_prim := by
    intro h_purp
    rcases h_purp.2.2.1 with rfl | h_u
    · exact h_ne_prim rfl
    · rw [h_end_prim, h_end₀] at h_u
      exact h_prim_collapses h_u
  have h_purp_alt : PurposefulAct i t h α_alt := by
    refine ⟨h_alt_feas, h_alt_exec, Or.inr ?_, ?_⟩
    · rw [h_end_alt, h_end₀]; exact h_alt_unease
    · intro β hβ
      rw [h_end_alt]
      exact h_alt_undom β hβ
  exact ⟨h_not_spec, h_not_prim, h_purp_alt⟩


theorem complement_starvation_not_teleological_dominates
    (b_stranded b_zero : Means → ℕ)
    (h_sterile : ∀ S : Finset Ends,
      JointlyAttains W.requirement b_stranded S → JointlyAttains W.requirement b_zero S) :
    ¬ TeleologicalBundleDominates W.requirement b_stranded b_zero := by
  intro ⟨_, ⟨S, hS1, hS2⟩⟩
  exact hS2 (h_sterile S hS1)

end DMU_TimePreference

/-- Complementary stocks are enough for absorption under unit requirements. -/
def InNeoclassicalAbsorptionRegime (buffer_stock substitute_stock req_comp : ℕ) : Prop :=
  req_comp ≤ buffer_stock + substitute_stock

/-- Combined buffer and substitute stocks below requirements force liquidation. -/
def InAustrianLiquidationRegime (buffer_stock substitute_stock req_comp : ℕ) : Prop :=
  buffer_stock + substitute_stock < req_comp

theorem neoclassical_vs_austrian_regime_boundary
    (buffer_stock substitute_stock req_comp : ℕ) :
    InAustrianLiquidationRegime buffer_stock substitute_stock req_comp ↔
      ¬ InNeoclassicalAbsorptionRegime buffer_stock substitute_stock req_comp := by
  dsimp [InAustrianLiquidationRegime, InNeoclassicalAbsorptionRegime]
  omega

theorem abct_buffer_regime_boundary
    (buffer_stock substitute_stock req_comp : ℕ) :
    InAustrianLiquidationRegime buffer_stock substitute_stock req_comp ↔
      ¬ InNeoclassicalAbsorptionRegime buffer_stock substitute_stock req_comp :=
  neoclassical_vs_austrian_regime_boundary buffer_stock substitute_stock req_comp

/-- Penalized substitutes complete a requirement exactly when their weighted
quantity covers the weighted requirement. -/
def CanCompleteWithSubstitutes
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ) : Prop :=
  req_comp * sub_penalty ≤ buffer_stock * sub_penalty + substitute_stock

/-- Liquidation occurs when penalized substitute supply falls strictly short. -/
def InConvexSubstitutionLiquidationRegime
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ) : Prop :=
  buffer_stock * sub_penalty + substitute_stock < req_comp * sub_penalty

/-- A penalized substitution technology carries positive evidence for the
weight used to compare buffer and substitute stocks directly within an ActionFrame. -/
structure PenalizedSubstitutionTechnology (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action) (m_buf m_sub : W.Means) where
  penalty : ℕ
  penaltyPositive : 0 < penalty

def PenalizedSubstitutionTechnology.bufferStock
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (_T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) : ℕ :=
  W.omega i t h m_buf

def PenalizedSubstitutionTechnology.substituteStock
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (_T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) : ℕ :=
  W.omega i t h m_sub

def PenalizedSubstitutionTechnology.requirement
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (_T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) : ℕ :=
  W.use_means α m_buf

def PenalizedSubstitutionTechnology.canComplete
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) : Prop :=
  CanCompleteWithSubstitutes T.bufferStock T.substituteStock T.requirement T.penalty

def PenalizedSubstitutionTechnology.liquidation
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) : Prop :=
  InConvexSubstitutionLiquidationRegime
    T.bufferStock T.substituteStock T.requirement T.penalty

theorem convex_substitution_liquidation_regime
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ)
    (h_short : buffer_stock * sub_penalty + substitute_stock <
      req_comp * sub_penalty) :
    InConvexSubstitutionLiquidationRegime buffer_stock substitute_stock req_comp sub_penalty :=
  h_short

theorem PenalizedSubstitutionTechnology.liquidation_implies_buffer_deficit
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) (h_liquidation : T.liquidation) :
    T.bufferStock < T.requirement := by
  dsimp [PenalizedSubstitutionTechnology.liquidation,
    InConvexSubstitutionLiquidationRegime] at h_liquidation
  have h_penalty_ge_one : 1 ≤ T.penalty := T.penaltyPositive
  by_contra h_not_lt
  have h_req_le : T.requirement ≤ T.bufferStock := Nat.le_of_not_gt h_not_lt
  have h_weighted : T.requirement * T.penalty ≤ T.bufferStock * T.penalty :=
    Nat.mul_le_mul_right T.penalty h_req_le
  omega

/-- Equality at the weighted threshold is completion, not liquidation. -/
theorem penalized_substitution_exact_threshold_regression :
    CanCompleteWithSubstitutes 2 6 5 2 ∧
      ¬ InConvexSubstitutionLiquidationRegime 2 6 5 2 := by
  constructor <;> norm_num [CanCompleteWithSubstitutes,
    InConvexSubstitutionLiquidationRegime]

/-- Stocks satisfying both the absorption and penalized liquidation regimes. -/
theorem convex_substitution_regime_non_vacuous :
    ∃ (buffer_stock substitute_stock req_comp sub_penalty : ℕ),
      InNeoclassicalAbsorptionRegime buffer_stock substitute_stock req_comp ∧
      2 ≤ sub_penalty ∧
      InConvexSubstitutionLiquidationRegime buffer_stock substitute_stock req_comp sub_penalty :=
  ⟨2, 3, 5, 2, by dsimp [InNeoclassicalAbsorptionRegime]; omega,
    by omega,
    by norm_num [InConvexSubstitutionLiquidationRegime]⟩

/-- Penalized substitution strictly expands liquidation beyond the unpenalized
stock shortfall whenever the substitution penalty is at least two. -/
theorem convex_substitution_regime_strictly_expands_liquidation
    (sub_penalty : ℕ) (h_penalty : 2 ≤ sub_penalty) :
    ∃ buffer_stock substitute_stock req_comp,
      InConvexSubstitutionLiquidationRegime
        buffer_stock substitute_stock req_comp sub_penalty ∧
      ¬ InAustrianLiquidationRegime buffer_stock substitute_stock req_comp := by
  refine ⟨2, 4, 5, ?_, ?_⟩
  · dsimp [InConvexSubstitutionLiquidationRegime]
    omega
  · dsimp [InAustrianLiquidationRegime]
    omega

/-- Every technology is either completable or in the strict liquidation
regime. -/
theorem penalized_substitution_completion_or_liquidation
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ) :
    CanCompleteWithSubstitutes buffer_stock substitute_stock req_comp sub_penalty ∨
      InConvexSubstitutionLiquidationRegime
        buffer_stock substitute_stock req_comp sub_penalty := by
  dsimp [CanCompleteWithSubstitutes, InConvexSubstitutionLiquidationRegime]
  omega

theorem convex_penalized_liquidation_regime_boundary
    (buffer_stock substitute_stock req_comp sub_penalty : ℕ) :
    InConvexSubstitutionLiquidationRegime
        buffer_stock substitute_stock req_comp sub_penalty ↔
      ¬ CanCompleteWithSubstitutes
        buffer_stock substitute_stock req_comp sub_penalty := by
  dsimp [InConvexSubstitutionLiquidationRegime, CanCompleteWithSubstitutes]
  omega

section DMU_TimePreference

variable [W : ActionFrame]

-- Section 2b: Fixed Unit Requirements


structure TeleologicalQuantumRegime
    (i : Agent) (t : Moment) (h : History) (m : Means) (N : ℕ) (q_min : ℕ) where
  hq : 1 ≤ q_min
  k : ℕ
  h_endow : endowment i t h m = k * q_min
  h_k_lt_N : k < N
  e_seq : Fin N → Ends
  e_seq_inj : Function.Injective e_seq
  quantum_requirement : ∀ r : Fin N, requirement (e_seq r) m = q_min
  strictly_ranked : ∀ (r s : Fin N), r < s → Preference i t h (e_seq r) (e_seq s)

/-- The set of ends indexed by `Fin N`. -/
def TeleologicalQuantumRegime.all_ends
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) : Finset Ends :=
  Finset.univ.image reg.e_seq

/-- Ends in the schedule whose indices are below `k`. -/
def S_opt_teleo {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (_hk : k ≤ N) : Finset Ends :=
  (Finset.filter (fun (r : Fin N) => r.val < k) Finset.univ).image reg.e_seq

/-- The selected ends belong to `all_ends`. -/
theorem S_opt_teleo_subset {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (hk : k ≤ N) :
    S_opt_teleo reg k hk ⊆ reg.all_ends := by
  dsimp [S_opt_teleo, TeleologicalQuantumRegime.all_ends]
  apply Finset.image_subset_image
  intro x _
  exact Finset.mem_univ x

/-- Cardinality of S*(k) is exactly k. -/
theorem card_S_opt_teleo {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (hk : k ≤ N) :
    (S_opt_teleo reg k hk).card = k := by
  dsimp [S_opt_teleo]
  rw [Finset.card_image_of_injective _ reg.e_seq_inj]
  exact card_filter_fin_lt k hk

/-- Total means requirement of any bundle S ⊆ all_ends equals |S| * q_min. -/
theorem teleological_bundle_requirement_eq_card_mul_q
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (S : Finset Ends) (hS : S ⊆ reg.all_ends) :
    (S.sum (fun e => requirement e m)) = S.card * q_min := by
  have h_const : ∀ e ∈ S, requirement e m = q_min := by
    intro e he
    have he_all : e ∈ reg.all_ends := hS he
    dsimp [TeleologicalQuantumRegime.all_ends] at he_all
    rcases Finset.mem_image.mp he_all with ⟨r, _, rfl⟩
    exact reg.quantum_requirement r
  have h_sum := Finset.sum_congr rfl h_const
  rw [h_sum, Finset.sum_const]
  rfl

/-- Bounding the total physical means requirement by k * q_min forces cardinality |S| ≤ k. -/
theorem teleological_quantum_bundle_card_le
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (S : Finset Ends)
    (hS : S ⊆ reg.all_ends) (k : ℕ)
    (h_feas : (S.sum (fun e => requirement e m)) ≤ k * q_min) :
    S.card ≤ k := by
  rw [teleological_bundle_requirement_eq_card_mul_q reg S hS] at h_feas
  have hq_pos : 0 < q_min := reg.hq
  exact Nat.le_of_mul_le_mul_right h_feas hq_pos


theorem S_opt_teleo_dominates_suboptimal_bundle
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (hk : k ≤ N)
    (S : Finset Ends) (hS_sub : S ⊆ reg.all_ends)
    (hS_card : S.card ≤ k) (hS_ne : S ≠ S_opt_teleo reg k hk) :
    (S_opt_teleo reg k hk \ S).Nonempty ∧
    (∀ e_in ∈ S_opt_teleo reg k hk \ S, ∀ e_out ∈ S \ S_opt_teleo reg k hk,
      Preference i t h e_in e_out) := by
  have h_nonempty : (S_opt_teleo reg k hk \ S).Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_sub : S_opt_teleo reg k hk ⊆ S := by
      intro x hx
      by_contra hx_not_in
      have : x ∈ S_opt_teleo reg k hk \ S := Finset.mem_sdiff.mpr ⟨hx, hx_not_in⟩
      rw [h_empty] at this
      cases this
    have h_card_opt : (S_opt_teleo reg k hk).card = k := card_S_opt_teleo reg k hk
    have h_eq : S_opt_teleo reg k hk = S := Finset.eq_of_subset_of_card_le h_sub (by omega)
    exact hS_ne h_eq.symm
  refine ⟨h_nonempty, ?_⟩
  intro e_in he_in e_out he_out
  rw [Finset.mem_sdiff] at he_in he_out
  have he_in_opt := he_in.1
  have he_out_s := he_out.1
  dsimp [S_opt_teleo] at he_in_opt
  rcases Finset.mem_image.mp he_in_opt with ⟨r, hr_filt, rfl⟩
  have hr_lt : r.val < k := (Finset.mem_filter.mp hr_filt).2
  have he_out_all : e_out ∈ reg.all_ends := hS_sub he_out_s
  dsimp [TeleologicalQuantumRegime.all_ends] at he_out_all
  rcases Finset.mem_image.mp he_out_all with ⟨s, _, rfl⟩
  have hs_not_opt := he_out.2
  have hs_ge : k ≤ s.val := by
    by_contra h_contra
    have hs_lt : s.val < k := by omega
    have hs_in_opt : reg.e_seq s ∈ S_opt_teleo reg k hk := by
      dsimp [S_opt_teleo]
      apply Finset.mem_image_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs_lt⟩
    exact hs_not_opt hs_in_opt
  have h_r_lt_s : r < s := by
    apply Fin.mk_lt_mk.mpr
    omega
  exact reg.strictly_ranked r s h_r_lt_s

/-- Feasible actions have bundles in `all_ends` with total requirement ≤ `k * q_min`;
    `α_opt` realizes `S_opt_teleo`. -/
structure TeleologicalBundleSystem (i : Agent) (t : Moment) (h : History) {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (hk : k ≤ N) where
  bundle_of : Action → Finset Ends
  bundle_all : ∀ α ∈ A_feas i t h, α ≠ α₀ →
    bundle_of α ⊆ reg.all_ends ∧ ((bundle_of α).sum (fun e => requirement e m)) ≤ k * q_min
  α_opt : Action
  h_opt_feas : α_opt ∈ A_feas i t h
  h_opt_bundle : bundle_of α_opt = S_opt_teleo reg k hk
  bundle_stock : Action → (Means → ℕ)
  h_end_eq_bundle : ∀ α, End_of i α t h = W.BundleEnd (bundle_stock α)
  h_opt_dominates : ∀ α ∈ A_feas i t h, bundle_of α ≠ S_opt_teleo reg k hk →
    W.SubjectiveTeleologicalDominates i t h (bundle_stock α_opt) (bundle_stock α)

theorem TeleologicalBundleSystem.mengerian_preference
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    {reg : TeleologicalQuantumRegime i t h m N q_min} {k : ℕ} {hk : k ≤ N}
    (sys : TeleologicalBundleSystem i t h reg k hk)
    (α : Action) (h_feas : α ∈ A_feas i t h) (h_sub : sys.bundle_of α ≠ S_opt_teleo reg k hk) :
    Preference i t h (End_of i sys.α_opt t h) (End_of i α t h) := by
  rw [sys.h_end_eq_bundle sys.α_opt, sys.h_end_eq_bundle α]
  exact W.teleological_bundle_dominance_induces_preference i t h
    (sys.bundle_stock sys.α_opt) (sys.bundle_stock α) (sys.h_opt_dominates α h_feas h_sub)


theorem purposeful_act_forces_teleological_S_opt
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ) (hk : k ≤ N)
    (sys : TeleologicalBundleSystem i t h reg k hk)
    (α_star : Action)
    (h_purp : PurposefulAct i t h α_star)
    (_h_active : α_star ≠ α₀) :
    sys.bundle_of α_star = S_opt_teleo reg k hk := by
  have h_feas := h_purp.1
  by_contra h_ne
  have h_pref := sys.mengerian_preference α_star h_feas h_ne
  have h_undom := h_purp.2.2.2 sys.α_opt sys.h_opt_feas
  exact h_undom h_pref

/-- The end at index `k - 1` in `reg.e_seq`. -/
def TeleologicalMarginalUtility {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min) (k : ℕ)
    (_hk_pos : 1 ≤ k) (_hk : k ≤ N) : Ends :=
  reg.e_seq ⟨k - 1, by omega⟩


theorem teleological_diminishing_marginal_utility
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min)
    (k1 k2 : ℕ) (hk1_pos : 1 ≤ k1) (hk2_le : k2 ≤ N) (hk_lt : k1 < k2) :
    Preference i t h
      (TeleologicalMarginalUtility reg k1 hk1_pos (by omega))
      (TeleologicalMarginalUtility reg k2 (by omega) hk2_le) := by
  dsimp [TeleologicalMarginalUtility]
  have hr_lt : (⟨k1 - 1, by omega⟩ : Fin N) < ⟨k2 - 1, by omega⟩ := by
    change k1 - 1 < k2 - 1
    omega
  exact reg.strictly_ranked ⟨k1 - 1, by omega⟩ ⟨k2 - 1, by omega⟩ hr_lt


theorem purposeful_teleological_diminishing_marginal_utility
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min)
    (k1 k2 : ℕ) (hk1_pos : 1 ≤ k1) (hk2_le : k2 ≤ N) (hk_lt : k1 < k2)
    (sys1 : TeleologicalBundleSystem i t h reg k1 (by omega))
    (sys2 : TeleologicalBundleSystem i t h reg k2 hk2_le)
    (α1 α2 : Action)
    (h_purp1 : PurposefulAct i t h α1)
    (h_purp2 : PurposefulAct i t h α2)
    (h_active1 : α1 ≠ α₀)
    (h_active2 : α2 ≠ α₀) :
    sys1.bundle_of α1 = S_opt_teleo reg k1 (by omega) ∧
    sys2.bundle_of α2 = S_opt_teleo reg k2 hk2_le ∧
    Preference i t h
      (TeleologicalMarginalUtility reg k1 hk1_pos (by omega))
      (TeleologicalMarginalUtility reg k2 (by omega) hk2_le) := by
  have h_eq1 := purposeful_act_forces_teleological_S_opt reg k1 (by omega) sys1 α1 h_purp1 h_active1
  have h_eq2 := purposeful_act_forces_teleological_S_opt reg k2 hk2_le sys2 α2 h_purp2 h_active2
  have h_dmu := teleological_diminishing_marginal_utility reg k1 k2 hk1_pos hk2_le hk_lt
  exact ⟨h_eq1, h_eq2, h_dmu⟩


theorem teleological_sub_quantum_remainder_sterile
    {i : Agent} {t : Moment} {h : History} {m : Means} {N q_min : ℕ}
    (reg : TeleologicalQuantumRegime i t h m N q_min)
    (S : Finset Ends) (hS : S ⊆ reg.all_ends) (k r : ℕ)
    (hr_lt : r < q_min)
    (h_feas : (S.sum (fun e => requirement e m)) ≤ k * q_min + r) :
    S.card ≤ k := by
  rw [teleological_bundle_requirement_eq_card_mul_q reg S hS] at h_feas
  by_contra h_gt
  have h_ge : k + 1 ≤ S.card := by omega
  have h_mul : (k + 1) * q_min ≤ S.card * q_min := Nat.mul_le_mul_right q_min h_ge
  have h_expand : (k + 1) * q_min = k * q_min + q_min := Nat.succ_mul k q_min
  omega


theorem teleological_sub_quantum_remainder_not_teleological_dominates
    (b1 b2 : Means → ℕ)
    (h_attain_equiv : ∀ S : Finset Ends,
      JointlyAttains W.requirement b1 S → JointlyAttains W.requirement b2 S) :
    ¬ TeleologicalBundleDominates W.requirement b1 b2 := by
  intro ⟨_, ⟨S, hS1, hS2⟩⟩
  exact hS2 (h_attain_equiv S hS1)


-- Section 3: Preference Condition on a Finite Set


/-- An end in `S` for which no `e ∈ S` satisfies `Pref e_min e`. -/
def IsLeastUrgentEnd (Pref : Ends → Ends → Prop) (S : Finset Ends) (e_min : Ends) : Prop :=
  e_min ∈ S ∧ ∀ e ∈ S, ¬ Pref e_min e


theorem mengerian_least_urgent_end_exists
    (S : Finset Ends) (hS : S.Nonempty)
    (Pref : Ends → Ends → Prop)
    (h_irrefl : ∀ x ∈ S, ¬ Pref x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Pref x y → Pref y z → Pref x z) :
    ∃ e_min ∈ S, IsLeastUrgentEnd Pref S e_min := by
  obtain ⟨m, hm_in, hm_min⟩ := exists_least_urgent_aux S.card S rfl hS Pref h_irrefl h_trans
  exact ⟨m, hm_in, ⟨hm_in, hm_min⟩⟩


theorem mengerian_marginal_sacrifice_exists
    (i : Agent) (t : Moment) (h : History)
    (S : Finset Ends) (hS : S.Nonempty)
    (h_trans : ∀ e1 ∈ S, ∀ e2 ∈ S, ∀ e3 ∈ S,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    ∃ e_sacrifice ∈ S,
      IsLeastUrgentEnd (Preference i t h) S e_sacrifice ∧
      ∀ e ∈ S, ¬ Preference i t h e_sacrifice e := by
  obtain ⟨e_min, hm_in, h_least⟩ :=
    exists_least_urgent_end i t h S hS h_trans
  exact ⟨e_min, hm_in, ⟨hm_in, h_least⟩, h_least⟩


-- Section 4: Time Preference and Feasible Deferral


/-- End `e` indexed by moment `τ`. -/
abbrev TimedEnd : Ends → Moment → Ends :=
  W.TimedEnd


def CausalNegativeTimePreference (i : Agent) (t : Moment) (h : History) (e : Ends) : Prop :=
  ∀ τ1 τ2 : Moment, (t = τ1 ∨ t < τ1) → τ1 < τ2 → Preference i t h (TimedEnd e τ2) (TimedEnd e τ1)


def CausalDoxasticOpenHorizon (i : Agent) (t : Moment) (h : History)
    (e : Ends) (α_near : Action) (τ1 : Moment) : Prop :=
  α_near ∈ A_feas i t h →
  End_of i α_near t h = TimedEnd e τ1 →
  (t = τ1 ∨ t < τ1) ∧
  ∃ (α_defer : Action) (τ2 : Moment),
    α_defer ∈ A_feas i t h ∧
    τ1 < τ2 ∧
    End_of i α_defer t h = TimedEnd e τ2

/-- Feasible deferral provides a distinct later outcome. -/
theorem causal_doxastic_open_horizon_implies_not_post_horizon
    (i : Agent) (t : Moment) (h : History) (e : Ends) (α_near : Action) (τ1 : Moment)
    (h_oeh : CausalDoxasticOpenHorizon i t h e α_near τ1)
    (h_near_feas : α_near ∈ A_feas i t h)
    (h_near_end : End_of i α_near t h = TimedEnd e τ1)
    (h_distinct : ∀ τ2, τ1 < τ2 → TimedEnd e τ2 ≠ End_of i α₀ t h) :
    ¬ IsPostHorizon i t h := by
  intro h_post
  obtain ⟨_, α_defer, τ2, h_defer_feas, h_lt, h_defer_end⟩ := h_oeh h_near_feas h_near_end
  have h_eq : α_defer = α₀ := Finset.mem_singleton.mp (h_post.symm ▸ h_defer_feas)
  have h_ne := h_distinct τ2 h_lt
  rw [← h_eq, h_defer_end] at h_ne
  exact h_ne rfl


theorem causal_not_purposeful_immediate_consumption_of_negative_time_pref
    (i : Agent) (t : Moment) (h : History) (e : Ends) (α_near : Action) (τ1 : Moment)
    (h_end : End_of i α_near t h = TimedEnd e τ1)
    (h_oeh : CausalDoxasticOpenHorizon i t h e α_near τ1)
    (h_neg : CausalNegativeTimePreference i t h e) :
    ¬ PurposefulAct i t h α_near := by
  intro h_act
  have h_feas := h_act.1
  obtain ⟨h_weak, α_defer, τ2, h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_feas h_end
  have h_pref_defer := h_neg τ1 τ2 h_weak h_lt
  rw [← h_end_defer, ← h_end] at h_pref_defer
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  exact h_undom h_pref_defer


theorem post_horizon_no_action
    (i : Agent) (t : Moment) (h : History) (α : Action)
    (h_post : IsPostHorizon i t h)
    (h_ne : α ≠ α₀) :
    ¬ PurposefulAct i t h α := by
  intro h_act
  have h_feas := h_act.1
  rw [h_post] at h_feas
  have h_eq : α = α₀ := Finset.mem_singleton.mp h_feas
  exact h_ne h_eq


theorem post_horizon_no_active_action
    (i : Agent) (t : Moment) (h : History) (α : Action)
    (h_post : IsPostHorizon i t h) :
    ¬ ActivePurposefulAct i t h α := by
  intro h_act
  have h_feas := h_act.1.1
  rw [h_post] at h_feas
  have h_eq : α = α₀ := Finset.mem_singleton.mp h_feas
  have h_np := purposeful_act_non_passive i t h α h_act.1 h_act.2
  exact h_np.1 h_eq


theorem causal_enacted_consumption_demonstrates_nonneg_time_pref
    (i : Agent) (t : Moment) (h : History) (e : Ends) (α_near : Action) (τ1 : Moment)
    (h_end : End_of i α_near t h = TimedEnd e τ1)
    (h_oeh : CausalDoxasticOpenHorizon i t h e α_near τ1)
    (h_act : PurposefulAct i t h α_near) :
    ∃ τ2 : Moment, τ1 < τ2 ∧ ¬ Preference i t h (TimedEnd e τ2) (TimedEnd e τ1) := by
  obtain ⟨_, α_defer, τ2, h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  rw [h_end_defer, h_end] at h_undom
  exact ⟨τ2, h_lt, h_undom⟩


def MenuComparable (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  ∀ β ∈ A_feas i t h, End_of i β t h ≠ End_of i α_star t h →
    (Preference i t h (End_of i α_star t h) (End_of i β t h) ∨
     Preference i t h (End_of i β t h) (End_of i α_star t h))


def DistinctEndDominantAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ A_feas i t h ∧
  Exec i t α_star h ∧
  Preference i t h (End_of i α_star t h) (End_of i α₀ t h) ∧
  ∀ β ∈ A_feas i t h, End_of i β t h ≠ End_of i α_star t h →
    Preference i t h (End_of i α_star t h) (End_of i β t h)


theorem purposeful_act_and_comparable_iff_distinct_dominant
    (i : Agent) (t : Moment) (h : History) (α_star : Action) :
    (ActivePurposefulAct i t h α_star ∧ MenuComparable i t h α_star) ↔
    DistinctEndDominantAct i t h α_star := by
  constructor
  · intro ⟨h_act, h_comp⟩
    refine ⟨h_act.1.1, h_act.1.2.1, h_act.2, ?_⟩
    intro β hβ h_ne
    cases h_comp β hβ h_ne with
    | inl h_pref => exact h_pref
    | inr h_pref_rev =>
      exact False.elim (h_act.1.2.2.2 β hβ h_pref_rev)
  · intro h_dom
    refine ⟨⟨⟨h_dom.1, h_dom.2.1, Or.inr h_dom.2.2.1, ?_⟩, h_dom.2.2.1⟩, ?_⟩
    · intro β hβ h_pref
      by_cases h_eq : End_of i β t h = End_of i α_star t h
      · rw [h_eq] at h_pref
        exact pref_irrefl i t h (End_of i α_star t h) h_pref
      · have h_dom_pref := h_dom.2.2.2 β hβ h_eq
        exact pref_asymm i t h h_dom_pref h_pref
    · intro β hβ h_ne
      exact Or.inl (h_dom.2.2.2 β hβ h_ne)


theorem causal_enacted_consumption_demonstrates_strict_time_pref
    (i : Agent) (t : Moment) (h : History) (e : Ends) (α_near : Action) (τ1 : Moment)
    (h_end : End_of i α_near t h = TimedEnd e τ1)
    (h_oeh : CausalDoxasticOpenHorizon i t h e α_near τ1)
    (h_act : DistinctEndDominantAct i t h α_near)
    (h_timed_inj : ∀ t1 t2 : Moment, t1 ≠ t2 → TimedEnd e t1 ≠ TimedEnd e t2) :
    ∃ τ2 : Moment, τ1 < τ2 ∧ Preference i t h (TimedEnd e τ1) (TimedEnd e τ2) := by
  obtain ⟨_, α_defer, τ2, h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_ne_mom : τ1 ≠ τ2 := fun h_eq => by subst h_eq; exact moment_lt_irrefl τ1 h_lt
  have h_ne_timed : TimedEnd e τ1 ≠ TimedEnd e τ2 := h_timed_inj τ1 τ2 h_ne_mom
  have h_ne_ends : End_of i α_defer t h ≠ End_of i α_near t h := by
    rw [h_end_defer, h_end]
    exact h_ne_timed.symm
  have h_dom := h_act.2.2.2 α_defer h_defer_feas h_ne_ends
  rw [h_end, h_end_defer] at h_dom
  exact ⟨τ2, h_lt, h_dom⟩


-- Section 5: Interest and Intertemporal Exchange


/-- End for holding or consuming `q` units of `m`. -/
abbrev QuantityEnd (m : Means) (q : ℕ) : Ends :=
  W.QuantityEnd m q

/-- End for consuming `q` units of `m` at `τ`. -/
def timedQuantityEnd (m : Means) (q : ℕ) (τ : Moment) : Ends :=
  TimedEnd (QuantityEnd m q) τ


theorem causal_enacted_unit_for_unit_exchange_rejected (i : Agent) (t : Moment) (h : History)
    (m : Means) (q : ℕ) (α_cons : Action) (τ1 : Moment)
    (h_end : End_of i α_cons t h = timedQuantityEnd m q τ1)
    (h_oeh : CausalDoxasticOpenHorizon i t h (QuantityEnd m q) α_cons τ1)
    (h_act : DistinctEndDominantAct i t h α_cons)
    (h_timed_inj : ∀ t1 t2 : Moment, t1 ≠ t2 →
      TimedEnd (QuantityEnd m q) t1 ≠ TimedEnd (QuantityEnd m q) t2) :
    ∃ τ2 : Moment, τ1 < τ2 ∧ Preference i t h (timedQuantityEnd m q τ1) (timedQuantityEnd m q τ2) :=
  causal_enacted_consumption_demonstrates_strict_time_pref i t h (QuantityEnd m q)
    α_cons τ1 h_end h_oeh h_act h_timed_inj


theorem purposeful_unit_for_unit_exchange_rejected (i : Agent) (t : Moment) (h : History)
    (m : Means) (q : ℕ) (τ1 τ2 : Moment)
    (h_pos_tp : Preference i t h (timedQuantityEnd m q τ1) (timedQuantityEnd m q τ2))
    (α_pres α_u4u : Action)
    (h_pres_feas : α_pres ∈ A_feas i t h)
    (h_pres_end : End_of i α_pres t h = timedQuantityEnd m q τ1)
    (h_u4u_end : End_of i α_u4u t h = timedQuantityEnd m q τ2) :
    ¬ PurposefulAct i t h α_u4u := by
  intro h_purp
  have h_undom := h_purp.2.2.2 α_pres h_pres_feas
  rw [h_u4u_end, h_pres_end] at h_undom
  exact h_undom h_pos_tp


theorem positive_originary_interest (i : Agent) (t : Moment) (h : History)
    (m : Means) (q q' : ℕ) (_hq : 0 < q)
    (τ1 τ2 : Moment)
    (h_pos_tp : Preference i t h (timedQuantityEnd m q τ1) (timedQuantityEnd m q τ2))
    (h_accept : Preference i t h (timedQuantityEnd m q' τ2) (timedQuantityEnd m q τ1))
    (h_sync_mono : q' ≤ q →
      Preference i t h (timedQuantityEnd m q τ2) (timedQuantityEnd m q' τ2) ∨
      timedQuantityEnd m q τ2 = timedQuantityEnd m q' τ2)
    (h_trans : ∀ e1 e2 e3,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    q < q' ∧ (∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ) := by
  have h_lt : q < q' := by
    by_contra h_not_lt
    have h_le : q' ≤ q := by omega
    have h_pref_cycle :=
      h_trans (timedQuantityEnd m q' τ2) (timedQuantityEnd m q τ1)
        (timedQuantityEnd m q τ2) h_accept h_pos_tp
    cases h_sync_mono h_le with
    | inl h_mono_pref =>
      exact pref_asymm i t h h_pref_cycle h_mono_pref
    | inr h_mono_eq =>
      rw [h_mono_eq] at h_pref_cycle
      exact pref_irrefl i t h (timedQuantityEnd m q' τ2) h_pref_cycle
  have h_prem : ∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ := by
    refine ⟨q' - q, by omega, by omega⟩
  exact ⟨h_lt, h_prem⟩


theorem purposeful_positive_originary_interest (i : Agent) (t : Moment) (h : History)
    (m : Means) (q q' : ℕ) (_hq : 0 < q) (τ1 τ2 : Moment)
    (h_pos_tp : Preference i t h (timedQuantityEnd m q τ1) (timedQuantityEnd m q τ2))
    (α_pres α_loan : Action)
    (h_pres_feas : α_pres ∈ A_feas i t h)
    (h_pres_end : End_of i α_pres t h = timedQuantityEnd m q τ1)
    (h_loan_end : End_of i α_loan t h = timedQuantityEnd m q' τ2)
    (h_loan_purp : PurposefulAct i t h α_loan)
    (h_sync_mono : q' ≤ q →
      Preference i t h (timedQuantityEnd m q τ2) (timedQuantityEnd m q' τ2) ∨
      timedQuantityEnd m q τ2 = timedQuantityEnd m q' τ2)
    (h_trans : ∀ e1 e2 e3,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    q < q' ∧ (∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ) := by
  have h_undom := h_loan_purp.2.2.2 α_pres h_pres_feas
  rw [h_loan_end, h_pres_end] at h_undom
  have h_lt : q < q' := by
    by_contra h_not_lt
    have h_le : q' ≤ q := by omega
    cases h_sync_mono h_le with
    | inl h_mono_pref =>
      have h_cycle :=
        h_trans (timedQuantityEnd m q τ1) (timedQuantityEnd m q τ2)
          (timedQuantityEnd m q' τ2) h_pos_tp h_mono_pref
      exact h_undom h_cycle
    | inr h_mono_eq =>
      rw [← h_mono_eq] at h_undom
      exact h_undom h_pos_tp
  have h_prem : ∃ δ : ℕ, δ ≥ 1 ∧ q' = q + δ := ⟨q' - q, by omega, by omega⟩
  exact ⟨h_lt, h_prem⟩


theorem bohm_bawerk_roundabout_productivity_necessity (i : Agent) (t : Moment) (h : History)
    (m : Means) (q_direct q_roundabout : ℕ) (hq : 0 < q_direct) (τ_direct τ_later : Moment)
    (h_pos_tp :
      Preference i t h (timedQuantityEnd m q_direct τ_direct) (timedQuantityEnd m q_direct τ_later))
    (α_direct α_roundabout : Action)
    (h_direct_feas : α_direct ∈ A_feas i t h)
    (h_direct_end : End_of i α_direct t h = timedQuantityEnd m q_direct τ_direct)
    (h_round_end : End_of i α_roundabout t h = timedQuantityEnd m q_roundabout τ_later)
    (h_round_purp : PurposefulAct i t h α_roundabout)
    (h_sync_mono : q_roundabout ≤ q_direct →
      Preference i t h
        (timedQuantityEnd m q_direct τ_later) (timedQuantityEnd m q_roundabout τ_later) ∨
      timedQuantityEnd m q_direct τ_later = timedQuantityEnd m q_roundabout τ_later)
    (h_trans : ∀ e1 e2 e3,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    q_direct < q_roundabout ∧
    (∃ δ_cap : ℕ, δ_cap ≥ 1 ∧ q_roundabout = q_direct + δ_cap) :=
  purposeful_positive_originary_interest i t h m q_direct q_roundabout hq τ_direct τ_later
    h_pos_tp α_direct α_roundabout h_direct_feas h_direct_end h_round_end
    h_round_purp h_sync_mono h_trans


theorem capital_accumulation_unlocks_action_menu_epoch
    {i : Agent} {t0 t1 : Moment} {h : History} {m_cap m_prod : Means}
    (α_build α_primitive α_roundabout : Action)
    (q_primitive q_high : ℕ) (τ_prim τ_high : Moment)
    (h_next : IsNextMoment Precedence W.mem_hist t0 t1 h)
    (h_not_tr_b : ¬ W.IsTradeAction α_build := by intro h; cases h)
    (h_exec_build : enacted i t0 h = α_build)
    (h_init_cap : W.omega i t0 h m_cap = 0)
    (h_use_build : W.use_means α_build m_cap = 0)
    (h_yield_build : W.yield_means α_build m_cap = 1)
    (h_round_req : W.use_means α_roundabout m_cap = 1)
    (h_round_feas_t1 : α_roundabout ∈ A_feas i t1 h)
    (h_menu_sub : A_feas i t0 h ⊆ A_feas i t1 h)
    (h_prim_end : End_of i α_primitive t0 h = timedQuantityEnd m_prod q_primitive τ_prim)
    (h_round_end : End_of i α_roundabout t1 h = timedQuantityEnd m_prod q_high τ_high)
    (h_phys_surplus : q_primitive < q_high)
    (h_pref : Preference i t1 h
      (timedQuantityEnd m_prod q_high τ_high) (timedQuantityEnd m_prod q_primitive τ_prim)) :
    W.omega i t1 h m_cap = 1 ∧
    α_roundabout ∉ A_feas i t0 h ∧
    A_feas i t0 h ⊂ A_feas i t1 h ∧
    q_primitive < q_high ∧
    Preference i t1 h (End_of i α_roundabout t1 h) (End_of i α_primitive t0 h) := by
  have h_tr := W.law_in_re_transition i t0 t1 h α_build m_cap h_not_tr_b h_exec_build h_next
  rw [h_use_build, h_init_cap, h_yield_build, Nat.add_zero] at h_tr
  have h_cap_t1 : W.omega i t1 h m_cap = 1 := by omega
  have h_infeas_t0 : α_roundabout ∉ A_feas i t0 h := by
    apply infeasible_of_insufficient_endowment i t0 h α_roundabout m_cap
    change W.omega i t0 h m_cap < W.use_means α_roundabout m_cap
    rw [h_init_cap, h_round_req]
    decide
  have h_ssub : A_feas i t0 h ⊂ A_feas i t1 h :=
    Finset.ssubset_iff_subset_ne.mpr ⟨h_menu_sub, fun h_eq => h_infeas_t0 (h_eq ▸ h_round_feas_t1)⟩
  have h_pref_ends :
    Preference i t1 h (End_of i α_roundabout t1 h) (End_of i α_primitive t0 h) := by
    rw [h_round_end, h_prim_end]
    exact h_pref
  exact ⟨h_cap_t1, h_infeas_t0, h_ssub, h_phys_surplus, h_pref_ends⟩


theorem saving_for_winter_is_positive_time_pref_for_security
    (i : Agent) (t_aut t_win : Moment) (h : History)
    (e_survival e_security e_feast : Ends)
    (h_pos_tp_survival : Preference i t_aut h
      (TimedEnd e_survival t_aut) (TimedEnd e_survival t_win))
    (h_pos_tp_security : Preference i t_aut h
      (TimedEnd e_security t_aut) (TimedEnd e_security t_win))
    (h_pos_tp_feast : Preference i t_aut h (TimedEnd e_feast t_aut) (TimedEnd e_feast t_win))
    (h_security_over_feast : Preference i t_aut h
      (TimedEnd e_security t_aut) (TimedEnd e_feast t_aut))
    (h_winter_over_autumn_feast : Preference i t_aut h
      (TimedEnd e_survival t_win) (TimedEnd e_feast t_aut)) :
    (∀ e ∈ ({e_survival, e_security, e_feast} : Finset Ends),
      Preference i t_aut h (TimedEnd e t_aut) (TimedEnd e t_win)) ∧
    Preference i t_aut h (TimedEnd e_security t_aut) (TimedEnd e_security t_win) ∧
    Preference i t_aut h (TimedEnd e_security t_aut) (TimedEnd e_feast t_aut) ∧
    Preference i t_aut h (TimedEnd e_survival t_win) (TimedEnd e_feast t_aut) := by
  refine ⟨?_, h_pos_tp_security, h_security_over_feast, h_winter_over_autumn_feast⟩
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact h_pos_tp_survival
  · exact h_pos_tp_security
  · exact h_pos_tp_feast

end DMU_TimePreference


theorem finite_model_quantity_monotonicity
    (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
    (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
    (q q' : ℕ) (τ : FiniteBranchingModel.Moment)
    (hq : q' < q) :
    @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel m q τ)
      (@timedQuantityEnd FiniteBranchingModel m q' τ) := by
  change end_rank (ModelEnd.timed (ModelEnd.quantity m q') τ) <
         end_rank (ModelEnd.timed (ModelEnd.quantity m q) τ)
  dsimp [end_rank]
  omega


theorem causal_intertemporal_chain_non_vacuous :
    ∃ (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
      (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
      (q q' : ℕ) (α_cons : FiniteBranchingModel.Action) (τ1 : FiniteBranchingModel.Moment),
      @PurposefulAct FiniteBranchingModel i t h α_cons ∧
      @DistinctEndDominantAct FiniteBranchingModel i t h α_cons ∧
      @CausalDoxasticOpenHorizon FiniteBranchingModel i t h
        (@QuantityEnd FiniteBranchingModel m q) α_cons τ1 ∧
      ¬ @IsPostHorizon FiniteBranchingModel i t h ∧
      (∃ (τ2 : FiniteBranchingModel.Moment) (δ : ℕ),
        0 < q ∧ @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 ∧ q < q' ∧ δ ≥ 1 ∧ q' = q + δ ∧
        @Preference FiniteBranchingModel i t h
          (@TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) τ1)
          (@TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) τ2) ∧
        @Preference FiniteBranchingModel i t h
          (@timedQuantityEnd FiniteBranchingModel m q τ1)
          (@timedQuantityEnd FiniteBranchingModel m q τ2)) := by
  let i : Fin 2 := 0
  let t : Fin 4 := 0
  let h : Fin 3 := 1
  let m : Fin 3 := 1
  let q : ℕ := 1
  let q' : ℕ := 2
  let α_cons : ModelAction := ModelAction.consume
  let τ1 : Fin 4 := 0
  have h_purp : @PurposefulAct FiniteBranchingModel i t h α_cons := by
    change (ModelAction.consume ∈
      ({ModelAction.idle, ModelAction.consume, ModelAction.defer} : Finset ModelAction)) ∧
           (branch_incidence 0 1 ∧ (ModelAction.consume = ModelAction.consume)) ∧
           (ModelAction.consume = ModelAction.idle ∨
            (end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) <
             end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0))) ∧
           ∀ (β : ModelAction), β ∈
            ({ModelAction.idle, ModelAction.consume, ModelAction.defer} : Finset ModelAction) →
             ¬ (end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
                end_rank (match β with
                  | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
                  | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
                  | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1))
    refine ⟨by decide, ⟨by decide, rfl⟩, Or.inr (by decide), ?_⟩
    intro β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl <;> decide
  have h_comp : @MenuComparable FiniteBranchingModel i t h α_cons := by
    change ∀ (β : ModelAction), β ∈
      ({ModelAction.idle, ModelAction.consume, ModelAction.defer} : Finset ModelAction) →
      (match β with
       | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
       | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
       | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1) ≠ ModelEnd.timed (ModelEnd.quantity 1 1) 0 →
      (end_rank (match β with
       | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
       | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
       | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1) <
       end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) ∨
       end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
       end_rank (match β with
       | ModelAction.idle => ModelEnd.timed (ModelEnd.quantity 0 0) 0
       | ModelAction.consume => ModelEnd.timed (ModelEnd.quantity 1 1) 0
       | _ => ModelEnd.timed (ModelEnd.quantity 1 1) 1))
    intro β hβ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl
    · left; decide
    · exact False.elim (hne rfl)
    · left; decide
  have h_dom : @DistinctEndDominantAct FiniteBranchingModel i t h α_cons :=
    (@purposeful_act_and_comparable_iff_distinct_dominant FiniteBranchingModel i t h α_cons).mp
      ⟨⟨h_purp, (show end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) <
                      end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) by decide)⟩, h_comp⟩
  have h_end :
    @End_of FiniteBranchingModel i α_cons t h = @timedQuantityEnd FiniteBranchingModel m q τ1 := rfl
  have h_causal_oeh :
    @CausalDoxasticOpenHorizon FiniteBranchingModel i t h
      (@QuantityEnd FiniteBranchingModel m q) α_cons τ1 := by
    intro _ _
    refine ⟨Or.inl rfl, ModelAction.defer, (1 : Fin 4), by decide,
      ⟨rfl, show (1 : Fin 4) ≠ 0 by decide⟩, rfl⟩
  have h_distinct : ∀ τ2 : Fin 4, @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 →
      @TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) τ2 ≠
      @End_of FiniteBranchingModel i ModelAction.idle t h := by
    intro τ2 _ heq
    change ModelEnd.timed (ModelEnd.quantity 1 1) τ2 =
      ModelEnd.timed (ModelEnd.quantity 0 0) 0 at heq
    injection heq with hq _
    injection hq with _ hq'
    exact Nat.zero_ne_one hq'.symm
  have h_not_post :=
    @causal_doxastic_open_horizon_implies_not_post_horizon FiniteBranchingModel i t h
    (@QuantityEnd FiniteBranchingModel m q) α_cons τ1 h_causal_oeh (by decide) h_end h_distinct
  have h_timed_inj : ∀ t1 t2 : FiniteBranchingModel.Moment, t1 ≠ t2 →
      @TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) t1 ≠
      @TimedEnd FiniteBranchingModel (@QuantityEnd FiniteBranchingModel m q) t2 := by
    intro (t1 : Fin 4) (t2 : Fin 4) hne heq
    have : t1 = t2 := ModelEnd.timed.inj heq |>.2
    exact hne this
  obtain ⟨τ2, h_lt, h_pos_tp⟩ :=
    @causal_enacted_consumption_demonstrates_strict_time_pref FiniteBranchingModel i t h
      (@QuantityEnd FiniteBranchingModel m q) α_cons τ1 h_end h_causal_oeh h_dom h_timed_inj
  have h_u4u : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel m q τ1)
      (@timedQuantityEnd FiniteBranchingModel m q τ2) :=
    h_pos_tp
  have h_accept : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel m q' τ2)
      (@timedQuantityEnd FiniteBranchingModel m q τ1) := by
    change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
           end_rank (ModelEnd.timed (ModelEnd.quantity 1 2) τ2)
    dsimp [end_rank]
    split_ifs <;> omega
  have h_sync_mono : q' ≤ q →
      @Preference FiniteBranchingModel i t h (@timedQuantityEnd FiniteBranchingModel m q τ2)
        (@timedQuantityEnd FiniteBranchingModel m q' τ2) ∨
      @timedQuantityEnd FiniteBranchingModel m q τ2 =
        @timedQuantityEnd FiniteBranchingModel m q' τ2 := by
    intro h_le
    rcases Nat.lt_or_eq_of_le h_le with h_lt_q | h_eq_q
    · exact Or.inl (finite_model_quantity_monotonicity i t h m q q' τ2 h_lt_q)
    · right; rw [h_eq_q]
  have h_trans : ∀ e1 e2 e3,
      @Preference FiniteBranchingModel i t h e1 e2 →
      @Preference FiniteBranchingModel i t h e2 e3 →
      @Preference FiniteBranchingModel i t h e1 e3 := by
    intro e1 e2 e3 h12 h23
    exact Nat.lt_trans h23 h12
  obtain ⟨hq_lt, ⟨δ, hδ_ge, hq'_eq⟩⟩ :=
    @positive_originary_interest FiniteBranchingModel i t h m q q' Nat.zero_lt_one τ1 τ2
      h_pos_tp h_accept h_sync_mono h_trans
  exact ⟨i, t, h, m, q, q', α_cons, τ1, h_purp, h_dom, h_causal_oeh, h_not_post,
         ⟨τ2, δ, Nat.zero_lt_one, h_lt, hq_lt, hδ_ge, hq'_eq, h_pos_tp, h_u4u⟩⟩


section TeleologicalComplementarity

variable [W : ActionFrame]


theorem teleological_quantum_subsumes_complementarity
    {i : Agent} {t : Moment} {h : History} {m : Means}
    (reg : TeleologicalQuantumRegime i t h m 2 2) :
    Preference i t h
      (TeleologicalMarginalUtility reg 1 (by omega) (by omega))
      (TeleologicalMarginalUtility reg 2 (by omega) (by omega)) :=
  teleological_diminishing_marginal_utility reg 1 2 (by omega) (by omega) (by omega)


theorem dmu_fails_under_complementarity
    (m_left m_right : Means) (h_diff : m_left ≠ m_right) :
    let b_zero : Means → ℕ := fun _ => 0
    let b_left : Means → ℕ := fun m => if m = m_left then 1 else 0
    let b_pair : Means → ℕ := fun m => if m = m_left ∨ m = m_right then 1 else 0
    PhysicalBundleDominates b_left b_zero ∧
    PhysicalBundleDominates b_pair b_left ∧
    b_left m_right = 0 ∧ b_pair m_right = 1 := by
  dsimp [PhysicalBundleDominates]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro m; split_ifs <;> omega
  · use m_left; simp
  · intro m
    by_cases hm : m = m_left
    · subst hm; simp
    · simp [hm]
  · use m_right; simp [h_diff.symm]
  · simp [h_diff.symm]
  · simp


theorem teleological_complementarity_resolves_dmu_anomaly
    (b_left b_zero : Means → ℕ)
    (h_sterile : ∀ S : Finset Ends,
      JointlyAttains W.requirement b_left S → JointlyAttains W.requirement b_zero S) :
    ¬ TeleologicalBundleDominates W.requirement b_left b_zero :=
  teleological_sub_quantum_remainder_not_teleological_dominates b_left b_zero h_sterile

end TeleologicalComplementarity

end Praxeology

end
