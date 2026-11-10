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
public import Praxeology.Marginal.AllocationChoice
public import Praxeology.Marginal.AllocationActionFrame
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

Local ordinal allocation results, finite ranked-schedule consequences,
Mengerian marginal sacrifice, roundabout production, and conditional
intertemporal preference results. The legacy schedule theorems below only
derive preference from an assumed ranking; they do not derive the ranking
from purposeful choice.
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


/-- Complementary ends requirement: two distinct means are both required in positive quantities
to attain end `e`. -/
def ComplementaryEndsRequirement (W : ActionFrame) (e : W.Ends) (m₁ m₂ : W.Means) : Prop :=
  m₁ ≠ m₂ ∧ 1 ≤ W.requirement e m₁ ∧ 1 ≤ W.requirement e m₂

/-- If two means are complementary for end `e`, then attaining `e` from an inventory bundle `b`
requires positive stock of both means. -/
theorem complementary_attainment_requires_both_means
    (e : Ends) (m₁ m₂ : Means)
    (h_comp : ComplementaryEndsRequirement W e m₁ m₂)
    (b : Means → ℕ) (h_attains : AttainsEnd W.requirement b e) :
    1 ≤ b m₁ ∧ 1 ≤ b m₂ := by
  dsimp [AttainsEnd] at h_attains
  exact ⟨le_trans h_comp.2.1 (h_attains m₁), le_trans h_comp.2.2 (h_attains m₂)⟩

/-- When complement `m₂` is absent (`b m₂ = 0`), expanding `m₁` to any quantity
never enables attainment of `e`. -/
theorem missing_complement_precludes_attainment
    (e : Ends) (m₁ m₂ : Means)
    (h_comp : ComplementaryEndsRequirement W e m₁ m₂)
    (b : Means → ℕ) (h_zero : b m₂ = 0) :
    ¬ AttainsEnd W.requirement b e := by
  intro h_attains
  have h_both := complementary_attainment_requires_both_means e m₁ m₂ h_comp b h_attains
  omega

/-- Purposeful action cannot attain an end requiring missing complement `m₂` when
the agent's endowment of `m₂` is zero. -/
theorem missing_complement_precludes_purposeful_act
    (i : Agent) (t : Moment) (h : History)
    (α : Action) (e : Ends) (m₁ m₂ : Means)
    (h_comp : ComplementaryEndsRequirement W e m₁ m₂)
    (h_req : W.requirement e m₂ ≤ W.use_means α m₂)
    (h_omega : endowment i t h m₂ = 0)
    (h_feas : α ∈ A_feas i t h) :
    False := by
  have h_coupling := (W.A_feas_coupling i t h α).mp h_feas
  have h_res : W.use_means α m₂ ≤ endowment i t h m₂ := h_coupling.2 m₂
  have h_req_pos : 1 ≤ W.requirement e m₂ := h_comp.2.2
  omega

/-- When stock covers the joint requirement of complementary factors, action `α`
attains `e` in a `PurposefulAct` when it is contemplated, executed, strictly improves
over passive baseline (or is passive), and is undominated on the feasible menu. -/
theorem complementary_stock_enables_purposeful_act
    (i : Agent) (t : Moment) (h : History)
    (α : Action) (e : Ends)
    (h_cont : α ∈ A_cont i t h)
    (h_stock : ∀ m, W.use_means α m ≤ endowment i t h m)
    (h_exec : Exec i t α h)
    (h_end : End_of i α t h = e)
    (h_baseline : α = α₀ ∨ Preference i t h e (End_of i α₀ t h))
    (h_undom : ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) e) :
    PurposefulAct i t h α := by
  have h_feas : α ∈ A_feas i t h :=
    (W.A_feas_coupling i t h α).mpr ⟨h_cont, h_stock⟩
  refine ⟨h_feas, h_exec, ?_, ?_⟩
  · rcases h_baseline with rfl | h_pref
    · exact Or.inl rfl
    · rw [h_end]
      exact Or.inr h_pref
  · intro β hβ
    rw [h_end]
    exact h_undom β hβ

/-- Expanding an unmatched complementary stock creates zero subjective teleological gain
when all valued ends require the missing complement. -/
theorem unmatched_complement_no_subjective_teleological_gain
    (m₁ m₂ : Means) (target_e : Ends)
    (h_comp : ComplementaryEndsRequirement W target_e m₁ m₂)
    (b_stranded b_zero : Means → ℕ)
    (h_zero_m2 : b_stranded m₂ = 0)
    (h_zero_stock : ∀ m, b_zero m = 0) :
    ¬ SubjectiveTeleologicalDominates W.requirement
      (fun e' => e' = target_e) b_stranded b_zero := by
  rintro ⟨_, ⟨S, h_val, h_stock, h_not⟩⟩
  have h_empty : S = ∅ := by
    by_contra h_ne
    have h_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    obtain ⟨e', he'⟩ := h_nonempty
    have h_all : ∀ x ∈ S, W.requirement x m₂ = W.requirement target_e m₂ := by
      intro x hx
      rw [h_val x hx]
    have hsum : S.sum (fun e'' => W.requirement e'' m₂) = S.card * W.requirement target_e m₂ := by
      rw [Finset.sum_congr rfl h_all, Finset.sum_const]
      rfl
    have h_bound : S.sum (fun e'' => W.requirement e'' m₂) ≤ b_stranded m₂ :=
      h_stock m₂
    rw [h_zero_m2, hsum] at h_bound
    have h_card_pos : 0 < S.card := Finset.card_pos.mpr ⟨e', he'⟩
    have h_req_pos : 0 < W.requirement target_e m₂ := h_comp.2.2
    have h_prod_pos : 0 < S.card * W.requirement target_e m₂ := Nat.mul_pos h_card_pos h_req_pos
    omega
  rw [h_empty] at h_not
  apply h_not
  intro m
  simp [h_zero_stock m]

/-- Satiation on finite menu: for any decision node in an `ActionFrame`,
the set of feasible actions is finite, so expanding endowments beyond maximum
contemplated input requirements cannot expand the set of attainable valued ends. -/
theorem action_frame_attainable_ends_finite
    (i : Agent) (t : Moment) (h : History) :
    ((A_feas i t h).image (End_of i · t h)).card ≤ (A_cont i t h).card := by
  have h_sub : A_feas i t h ⊆ A_cont i t h := fun α hα =>
    ((W.A_feas_coupling i t h α).mp hα).1
  have h_card_feas : (A_feas i t h).card ≤ (A_cont i t h).card :=
    Finset.card_le_card h_sub
  exact le_trans (Finset.card_image_le) h_card_feas


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


theorem intertemporal_consumption_stock_and_service [BilateralExchangeFrame W]
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

/-- Liquidation regime induces physical infeasibility and non-purposefulness of completion. -/
theorem PenalizedSubstitutionTechnology.liquidation_infeasible
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub) (h_liquidation : T.liquidation) :
    α ∉ W.A_feas i t h ∧ ¬ PurposefulAct i t h α := by
  have h_deficit := T.liquidation_implies_buffer_deficit h_liquidation
  have h_not_feas : α ∉ W.A_feas i t h := by
    rw [W.A_feas_coupling]
    rintro ⟨_, h_cov⟩
    have h_m := h_cov m_buf
    dsimp [PenalizedSubstitutionTechnology.bufferStock,
      PenalizedSubstitutionTechnology.requirement] at h_deficit
    omega
  exact ⟨h_not_feas, fun h_purp => h_not_feas h_purp.1⟩

/-- When penalized substitute stocks fall strictly short of the completion requirement,
the candidate production action is physically infeasible and non-purposeful. -/
theorem convex_substitution_liquidation_regime
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {α : W.Action} {m_buf m_sub : W.Means}
    (T : PenalizedSubstitutionTechnology W i t h α m_buf m_sub)
    (h_short : InConvexSubstitutionLiquidationRegime
      T.bufferStock T.substituteStock T.requirement T.penalty) :
    α ∉ W.A_feas i t h ∧ ¬ PurposefulAct i t h α :=
  T.liquidation_infeasible h_short

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

-- Section 2b: Fixed Unit Requirements and Teleological Quanta

/-- Quantum capacity bound: when each end in `S` requires at least `q_min` units of `m`,
an endowment of `k * q_min + r` with sub-quantum remainder `r < q_min` bounds the number
of attainable ends in `S` to at most `k`. -/
theorem teleological_quantum_capacity_bound
    (m : Means) (q_min : ℕ)
    (S : Finset Ends)
    (h_req : ∀ e ∈ S, q_min ≤ W.requirement e m)
    (k r : ℕ) (hr_lt : r < q_min)
    (h_feas : (S.sum (fun e => W.requirement e m)) ≤ k * q_min + r) :
    S.card ≤ k := by
  have h_sum_ge : S.card * q_min ≤ S.sum (fun e => W.requirement e m) := by
    have h_le := Finset.sum_le_sum h_req
    rw [Finset.sum_const, nsmul_eq_mul] at h_le
    exact h_le
  by_contra h_gt
  have h_ge : k + 1 ≤ S.card := by omega
  have h_mul : (k + 1) * q_min ≤ S.card * q_min := Nat.mul_le_mul_right q_min h_ge
  have h_expand : (k + 1) * q_min = k * q_min + q_min := Nat.succ_mul k q_min
  omega


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


theorem finite_preference_relation_has_least_element
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


section TimePreferenceFixedEnds

variable [IntertemporalEnds W]

/-- End `e` indexed by moment `τ`. -/
abbrev TimedEnd : Ends → Moment → Ends :=
  W.TimedEnd


/-! `CausalNegativeTimePreference` is a universal condition over the specified
timed end and feasible dates. It is stronger than a demonstrated preference
between one particular pair of timing alternatives. -/
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

end TimePreferenceFixedEnds


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


/-! An enacted purposeful near-timing choice, together with a feasible later
alternative for the same underlying end, rules out strict preference for that
particular later outcome. This is a local revealed-choice result; it does not
establish a universal time-preference ordering. -/
theorem causal_enacted_consumption_demonstrates_nonneg_time_pref [IntertemporalEnds W]
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


/-! If a purposeful act strictly dominates every feasible action with a
distinct end, and a later timing alternative is feasible with a distinct
timed end, the choice reveals preference for the nearer date in that pair.
Injectivity of the timing map is explicit; the result does not assert a
universal preference over all dates or ends. -/
theorem strict_time_preference_from_distinct_end_dominance [IntertemporalEnds W]
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

section InterestIntertemporalExchange

variable [IntertemporalEnds W]


/-- End for holding or consuming `q` units of `m`. -/
abbrev QuantityEnd (m : Means) (q : ℕ) : Ends :=
  W.QuantityEnd m q

/-- End for consuming `q` units of `m` at `τ`. -/
@[reducible]
def timedQuantityEnd (m : Means) (q : ℕ) (τ : Moment) : Ends :=
  TimedEnd (QuantityEnd m q) τ


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


/-! The positive repayment-premium conclusion follows from the stated
intertemporal preference, acceptance comparison, same-date quantity
monotonicity, and transitivity. `_hq` marks that the represented principal is
positive for the loan interpretation; the arithmetic inequality itself does
not use this domain condition. This theorem concerns ordinal quantity and
timing comparisons, not a nominal loan rate. -/
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


/-! This version additionally requires the loan action to be purposeful and a
feasible comparison action preserving the original quantity at the earlier
date. It derives the quantity premium under the same explicit preference laws;
it is not a theorem about every contract or a nominal interest rate. -/
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

end InterestIntertemporalExchange


/-! ## Security, Storage, and Explicit Choice Premises

Storage alone preserves later options; it does not prove a strict preference
for earlier dates. An extra valued service, actually attainable only under
earlier control, supplies the strict part of teleological dominance. The
following records keep those physical and ordinal premises explicit. -/

/-- Evidence that an earlier control bundle can reproduce every valued plan
available from a later bundle, and can attain one additional valued security
service. The represented actions are feasible and executed, and their intended
ends are tied to the corresponding physical bundles. -/
structure EarlierControlSecurityEvidence (i : Agent) (t : Moment) (h : History) where
  earlierBundle : Means → ℕ
  laterBundle : Means → ℕ
  earlierAction : Action
  laterAction : Action
  earlierAction_feasible : earlierAction ∈ A_feas i t h
  laterAction_feasible : laterAction ∈ A_feas i t h
  /-- The selected earlier-control action is the actual action. The later
  control option is evaluated as an alternative and is not also required to
  occur on this same actor-history. -/
  earlierAction_executed : Exec i t earlierAction h
  earlierAction_end : End_of i earlierAction t h = W.BundleEnd earlierBundle
  laterAction_end : End_of i laterAction t h = W.BundleEnd laterBundle
  storage_reproduces_valued_plans : ∀ S,
    (∀ e ∈ S, W.ValuedEnd i t h e) →
    JointlyAttains W.requirement laterBundle S →
    JointlyAttains W.requirement earlierBundle S
  earlySecurityService : Ends
  security_is_valued : W.ValuedEnd i t h earlySecurityService
  security_attainable_early : AttainsEnd W.requirement earlierBundle
    earlySecurityService
  security_unattainable_late : ¬ AttainsEnd W.requirement laterBundle
    earlySecurityService

/-- Storage plus an additional valued service derives preference for the
earlier control bundle. No universal strict time-preference law is assumed. -/
theorem earlier_control_preferred_from_storage_and_security
    (E : EarlierControlSecurityEvidence i t h) :
    Preference i t h (End_of i E.earlierAction t h)
      (End_of i E.laterAction t h) := by
  have hdominates :
      SubjectiveTeleologicalDominates W.requirement (W.ValuedEnd i t h)
        E.earlierBundle E.laterBundle := by
    refine ⟨E.storage_reproduces_valued_plans, ?_⟩
    refine ⟨{E.earlySecurityService}, ?_, ?_, ?_⟩
    · intro e he
      have heq : e = E.earlySecurityService := Finset.mem_singleton.mp he
      subst e
      exact E.security_is_valued
    · exact (jointly_attains_singleton W.requirement E.earlierBundle
        E.earlySecurityService).2 E.security_attainable_early
    · intro hattains
      apply E.security_unattainable_late
      exact (jointly_attains_singleton W.requirement E.laterBundle
        E.earlySecurityService).1 hattains
  rw [E.earlierAction_end, E.laterAction_end]
  exact W.teleological_bundle_dominance_induces_preference
    i t h E.earlierBundle E.laterBundle hdominates

/-- Evidence for a saving or insurance action whose executed outcome supplies
a valued current-security service. The fixed preference ranks it above the
forgone current-spending action. Preference asymmetry rules out that spending
action as a strict improvement; the remaining feasible alternatives are
checked explicitly for the same property. -/
structure CurrentSecurityChoiceEvidence (i : Agent) (t : Moment) (h : History) where
  savingAction : Action
  spendingAction : Action
  currentSecurity : Ends
  saving_feasible : savingAction ∈ A_feas i t h
  spending_feasible : spendingAction ∈ A_feas i t h
  saving_execution : @Exec W i t savingAction h
  savingSuccessor : Moment
  successor_is_immediate : IsNextMoment W.Precedence W.mem_hist
    t savingSuccessor h
  security_matures_at_successor :
    W.ExpectedMaturation i savingAction t h = savingSuccessor
  /-- This is actual delivery at the immediate successor. Valuation and the
  intended end are evaluated at the decision; the service need not already be
  in the pre-action inventory. -/
  security_outcome :
    W.OutcomeOf i savingAction t
      savingSuccessor h = currentSecurity
  security_is_valued : W.ValuedEnd i t h currentSecurity
  saving_end_is_security : End_of i savingAction t h = currentSecurity
  spending_end : Ends
  spending_action_end : End_of i spendingAction t h = spending_end
  security_preferred_to_forgone_spending :
    Preference i t h currentSecurity spending_end
  security_preferred_to_idle :
    Preference i t h currentSecurity (End_of i alpha_zero t h)
  /-- The feasible action set consists of the passive baseline, the spending
  action, and the security-providing saving action. -/
  feasible_menu_is_three : A_feas i t h = {alpha_zero, spendingAction, savingAction}

/-- Undominatedness over the non-spending menu alternatives is derived from the
three-action feasible menu, preference asymmetry, and irreflexivity. -/
theorem CurrentSecurityChoiceEvidence.saving_undominated_except_spending
    (E : CurrentSecurityChoiceEvidence i t h) (β : Action) (hβ : β ∈ A_feas i t h)
    (hne : β ≠ E.spendingAction) :
    ¬ Preference i t h (End_of i β t h) E.currentSecurity := by
  have hmenu := E.feasible_menu_is_three
  rw [hmenu] at hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl | rfl
  · intro hpref
    have hasymm := pref_asymm i t h E.security_preferred_to_idle
    exact hasymm hpref
  · exact (hne rfl).elim
  · rw [E.saving_end_is_security]
    exact pref_irrefl i t h E.currentSecurity

/-- Under the explicit execution, valuation, preference, and undominated-choice
evidence, the security-providing saving action is purposeful. -/
theorem current_security_choice_is_purposeful
    (E : CurrentSecurityChoiceEvidence i t h) :
    PurposefulAct i t h E.savingAction := by
  refine ⟨E.saving_feasible, ?_, ?_, ?_⟩
  · exact E.saving_execution
  · exact Or.inr (by rw [E.saving_end_is_security]; exact E.security_preferred_to_idle)
  · intro β hβ
    rw [E.saving_end_is_security]
    by_cases hspending : β = E.spendingAction
    · subst β
      rw [E.spending_action_end]
      exact pref_asymm i t h E.security_preferred_to_forgone_spending
    · exact E.saving_undominated_except_spending β hβ hspending

end DMU_TimePreference

section FiniteCurrentSecurityWitness

local instance W : ActionFrame := FiniteBranchingModel

/-- A concrete finite model witnesses the repaired current-security evidence.
The chosen consume action is executed on history one, while the defer action
is only a feasible forgone alternative. Security is evaluated at the decision
and delivered at the action's immediate successor. -/
def finiteCurrentSecurityChoiceEvidence :
    CurrentSecurityChoiceEvidence (W := FiniteBranchingModel)
      (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) := by
  refine
    { savingAction := ModelAction.consume
      spendingAction := ModelAction.defer
      currentSecurity := ModelEnd.timed (ModelEnd.quantity 1 1) 0
      saving_feasible := by decide
      spending_feasible := by decide
      saving_execution := by
        change ActionFrame.mem_hist (self := FiniteBranchingModel)
            (0 : Fin 4) (1 : Fin 3) ∧
          ActionFrame.enacted (self := FiniteBranchingModel)
            (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) = ModelAction.consume
        constructor
        · change branch_incidence (0 : Fin 4) (1 : Fin 3)
          exact Or.inl rfl
        · change (if (0 : Fin 2) = 0 ∧ (0 : Fin 4) = 0 then
            if (1 : Fin 3) = 0 then ModelAction.idle
            else if (1 : Fin 3) = 1 then ModelAction.consume
            else ModelAction.defer else ModelAction.idle) = ModelAction.consume
          decide
      savingSuccessor := (2 : Fin 4)
      successor_is_immediate := by
        change IsNextMoment finite_action_prec branch_incidence
          (0 : Fin 4) (2 : Fin 4) (1 : Fin 3)
        refine ⟨by simp [branch_incidence], by simp [branch_incidence],
          by simp [finite_action_prec], ?_⟩
        intro τ hτ hbetween
        rcases hτ with hroot | hleaf
        · subst τ
          simp [finite_action_prec] at hbetween
        · have hzero' : τ = (0 : Fin 4) := by
            exact hbetween.2.1
          rw [hzero'] at hleaf
          have : (0 : Fin 4).val = 2 := hleaf
          norm_num at this
      security_matures_at_successor := by decide
      security_outcome := by decide
      security_is_valued := by trivial
      saving_end_is_security := by rfl
      spending_end := ModelEnd.timed (ModelEnd.quantity 1 1) 1
      spending_action_end := by rfl
      security_preferred_to_forgone_spending := by
        change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 1) <
          end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
        decide
      security_preferred_to_idle := by
        change Preference (F := FiniteBranchingModel)
          (0 : Fin 2) (0 : Fin 4) (1 : Fin 3)
          (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
          (End_of (F := FiniteBranchingModel)
            (0 : Fin 2) ModelAction.idle (0 : Fin 4) (1 : Fin 3))
        change end_rank (ModelEnd.timed (ModelEnd.quantity 0 0) 0) <
          end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0)
        decide
      feasible_menu_is_three := by decide }

/-- The concrete current-security witness satisfies the one-purposefulness
predicate from actual feasibility, execution, intended improvement, and menu
undominatedness. -/
theorem finite_current_security_choice_is_purposeful :
    PurposefulAct (0 : Fin 2) (0 : Fin 4) (1 : Fin 3) ModelAction.consume :=
  current_security_choice_is_purposeful finiteCurrentSecurityChoiceEvidence

end FiniteCurrentSecurityWitness

section DMU_TimePreference

variable [W : ActionFrame] [IntertemporalEnds W]

/-- A feasible saving action whose end is strictly preferred to feasting
rules out purposeful feasting. -/
theorem saving_dominance_excludes_feasting
    (i : Agent) (t_aut : Moment) (h : History)
    (e_security e_feast : Ends)
    (h_security_over_feast : Preference i t_aut h
      (TimedEnd e_security t_aut) (TimedEnd e_feast t_aut))
    (α_save α_feast : Action)
    (h_save_feas : α_save ∈ A_feas i t_aut h)
    (h_save_end : End_of i α_save t_aut h = TimedEnd e_security t_aut)
    (h_feast_end : End_of i α_feast t_aut h = TimedEnd e_feast t_aut) :
    ¬ PurposefulAct i t_aut h α_feast := by
  intro h_purp
  have h_undom := h_purp.2.2.2 α_save h_save_feas
  rw [h_feast_end, h_save_end] at h_undom
  exact h_undom h_security_over_feast

/-- Conditional saving and exchange exclusions. The dated preferences are
premises, and the result rules out the specified dominated actions. It does
not establish universal time preference or a positive interest premium. -/
theorem saving_and_unit_exchange_rejected_under_dated_preferences
    (i : Agent) (t_aut t_win : Moment) (h : History)
    (e_security e_feast : Ends)
    (m : Means) (q : ℕ)
    (h_security_over_feast : Preference i t_aut h
      (TimedEnd e_security t_aut) (TimedEnd e_feast t_aut))
    (h_pos_tp_means : Preference i t_aut h
      (timedQuantityEnd m q t_aut) (timedQuantityEnd m q t_win))
    (α_save α_feast α_pres α_u4u : Action)
    (h_save_feas : α_save ∈ A_feas i t_aut h)
    (h_save_end : End_of i α_save t_aut h = TimedEnd e_security t_aut)
    (h_feast_end : End_of i α_feast t_aut h = TimedEnd e_feast t_aut)
    (h_pres_feas : α_pres ∈ A_feas i t_aut h)
    (h_pres_end : End_of i α_pres t_aut h = timedQuantityEnd m q t_aut)
    (h_u4u_end : End_of i α_u4u t_aut h = timedQuantityEnd m q t_win) :
    ¬ PurposefulAct i t_aut h α_feast ∧
    ¬ PurposefulAct i t_aut h α_u4u := by
  have h_res := saving_dominance_excludes_feasting i t_aut h
    e_security e_feast h_security_over_feast
    α_save α_feast h_save_feas h_save_end h_feast_end
  have h_u4u := purposeful_unit_for_unit_exchange_rejected
    i t_aut h m q t_aut t_win h_pos_tp_means α_pres α_u4u h_pres_feas h_pres_end h_u4u_end
  exact ⟨h_res, h_u4u⟩

end DMU_TimePreference


theorem finite_model_quantity_monotonicity
    (i : FiniteBranchingModel.Agent) (t : FiniteBranchingModel.Moment)
    (h : FiniteBranchingModel.History) (m : FiniteBranchingModel.Means)
    (q q' : ℕ) (τ : FiniteBranchingModel.Moment)
    (hq : q' < q) :
    @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel _ m q τ)
      (@timedQuantityEnd FiniteBranchingModel _ m q' τ) := by
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
      @CausalDoxasticOpenHorizon FiniteBranchingModel _ i t h
        (@QuantityEnd FiniteBranchingModel _ m q) α_cons τ1 ∧
      ¬ @IsPostHorizon FiniteBranchingModel i t h ∧
      (∃ (τ2 : FiniteBranchingModel.Moment) (δ : ℕ),
        0 < q ∧ @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 ∧ q < q' ∧ δ ≥ 1 ∧ q' = q + δ ∧
        @Preference FiniteBranchingModel i t h
          (@TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) τ1)
          (@TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) τ2) ∧
        @Preference FiniteBranchingModel i t h
          (@timedQuantityEnd FiniteBranchingModel _ m q τ1)
          (@timedQuantityEnd FiniteBranchingModel _ m q τ2)) := by
  let : ActionFrame := FiniteBranchingModel
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
    @End_of FiniteBranchingModel i α_cons t h =
      @timedQuantityEnd FiniteBranchingModel _ m q τ1 := rfl
  have h_causal_oeh :
    @CausalDoxasticOpenHorizon FiniteBranchingModel _ i t h
      (@QuantityEnd FiniteBranchingModel _ m q) α_cons τ1 := by
    intro _ _
    refine ⟨Or.inl rfl, ModelAction.defer, (1 : Fin 4), by decide,
      ⟨rfl, show (1 : Fin 4) ≠ 0 by decide⟩, rfl⟩
  have h_distinct : ∀ τ2 : Fin 4, @LT.lt FiniteBranchingModel.Moment _ τ1 τ2 →
      @TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) τ2 ≠
      @End_of FiniteBranchingModel i ModelAction.idle t h := by
    intro τ2 _ heq
    change ModelEnd.timed (ModelEnd.quantity 1 1) τ2 =
      ModelEnd.timed (ModelEnd.quantity 0 0) 0 at heq
    injection heq with hq _
    injection hq with _ hq'
    exact Nat.zero_ne_one hq'.symm
  have h_not_post :=
    @causal_doxastic_open_horizon_implies_not_post_horizon FiniteBranchingModel _ i t h
    (@QuantityEnd FiniteBranchingModel _ m q) α_cons τ1 h_causal_oeh (by decide) h_end h_distinct
  have h_timed_inj : ∀ t1 t2 : FiniteBranchingModel.Moment, t1 ≠ t2 →
      @TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) t1 ≠
      @TimedEnd FiniteBranchingModel _ (@QuantityEnd FiniteBranchingModel _ m q) t2 := by
    intro (t1 : Fin 4) (t2 : Fin 4) hne heq
    have : t1 = t2 := ModelEnd.timed.inj heq |>.2
    exact hne this
  obtain ⟨τ2, h_lt, h_pos_tp⟩ :=
    @strict_time_preference_from_distinct_end_dominance FiniteBranchingModel _ i t h
      (@QuantityEnd FiniteBranchingModel _ m q) α_cons τ1 h_end h_causal_oeh h_dom h_timed_inj
  have h_u4u : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel _ m q τ1)
      (@timedQuantityEnd FiniteBranchingModel _ m q τ2) :=
    h_pos_tp
  have h_accept : @Preference FiniteBranchingModel i t h
      (@timedQuantityEnd FiniteBranchingModel _ m q' τ2)
      (@timedQuantityEnd FiniteBranchingModel _ m q τ1) := by
    change end_rank (ModelEnd.timed (ModelEnd.quantity 1 1) 0) <
           end_rank (ModelEnd.timed (ModelEnd.quantity 1 2) τ2)
    dsimp [end_rank]
    split_ifs <;> omega
  have h_sync_mono : q' ≤ q →
      @Preference FiniteBranchingModel i t h (@timedQuantityEnd FiniteBranchingModel _ m q τ2)
        (@timedQuantityEnd FiniteBranchingModel _ m q' τ2) ∨
      @timedQuantityEnd FiniteBranchingModel _ m q τ2 =
        @timedQuantityEnd FiniteBranchingModel _ m q' τ2 := by
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
    @positive_originary_interest FiniteBranchingModel _ i t h m q q' Nat.zero_lt_one τ1 τ2
      h_pos_tp h_accept h_sync_mono h_trans
  exact ⟨i, t, h, m, q, q', α_cons, τ1, h_purp, h_dom, h_causal_oeh, h_not_post,
         ⟨τ2, δ, Nat.zero_lt_one, h_lt, hq_lt, hδ_ge, hq'_eq, h_pos_tp, h_u4u⟩⟩

end Praxeology

end
