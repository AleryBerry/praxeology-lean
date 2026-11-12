/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases


/-!
# Praxeological Frame: Foundational Ontological Structures

Foundational ontology of praxeology: time, causality, agents, ends, means, and action frames.
-/

open scoped BigOperators


@[expose] public section

namespace Praxeology


-- 1. ActionFrame


/-- `t'` immediately follows `t` on history `h`. -/
def IsNextMoment {Moment History : Type} (prec : Moment → Moment → Prop)
    (mem_hist : Moment → History → Prop) (t t' : Moment) (h : History) : Prop :=
  mem_hist t h ∧ mem_hist t' h ∧ prec t t' ∧
  ∀ τ, mem_hist τ h → ¬ (prec t τ ∧ prec τ t')

/-- A set of moments is a linear chain if all pairs of elements are comparable under precedence. -/
def IsLinearChain {Moment : Type} (prec : Moment → Moment → Prop) (s : Set Moment) : Prop :=
  ∀ ⦃t1 t2⦄, t1 ∈ s → t2 ∈ s → (prec t1 t2 ∨ t1 = t2 ∨ prec t2 t1)

/-- A set of moments is a maximal linear chain in (Moment, prec). -/
def IsMaximalLinearChain {Moment : Type} (prec : Moment → Moment → Prop) (s : Set Moment) : Prop :=
  IsLinearChain prec s ∧ ∀ s', IsLinearChain prec s' → s ⊆ s' → s' ⊆ s

/-- `b1` is at least as large in every coordinate and larger in one. -/
def PhysicalBundleDominates {Means : Type} (b1 b2 : Means → ℕ) : Prop :=
  (∀ m, b2 m ≤ b1 m) ∧ (∃ m, b2 m < b1 m)

/-- An end `e` is attainable under physical bundle `b` given requirement schedule `req`. -/
def AttainsEnd {Ends Means : Type} (req : Ends → Means → ℕ) (b : Means → ℕ) (e : Ends) : Prop :=
  ∀ m : Means, req e m ≤ b m

/-- A finite set of ends `S` is jointly attainable under physical bundle `b`
given requirement schedule `req`. -/
def JointlyAttains {Ends Means : Type} (req : Ends → Means → ℕ) (b : Means → ℕ)
    (S : Finset Ends) : Prop :=
  ∀ m : Means, (S.sum (fun e => req e m)) ≤ b m


def TeleologicalBundleDominates {Ends Means : Type} (req : Ends → Means → ℕ)
    (b1 b2 : Means → ℕ) : Prop :=
  (∀ S : Finset Ends, JointlyAttains req b2 S → JointlyAttains req b1 S) ∧
  (∃ S : Finset Ends, JointlyAttains req b1 S ∧ ¬ JointlyAttains req b2 S)

/-- Capital stock is usable only when its complementary factor reaches the
required threshold. -/
def complementaryEffectiveBundle {Means : Type} [DecidableEq Means]
    (m_cap m_comp : Means) (q_comp : ℕ) (b : Means → ℕ) (m : Means) : ℕ :=
  if m = m_cap then if b m_comp < q_comp then 0 else b m else b m

theorem complementaryEffectiveBundle_le {Means : Type} [DecidableEq Means]
    (m_cap m_comp : Means) (q_comp : ℕ) (b : Means → ℕ) (m : Means) :
    complementaryEffectiveBundle m_cap m_comp q_comp b m ≤ b m := by
  by_cases hm : m = m_cap
  · subst m
    dsimp [complementaryEffectiveBundle]
    split_ifs <;> omega
  · simp [complementaryEffectiveBundle, hm]

/-- A starved complementary factor strands positive capital stock. -/
theorem complementaryEffectiveBundle_physical_dominance
    {Means : Type} [DecidableEq Means]
    (m_cap m_comp : Means) (q_comp : ℕ) (b : Means → ℕ)
    (h_starved : b m_comp < q_comp) (h_capital : 0 < b m_cap) :
    PhysicalBundleDominates b
      (complementaryEffectiveBundle m_cap m_comp q_comp b) := by
  refine ⟨fun m => complementaryEffectiveBundle_le m_cap m_comp q_comp b m,
    ⟨m_cap, ?_⟩⟩
  simp [complementaryEffectiveBundle, h_starved, h_capital]

/-- Joint attainment is invariant when starved capital is removed, provided
every end requiring it also needs the complementary factor. -/
theorem jointly_attains_iff_complementaryEffectiveBundle
    {Ends Means : Type} [DecidableEq Means]
    (req : Ends → Means → ℕ) (m_cap m_comp : Means) (q_comp : ℕ)
    (b : Means → ℕ)
    (h_comp : ∀ e, 0 < req e m_cap → q_comp ≤ req e m_comp)
    (h_starved : b m_comp < q_comp) (S : Finset Ends) :
    JointlyAttains req b S ↔
      JointlyAttains req (complementaryEffectiveBundle m_cap m_comp q_comp b) S := by
  constructor
  · intro hS m
    by_cases hm : m = m_cap
    · subst m
      have hzeros : ∀ e ∈ S, req e m_cap = 0 := by
        intro e he
        by_contra hnot
        have hpos : 0 < req e m_cap := by omega
        have hreq := h_comp e hpos
        have hsingle : req e m_comp ≤ S.sum (fun x => req x m_comp) :=
          Finset.single_le_sum (f := fun x => req x m_comp)
            (fun _ _ => Nat.zero_le _) he
        have hbound := hS m_comp
        omega
      have hsum : S.sum (fun e => req e m_cap) = 0 :=
        Finset.sum_eq_zero hzeros
      simp [complementaryEffectiveBundle, h_starved, hsum]
    · simpa [complementaryEffectiveBundle, hm] using hS m
  · intro hS m
    exact le_trans (hS m)
      (complementaryEffectiveBundle_le m_cap m_comp q_comp b m)

/-- `b1` permits every valued end permitted by `b2` and at least one more. -/
def SubjectiveTeleologicalDominates {Ends Means : Type} [DecidableEq Ends]
    (req : Ends → Means → ℕ) (valued : Ends → Prop) (b1 b2 : Means → ℕ) : Prop :=
  (∀ S : Finset Ends, (∀ e ∈ S, valued e) →
    JointlyAttains req b2 S → JointlyAttains req b1 S) ∧
  (∃ S : Finset Ends, (∀ e ∈ S, valued e) ∧
    JointlyAttains req b1 S ∧ ¬ JointlyAttains req b2 S)

/-- If every end is valued, subjective dominance is equivalent to bundle dominance. -/
theorem subjective_teleological_dominates_iff_teleological_of_universal
    {Ends Means : Type} [DecidableEq Ends]
    (req : Ends → Means → ℕ) (valued : Ends → Prop)
    (hall : ∀ e, valued e) (b1 b2 : Means → ℕ) :
    SubjectiveTeleologicalDominates req valued b1 b2 ↔
      TeleologicalBundleDominates req b1 b2 := by
  constructor
  · rintro ⟨h_all, ⟨S, _, h1, h2⟩⟩
    exact ⟨fun S hS => h_all S (fun e _ => hall e) hS, ⟨S, h1, h2⟩⟩
  · rintro ⟨h_all, ⟨S, h1, h2⟩⟩
    exact ⟨fun S _ hS => h_all S hS, ⟨S, fun e _ => hall e, h1, h2⟩⟩

/-- When no end is valued, no physical stock strictly improves subjective appraisal. -/
theorem no_subjective_teleological_dominance_of_no_valued_ends
    {Ends Means : Type} [DecidableEq Ends]
    (req : Ends → Means → ℕ) (valued : Ends → Prop)
    (hnone : ∀ e, ¬ valued e) (b1 b2 : Means → ℕ) :
    ¬ SubjectiveTeleologicalDominates req valued b1 b2 := by
  rintro ⟨_, ⟨S, hS, _, hnot⟩⟩
  apply hnot
  intro m
  have hzero : S.sum (fun w => req w m) = 0 :=
    Finset.sum_eq_zero (fun e he => (hnone e (hS e he)).elim)
  simp [hzero]

/-- A unique valued end determines strict subjective bundle dominance when one
bundle attains it and the other does not. -/
theorem subjective_teleological_dominates_of_unique_valued_end
    {Ends Means : Type} [DecidableEq Ends]
    (req : Ends → Means → ℕ) (valued : Ends → Prop) (e : Ends)
    (b1 b2 : Means → ℕ)
    (h_unique : ∀ e', valued e' → e' = e)
    (h_valued : valued e)
    (h_attains : JointlyAttains req b1 {e})
    (h_misses : ¬ JointlyAttains req b2 {e}) :
    SubjectiveTeleologicalDominates req valued b1 b2 := by
  refine ⟨?_, ⟨{e}, ?_, h_attains, h_misses⟩⟩
  · intro S h_valued h_att m
    have h_sub : S ⊆ ({e} : Finset Ends) := by
      intro e' he'
      simp only [Finset.mem_singleton]
      exact h_unique e' (h_valued e' he')
    rcases Finset.subset_singleton_iff.mp h_sub with h_empty | h_single
    · subst S
      simp
    · subst S
      exact (h_misses h_att).elim
  · intro e' he'
    have heq : e' = e := Finset.mem_singleton.mp he'
    subst e'
    exact h_valued

/-- Teleological bundle dominance is irreflexive. -/
theorem teleological_bundle_dominates_irrefl {Ends Means : Type} (req : Ends → Means → ℕ)
    (b : Means → ℕ) :
    ¬ TeleologicalBundleDominates req b b := by
  intro ⟨_, ⟨S, hS1, hS2⟩⟩
  exact hS2 hS1

/-- Teleological bundle dominance is strictly asymmetric. -/
theorem teleological_bundle_dominates_asymm {Ends Means : Type} (req : Ends → Means → ℕ)
    (b1 b2 : Means → ℕ) :
    TeleologicalBundleDominates req b1 b2 → ¬ TeleologicalBundleDominates req b2 b1 := by
  intro ⟨_, ⟨S1, hS1_1, hS1_2⟩⟩ ⟨h_all2, _⟩
  exact hS1_2 (h_all2 S1 hS1_1)

/-- Teleological bundle dominance is transitive. -/
theorem teleological_bundle_dominates_trans {Ends Means : Type} (req : Ends → Means → ℕ)
    (b1 b2 b3 : Means → ℕ) :
    TeleologicalBundleDominates req b1 b2 → TeleologicalBundleDominates req b2 b3 →
    TeleologicalBundleDominates req b1 b3 := by
  intro ⟨h12_all, ⟨S1, hS1_1, hS1_2⟩⟩ ⟨h23_all, _⟩
  refine ⟨fun S hS => h12_all S (h23_all S hS), ⟨S1, hS1_1, ?_⟩⟩
  intro hS1_3
  exact hS1_2 (h23_all S1 hS1_3)

/-- Componentwise physical order preserves joint attainability. -/
theorem jointly_attains_le {Ends Means : Type} (req : Ends → Means → ℕ) (b1 b2 : Means → ℕ)
    (hle : ∀ m, b2 m ≤ b1 m) (S : Finset Ends) (hS : JointlyAttains req b2 S) :
    JointlyAttains req b1 S :=
  fun m => le_trans (hS m) (hle m)

/-- The empty set of ends is unconditionally attainable by any physical bundle. -/
theorem jointly_attains_empty {Ends Means : Type} (req : Ends → Means → ℕ) (b : Means → ℕ) :
    JointlyAttains req b ∅ := by
  intro m
  dsimp [JointlyAttains]
  simp

/-- Joint attainability of a singleton end-set `{e}` coincides with single-end attainability. -/
theorem jointly_attains_singleton {Ends Means : Type} (req : Ends → Means → ℕ)
    (b : Means → ℕ) (e : Ends) :
    JointlyAttains req b {e} ↔ AttainsEnd req b e := by
  dsimp [JointlyAttains, AttainsEnd]
  simp


theorem physical_bundle_dominance_implies_teleological_bundle_dominance_of_bundle_ends
    {Ends Means : Type} (req : Ends → Means → ℕ)
    (bundle_end : (Means → ℕ) → Ends)
    (h_req_bundle : ∀ b, req (bundle_end b) = b)
    (b1 b2 : Means → ℕ)
    (h_dom : PhysicalBundleDominates b1 b2) :
    TeleologicalBundleDominates req b1 b2 := by
  rcases h_dom with ⟨hle, ⟨m_star, hlt⟩⟩
  refine ⟨fun S hS m => le_trans (hS m) (hle m), ?_⟩
  refine ⟨{bundle_end b1}, ?_, ?_⟩
  · intro m
    simp [h_req_bundle]
  · intro h_att2
    have hm : b1 m_star ≤ b2 m_star := by
      have h := h_att2 m_star
      simpa [h_req_bundle] using h
    omega

/-- An end requiring one unit of `m_star` distinguishes these bundles. -/
theorem atomic_teleological_bundle_dominance_over_zero
    {Ends Means : Type} [DecidableEq Means] (req : Ends → Means → ℕ)
    (atomic_end : Means → Ends)
    (h_atomic : ∀ m m', req (atomic_end m) m' = if m' = m then 1 else 0)
    (b1 b2 : Means → ℕ)
    (hle : ∀ m, b2 m ≤ b1 m)
    (m_star : Means)
    (h_zero : b2 m_star = 0)
    (h_pos : 1 ≤ b1 m_star) :
    TeleologicalBundleDominates req b1 b2 := by
  refine ⟨fun S hS m => le_trans (hS m) (hle m), ⟨{atomic_end m_star}, ?_, ?_⟩⟩
  · intro m
    simp only [Finset.sum_singleton, h_atomic]
    split_ifs with h_eq
    · subst h_eq; exact h_pos
    · exact Nat.zero_le _
  · intro h_att2
    have hm : 1 ≤ b2 m_star := by
      have h := h_att2 m_star
      simpa only [Finset.sum_singleton, h_atomic, ite_true] using h
    omega


class ActionFrame where
  Agent : Type
  [instNonemptyAgent : Nonempty Agent]
  [instFintypeAgent : Fintype Agent]
  [instDecidableEqAgent : DecidableEq Agent]
  Moment : Type
  [instDecidableEqMoment : DecidableEq Moment]
  History : Type
  [instDecidableEqHistory : DecidableEq History]
  Action : Type
  [instNonemptyAction : Nonempty Action]
  [instDecidableEqAction : DecidableEq Action]
  Means : Type
  [instFintypeMeans : Fintype Means]
  [instDecidableEqMeans : DecidableEq Means]
  Ends : Type
  [instDecidableEqEnds : DecidableEq Ends]
  /-- Baseline action `alpha_zero`. -/
  alpha_zero : Action

  /-- Strict temporal precedence (<) on Moment. -/
  Precedence : Moment → Moment → Prop
  moment_lt_irrefl : ∀ t : Moment, ¬ Precedence t t
  moment_lt_trans : ∀ {t1 t2 t3 : Moment}, Precedence t1 t2 → Precedence t2 t3 → Precedence t1 t3
  /-- Moments preceding the same moment are comparable. -/
  backward_linearity : ∀ {t1 t2 t3 : Moment}, Precedence t1 t3 → Precedence t2 t3 →
    Precedence t1 t2 ∨ t1 = t2 ∨ Precedence t2 t1

  /-- Whether moment `t` lies on history `h`. -/
  mem_hist : Moment → History → Prop
  /-- Every moment belongs to at least one history branch. -/
  moment_in_history : ∀ t : Moment, ∃ h : History, mem_hist t h
  /-- Each history is a maximal linear chain of moments. -/
  histories_maximal_linear : ∀ h : History,
    IsMaximalLinearChain Precedence { t : Moment | mem_hist t h }
  /-- Histories with the same moments are equal. -/
  histories_extensional : ∀ h1 h2 : History,
    (∀ t : Moment, mem_hist t h1 ↔ mem_hist t h2) → h1 = h2



  divergent_futures_witness : ∀ {t : Moment} (h1 h2 : History),
    mem_hist t h1 → mem_hist t h2 → h1 ≠ h2 →
    ∃ u v : Moment,
      mem_hist u h1 ∧ mem_hist v h2 ∧
      Precedence t u ∧ Precedence t v ∧
      ¬ Precedence u v ∧ u ≠ v ∧ ¬ Precedence v u

  /-- Contemplated actions for agent `i` at `⟨t, h⟩`. -/
  A_cont : Agent → Moment → History → Finset Action
  /-- Contemplated actions agree across histories through `t`. -/
  A_cont_bundle_invariant : ∀ i t {h1 h2 : History}, mem_hist t h1 → mem_hist t h2 →
    A_cont i t h1 = A_cont i t h2
  /-- The baseline action is always contemplated. -/
  alpha_zero_cont : ∀ i t h, alpha_zero ∈ A_cont i t h

  /-- Physical endowment. -/
  omega : Agent → Moment → History → Means → ℕ
  /-- Endowment agrees across histories through `t`. -/
  omega_bundle_invariant : ∀ i t m {h1 h2 : History}, mem_hist t h1 → mem_hist t h2 →
    omega i t h1 m = omega i t h2 m
  /-- Means used by each action. -/
  use_means : Action → Means → ℕ
  /-- Means yielded by each action. -/
  yield_means : Action → Means → ℕ
  /-- The baseline action uses no means. -/
  use_means_alpha_zero : ∀ m, use_means alpha_zero m = 0
  /-- The baseline action yields no means. -/
  yield_means_alpha_zero : ∀ m, yield_means alpha_zero m = 0
  /-- Feasible actions for agent `i` at `⟨t, h⟩`. -/
  A_feas : Agent → Moment → History → Finset Action :=
    fun i t h => (A_cont i t h).filter (fun α => ∀ m, use_means α m ≤ omega i t h m)
  /-- Feasible actions are contemplated and meet the means requirements. -/
  A_feas_coupling : ∀ i t h α,
    α ∈ A_feas i t h ↔ α ∈ A_cont i t h ∧ ∀ m, use_means α m ≤ omega i t h m := by
    intro i t h α
    simp only [Finset.mem_filter]

  /-- Action enacted by agent `i` at `⟨t, h⟩`. -/
  enacted : Agent → Moment → History → Action
  /-- Enacted actions are feasible at moments on the history. -/
  enacted_in_A_feas : ∀ i t h, mem_hist t h → enacted i t h ∈ A_feas i t h
  /-- Histories sharing a later moment have the same action at `t`. -/
  no_choice_between_undivided : ∀ i t u h1 h2,
    mem_hist t h1 → mem_hist t h2 → Precedence t u →
    mem_hist u h1 → mem_hist u h2 → enacted i t h1 = enacted i t h2




  sigma : Agent → Moment → Action → History → History
  /-- Each feasible action is enacted on a history through `t`. -/
  sigma_realization : ∀ i t h h' {α : Action},
    mem_hist t h → α ∈ A_feas i t h → mem_hist t h' →
    mem_hist t (sigma i t α h') ∧ enacted i t (sigma i t α h') = α
  /-- Branch selection preserves a history that already enacts `α`. -/
  sigma_centering : ∀ i t h' {α : Action},
    mem_hist t h' → enacted i t h' = α → sigma i t α h' = h'
  /-- Branch selection preserves other agents' actions at `t`. -/
  sigma_co_agency : ∀ i j t h h' {α : Action},
    i ≠ j → mem_hist t h → α ∈ A_feas i t h → mem_hist t h' →
    enacted j t (sigma i t α h') = enacted j t h'

  /-- Predicate characterizing bilateral exchange actions (Offer / Accept).
      Defaults to False in autarkic / nontrading models. -/
  IsTradeAction : Action → Prop := fun _ => False
  alpha_zero_not_trade : ¬ IsTradeAction alpha_zero := by
    intro h
    exact h

  /-- Predicate characterizing whether an action physically seizes from or invades
      target agent `i`. Defaults to False in peaceful / purely catallactic models. -/
  IsInvasiveOn : Action → Agent → Prop := fun _ _ => False
  alpha_zero_not_invasive : ∀ i, ¬ IsInvasiveOn alpha_zero i := by
    intro _ h
    exact h

  /-- Endowment changes by action use and yield for nontrade actions when agent `i`
      is uninvaded by all other agents. -/
  law_in_re_transition : ∀ i t t' h α m,
    ¬ IsTradeAction α →
    (∀ j, ¬ IsInvasiveOn (enacted j t h) i) →
    enacted i t h = α →
    IsNextMoment Precedence mem_hist t t' h →
    omega i t' h m + use_means α m = omega i t h m + yield_means α m

  /-- Plausible histories for agent `i` at moment `t`. -/
  MinPlausible : Agent → Moment → Set History
  /-- The minimal plausibility set is non-empty. -/
  min_plausible_nonempty : ∀ i t, (MinPlausible i t).Nonempty




  tau : Agent → Moment → History → Moment := fun _ t _ => t

  /-- Each plausible history contains its projected moment. -/
  min_plausible_node_incidence : ∀ i t, ∀ h' ∈ MinPlausible i t, mem_hist (tau i t h') h'

  /-- The projected node is `t` on histories that contain `t`. -/
  tau_centering : ∀ i t h, mem_hist t h → tau i t h = t := by
    intros; rfl

  /-- Means required by each end. -/
  requirement : Ends → Means → ℕ
  /-- Ends valued by each agent at a decision node. -/
  ValuedEnd : Agent → Moment → History → Ends → Prop
  /-- Valuation of each end agrees across histories through `t`. -/
  valued_end_bundle_invariant : ∀ i t {h1 h2 : History} e,
    mem_hist t h1 → mem_hist t h2 →
    (ValuedEnd i t h1 e ↔ ValuedEnd i t h2 e)

  /-- Outcome of action `α` at maturation moment `τ` on history `h`. -/
  OutcomeOf : Agent → Action → Moment → Moment → History → Ends
  /-- Expected maturation moment for action `α` on history `h`. -/
  ExpectedMaturation : Agent → Action → Moment → History → Moment
  /-- Maturation lies on the history at `t` or after `t`. -/
  expected_maturation_mem_future : ∀ i α t h,
    mem_hist t h → enacted i t h = α →
    mem_hist (ExpectedMaturation i α t h) h ∧
    (t = ExpectedMaturation i α t h ∨ Precedence t (ExpectedMaturation i α t h))

  /-- Intended end of action `α` at `⟨t, h⟩`. -/
  End_of : Agent → Action → Moment → History → Ends
  /-- Intended ends agree across histories through `t`. -/
  End_of_bundle_invariant : ∀ i α t {h1 h2 : History}, mem_hist t h1 → mem_hist t h2 →
    End_of i α t h1 = End_of i α t h2

  /-- Preference relation over ends. -/
  Preference : Agent → Moment → History → Ends → Ends → Prop
  /-- Preferences agree across histories through `t`. -/
  Preference_bundle_invariant : ∀ i t {h1 h2 : History}, mem_hist t h1 → mem_hist t h2 →
    Preference i t h1 = Preference i t h2
  /-- Preference is asymmetric. -/
  pref_asymm : ∀ i t h {e1 e2 : Ends}, Preference i t h e1 e2 → ¬ Preference i t h e2 e1




  /-- Appraisal assumption: the stated outcome comparisons imply the
  intended-end preference. This is a frame premise. -/
  doxastic_sure_thing_bridge : ∀ i α β t h,
    (∀ h' ∈ MinPlausible i t,
      α ∈ A_feas i (tau i t h') h' ∧ β ∈ A_feas i (tau i t h') h') →
    (∀ h' ∈ MinPlausible i t,
      let t' := tau i t h'
      OutcomeOf i α t' (ExpectedMaturation i α t' (sigma i t' α h')) (sigma i t' α h') =
      OutcomeOf i β t' (ExpectedMaturation i β t' (sigma i t' β h')) (sigma i t' β h') ∨
      Preference i t h
        (OutcomeOf i α t' (ExpectedMaturation i α t' (sigma i t' α h')) (sigma i t' α h'))
        (OutcomeOf i β t' (ExpectedMaturation i β t' (sigma i t' β h')) (sigma i t' β h'))) →
    (∃ h' ∈ MinPlausible i t,
      let t' := tau i t h'
      Preference i t h
        (OutcomeOf i α t' (ExpectedMaturation i α t' (sigma i t' α h')) (sigma i t' α h'))
        (OutcomeOf i β t' (ExpectedMaturation i β t' (sigma i t' β h')) (sigma i t' β h'))) →
    Preference i t h (End_of i α t h) (End_of i β t h)




  /-- Appraisal assumption: an intended-end preference has support on at
  least one plausible history when both actions are appraisable. -/
  doxastic_plausible_support : ∀ i α β t h,
    (∀ h' ∈ MinPlausible i t,
      α ∈ A_feas i (tau i t h') h' ∧ β ∈ A_feas i (tau i t h') h') →
    Preference i t h (End_of i α t h) (End_of i β t h) →
    ∃ h' ∈ MinPlausible i t,
      let t' := tau i t h'
      Preference i t h
        (OutcomeOf i α t' (ExpectedMaturation i α t' (sigma i t' α h')) (sigma i t' α h'))
        (OutcomeOf i β t' (ExpectedMaturation i β t' (sigma i t' β h')) (sigma i t' β h'))

  /-- Representation of a physical commodity bundle as an end. -/
  BundleEnd : (Means → ℕ) → Ends
  /-- Appraisal assumption: dominance over valued ends induces preference
  between bundle ends. It is not derived from preference asymmetry. -/
  teleological_bundle_dominance_induces_preference : ∀ i t h b1 b2,
    SubjectiveTeleologicalDominates requirement (ValuedEnd i t h) b1 b2 →
      Preference i t h (BundleEnd b1) (BundleEnd b2)

instance (W : ActionFrame) : DecidableEq W.Agent := W.instDecidableEqAgent
instance (W : ActionFrame) : DecidableEq W.Action := W.instDecidableEqAction
instance (W : ActionFrame) : DecidableEq W.Means := W.instDecidableEqMeans
instance (W : ActionFrame) : DecidableEq W.Ends := W.instDecidableEqEnds
instance (W : ActionFrame) : Fintype W.Agent := W.instFintypeAgent
instance (W : ActionFrame) : Fintype W.Means := W.instFintypeMeans

/-- Optional bilateral exchange structure for ActionFrames supporting voluntary market trade. -/
class BilateralExchangeFrame (W : ActionFrame) where
  Offer : W.Agent → W.Agent → ℕ → W.Means → ℕ → W.Means → W.Action
  Accept : W.Agent → W.Agent → ℕ → W.Means → ℕ → W.Means → W.Action
  use_means_offer : ∀ i j qA mA qB mB m,
    W.use_means (Offer i j qA mA qB mB) m = (if m = mA then qA else 0)
  yield_means_offer : ∀ i j qA mA qB mB m,
    W.yield_means (Offer i j qA mA qB mB) m = (if m = mB then qB else 0)
  use_means_accept : ∀ j i qA mA qB mB m,
    W.use_means (Accept j i qA mA qB mB) m = (if m = mB then qB else 0)
  yield_means_accept : ∀ j i qA mA qB mB m,
    W.yield_means (Accept j i qA mA qB mB) m = (if m = mA then qA else 0)
  offer_inj : ∀ {i1 j1 qA1 mA1 qB1 mB1 i2 j2 qA2 mA2 qB2 mB2},
    Offer i1 j1 qA1 mA1 qB1 mB1 = Offer i2 j2 qA2 mA2 qB2 mB2 →
    i1 = i2 ∧ j1 = j2 ∧ qA1 = qA2 ∧ mA1 = mA2 ∧ qB1 = qB2 ∧ mB1 = mB2
  accept_inj : ∀ {j1 i1 qA1 mA1 qB1 mB1 j2 i2 qA2 mA2 qB2 mB2},
    Accept j1 i1 qA1 mA1 qB1 mB1 = Accept j2 i2 qA2 mA2 qB2 mB2 →
    j1 = j2 ∧ i1 = i2 ∧ qA1 = qA2 ∧ mA1 = mA2 ∧ qB1 = qB2 ∧ mB1 = mB2
  offer_ne_accept : ∀ {i j qA mA qB mB j' i' qA' mA' qB' mB'},
    Offer i j qA mA qB mB ≠ Accept j' i' qA' mA' qB' mB'
  alpha_zero_ne_offer : ∀ {i j qA mA qB mB}, W.alpha_zero ≠ Offer i j qA mA qB mB
  alpha_zero_ne_accept : ∀ {j i qA mA qB mB}, W.alpha_zero ≠ Accept j i qA mA qB mB
  unilateral_offer_noop : ∀ i j qA mA qB mB t t' h m,
    W.enacted i t h = Offer i j qA mA qB mB →
    W.enacted j t h ≠ Accept j i qA mA qB mB →
    IsNextMoment W.Precedence W.mem_hist t t' h →
    W.omega i t' h m = W.omega i t h m
  unilateral_accept_noop : ∀ j i qA mA qB mB t t' h m,
    W.enacted j t h = Accept j i qA mA qB mB →
    W.enacted i t h ≠ Offer i j qA mA qB mB →
    IsNextMoment W.Precedence W.mem_hist t t' h →
    W.omega j t' h m = W.omega j t h m
  bilateral_transfer_law : ∀ i j qA mA qB mB t t' h m,
    i ≠ j →
    W.enacted i t h = Offer i j qA mA qB mB →
    W.enacted j t h = Accept j i qA mA qB mB →
    IsNextMoment W.Precedence W.mem_hist t t' h →
    (W.omega i t' h m + (if m = mA then qA else 0) =
      W.omega i t h m + (if m = mB then qB else 0)) ∧
    (W.omega j t' h m + (if m = mB then qB else 0) =
      W.omega j t h m + (if m = mA then qA else 0))
  is_trade_action_def : ∀ α, W.IsTradeAction α ↔
    (∃ i j qA mA qB mB, α = Offer i j qA mA qB mB) ∨
    (∃ j i qA mA qB mB, α = Accept j i qA mA qB mB)

@[reducible]
def ActionFrame.Offer (W : ActionFrame) [B : BilateralExchangeFrame W] :
    W.Agent → W.Agent → ℕ → W.Means → ℕ → W.Means → W.Action :=
  B.Offer

@[reducible]
def ActionFrame.Accept (W : ActionFrame) [B : BilateralExchangeFrame W] :
    W.Agent → W.Agent → ℕ → W.Means → ℕ → W.Means → W.Action :=
  B.Accept

theorem ActionFrame.use_means_offer (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ i j qA mA qB mB m,
      W.use_means (W.Offer i j qA mA qB mB) m = (if m = mA then qA else 0) :=
  B.use_means_offer

theorem ActionFrame.yield_means_offer (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ i j qA mA qB mB m,
      W.yield_means (W.Offer i j qA mA qB mB) m = (if m = mB then qB else 0) :=
  B.yield_means_offer

theorem ActionFrame.use_means_accept (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ j i qA mA qB mB m,
      W.use_means (W.Accept j i qA mA qB mB) m = (if m = mB then qB else 0) :=
  B.use_means_accept

theorem ActionFrame.yield_means_accept (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ j i qA mA qB mB m,
      W.yield_means (W.Accept j i qA mA qB mB) m = (if m = mA then qA else 0) :=
  B.yield_means_accept

theorem ActionFrame.offer_inj (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ {i1 j1 qA1 mA1 qB1 mB1 i2 j2 qA2 mA2 qB2 mB2},
      W.Offer i1 j1 qA1 mA1 qB1 mB1 = W.Offer i2 j2 qA2 mA2 qB2 mB2 →
      i1 = i2 ∧ j1 = j2 ∧ qA1 = qA2 ∧ mA1 = mA2 ∧ qB1 = qB2 ∧ mB1 = mB2 :=
  B.offer_inj

theorem ActionFrame.accept_inj (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ {j1 i1 qA1 mA1 qB1 mB1 j2 i2 qA2 mA2 qB2 mB2},
      W.Accept j1 i1 qA1 mA1 qB1 mB1 = W.Accept j2 i2 qA2 mA2 qB2 mB2 →
      j1 = j2 ∧ i1 = i2 ∧ qA1 = qA2 ∧ mA1 = mA2 ∧ qB1 = qB2 ∧ mB1 = mB2 :=
  B.accept_inj

theorem ActionFrame.offer_ne_accept (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ {i j qA mA qB mB j' i' qA' mA' qB' mB'},
      W.Offer i j qA mA qB mB ≠ W.Accept j' i' qA' mA' qB' mB' :=
  B.offer_ne_accept

theorem ActionFrame.alpha_zero_ne_offer (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ {i j qA mA qB mB}, W.alpha_zero ≠ W.Offer i j qA mA qB mB :=
  B.alpha_zero_ne_offer

theorem ActionFrame.alpha_zero_ne_accept (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ {j i qA mA qB mB}, W.alpha_zero ≠ W.Accept j i qA mA qB mB :=
  B.alpha_zero_ne_accept

theorem ActionFrame.unilateral_offer_noop (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ i j qA mA qB mB t t' h m,
      W.enacted i t h = W.Offer i j qA mA qB mB →
      W.enacted j t h ≠ W.Accept j i qA mA qB mB →
      IsNextMoment W.Precedence W.mem_hist t t' h →
      W.omega i t' h m = W.omega i t h m :=
  B.unilateral_offer_noop

theorem ActionFrame.unilateral_accept_noop (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ j i qA mA qB mB t t' h m,
      W.enacted j t h = W.Accept j i qA mA qB mB →
      W.enacted i t h ≠ W.Offer i j qA mA qB mB →
      IsNextMoment W.Precedence W.mem_hist t t' h →
      W.omega j t' h m = W.omega j t h m :=
  B.unilateral_accept_noop

theorem ActionFrame.bilateral_transfer_law (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ i j qA mA qB mB t t' h m,
      i ≠ j →
      W.enacted i t h = W.Offer i j qA mA qB mB →
      W.enacted j t h = W.Accept j i qA mA qB mB →
      IsNextMoment W.Precedence W.mem_hist t t' h →
      (W.omega i t' h m + (if m = mA then qA else 0) =
        W.omega i t h m + (if m = mB then qB else 0)) ∧
      (W.omega j t' h m + (if m = mB then qB else 0) =
        W.omega j t h m + (if m = mA then qA else 0)) :=
  B.bilateral_transfer_law

theorem ActionFrame.is_trade_action_def (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ∀ α, W.IsTradeAction α ↔
      (∃ i j qA mA qB mB, α = W.Offer i j qA mA qB mB) ∨
      (∃ j i qA mA qB mB, α = W.Accept j i qA mA qB mB) :=
  B.is_trade_action_def

theorem BilateralExchangeFrame.alpha_zero_not_trade
    (W : ActionFrame) [B : BilateralExchangeFrame W] :
    ¬ W.IsTradeAction W.alpha_zero := by
  intro h_tr
  rw [B.is_trade_action_def] at h_tr
  rcases h_tr with ⟨i, j, qA, mA, qB, mB, h_eq⟩ | ⟨j, i, qA, mA, qB, mB, h_eq⟩
  · exact B.alpha_zero_ne_offer h_eq
  · exact B.alpha_zero_ne_accept h_eq

/-- Optional coercive transfer structure for ActionFrames supporting unilateral physical seizure. -/
class CoerciveTransferFrame (W : ActionFrame) where
  Seize : W.Agent → W.Agent → ℕ → W.Means → W.Action
  seize_not_trade : ∀ j i q m, ¬ W.IsTradeAction (Seize j i q m)
  seize_invasive_iff : ∀ j i q m k,
    W.IsInvasiveOn (Seize j i q m) k ↔ (k = i ∧ j ≠ i ∧ 0 < q)
  seize_transfer_law : ∀ j i q m t t' h m',
    j ≠ i →
    q ≤ W.omega i t h m →
    W.enacted j t h = Seize j i q m →
    W.enacted i t h = W.alpha_zero →
    (∀ k, k ≠ j → k ≠ i →
      ¬ W.IsInvasiveOn (W.enacted k t h) i ∧ ¬ W.IsInvasiveOn (W.enacted k t h) j) →
    IsNextMoment W.Precedence W.mem_hist t t' h →
    (W.omega j t' h m' = W.omega j t h m' + (if m' = m then q else 0)) ∧
    (W.omega i t' h m' + (if m' = m then q else 0) = W.omega i t h m')

@[reducible]
def ActionFrame.Seize (W : ActionFrame) [C : CoerciveTransferFrame W] :
    W.Agent → W.Agent → ℕ → W.Means → W.Action :=
  C.Seize

theorem ActionFrame.seize_not_trade (W : ActionFrame) [C : CoerciveTransferFrame W] :
    ∀ j i q m, ¬ W.IsTradeAction (W.Seize j i q m) :=
  C.seize_not_trade

theorem ActionFrame.seize_invasive_iff (W : ActionFrame) [C : CoerciveTransferFrame W] :
    ∀ j i q m k, W.IsInvasiveOn (W.Seize j i q m) k ↔ (k = i ∧ j ≠ i ∧ 0 < q) :=
  C.seize_invasive_iff

/-- Optional intertemporal composite ends for models formalizing time preference
    and originary interest. -/
class IntertemporalEnds (W : ActionFrame) where
  /-- Temporally indexed end ⟨e, τ⟩ representing realization of end `e` at moment `τ`. -/
  TimedEnd : W.Ends → W.Moment → W.Ends
  /-- Untimed end of holding/consuming `q` discrete units of means `m`. -/
  QuantityEnd : W.Means → ℕ → W.Ends
  /-- Injectivity of TimedEnd. -/
  timed_end_inj : ∀ {e1 τ1 e2 τ2}, TimedEnd e1 τ1 = TimedEnd e2 τ2 → e1 = e2 ∧ τ1 = τ2
  /-- Injectivity of QuantityEnd. -/
  quantity_end_inj : ∀ {m1 q1 m2 q2}, QuantityEnd m1 q1 = QuantityEnd m2 q2 → m1 = m2 ∧ q1 = q2

@[reducible]
def ActionFrame.TimedEnd (W : ActionFrame) [E : IntertemporalEnds W] :
    W.Ends → W.Moment → W.Ends :=
  E.TimedEnd

@[reducible]
def ActionFrame.QuantityEnd (W : ActionFrame) [E : IntertemporalEnds W] :
    W.Means → ℕ → W.Ends :=
  E.QuantityEnd

theorem ActionFrame.timed_end_inj (W : ActionFrame) [E : IntertemporalEnds W] :
    ∀ {e1 τ1 e2 τ2}, W.TimedEnd e1 τ1 = W.TimedEnd e2 τ2 → e1 = e2 ∧ τ1 = τ2 :=
  E.timed_end_inj

theorem ActionFrame.quantity_end_inj (W : ActionFrame) [E : IntertemporalEnds W] :
    ∀ {m1 q1 m2 q2}, W.QuantityEnd m1 q1 = W.QuantityEnd m2 q2 → m1 = m2 ∧ q1 = q2 :=
  E.quantity_end_inj

/-- The passive baseline `α₀` is always feasible. -/
theorem ActionFrame.alpha_zero_feasible (W : ActionFrame) (i : W.Agent)
    (t : W.Moment) (h : W.History) :
    W.alpha_zero ∈ W.A_feas i t h := by
  rw [W.A_feas_coupling]
  refine ⟨W.alpha_zero_cont i t h, fun m => ?_⟩
  rw [W.use_means_alpha_zero m]
  exact Nat.zero_le _


theorem ActionFrame.A_feas_bundle_invariant (W : ActionFrame) (i : W.Agent) (t : W.Moment)
    {h1 h2 : W.History} (h1_in : W.mem_hist t h1) (h2_in : W.mem_hist t h2) :
    W.A_feas i t h1 = W.A_feas i t h2 := by
  ext α
  rw [W.A_feas_coupling, W.A_feas_coupling,
      W.A_cont_bundle_invariant i t h1_in h2_in]
  simp only [W.omega_bundle_invariant i t _ h1_in h2_in]

/-- Proposition 2.13: Inaction preserves endowments across temporal transitions when uninvaded. -/
theorem ActionFrame.inaction_preserves_endowments (W : ActionFrame)
    (i : W.Agent) (t t' : W.Moment) (h : W.History)
    (h_enacted : W.enacted i t h = W.alpha_zero)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    ∀ m, W.omega i t' h m = W.omega i t h m := by
  intro m
  have h_tr := W.law_in_re_transition i t t' h W.alpha_zero m
    W.alpha_zero_not_trade h_uninvaded h_enacted h_next
  rw [W.use_means_alpha_zero m, W.yield_means_alpha_zero m,
      Nat.add_zero, Nat.add_zero] at h_tr
  exact h_tr

/-- Proposition 2.14 (Part 1): Pure production reflects yield in ending inventory when uninvaded. -/
theorem ActionFrame.pure_production_yield_only (W : ActionFrame)
    (i : W.Agent) (t t' : W.Moment) (h : W.History) (α : W.Action) (m : W.Means)
    (h_not_trade : ¬ W.IsTradeAction α)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_use : W.use_means α m = 0)
    (h_enacted : W.enacted i t h = α)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.omega i t' h m = W.omega i t h m + W.yield_means α m := by
  have h_tr := W.law_in_re_transition i t t' h α m h_not_trade h_uninvaded h_enacted h_next
  rw [h_use, Nat.add_zero] at h_tr
  exact h_tr

/-- Proposition 2.14 (Part 2):
Pure consumption reflects use in ending inventory balance when uninvaded. -/
theorem ActionFrame.pure_consumption_use_only (W : ActionFrame)
    (i : W.Agent) (t t' : W.Moment) (h : W.History) (α : W.Action) (m : W.Means)
    (h_not_trade : ¬ W.IsTradeAction α)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_yield : W.yield_means α m = 0)
    (h_enacted : W.enacted i t h = α)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    W.omega i t' h m + W.use_means α m = W.omega i t h m := by
  have h_tr := W.law_in_re_transition i t t' h α m h_not_trade h_uninvaded h_enacted h_next
  rw [h_yield, Nat.add_zero] at h_tr
  exact h_tr

/-- Every maximal history contains the full past of each of its moments. -/
theorem ActionFrame.past_mem_of_mem (W : ActionFrame) (h : W.History)
    (s t : W.Moment) (ht : W.mem_hist t h) (hst : W.Precedence s t) : W.mem_hist s h := by
  let S : Set W.Moment := {x | W.mem_hist x h ∨ x = s}
  have hlinear := (W.histories_maximal_linear h).1
  have hcompare (x : W.Moment) (hx : W.mem_hist x h) :
      W.Precedence s x ∨ s = x ∨ W.Precedence x s := by
    rcases hlinear hx ht with hxt | heq | htx
    · exact W.backward_linearity hst hxt
    · subst x
      exact Or.inl hst
    · exact Or.inl (W.moment_lt_trans hst htx)
  have hSlinear : IsLinearChain W.Precedence S := by
    intro x y hx hy
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · exact hlinear hx hy
    · rcases hcompare x hx with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
    · exact hcompare y hy
    · exact Or.inr (Or.inl rfl)
  have hsub : {x : W.Moment | W.mem_hist x h} ⊆ S := fun _ hx => Or.inl hx
  have hmax := (W.histories_maximal_linear h).2 S hSlinear hsub
  exact hmax (Or.inr rfl)

/-- Distinct histories through a moment have incompatible future moments. -/
theorem ActionFrame.distinct_histories_have_incompatible_futures (W : ActionFrame)
    (t : W.Moment) (h1 h2 : W.History)
    (ht1 : W.mem_hist t h1) (ht2 : W.mem_hist t h2) (hne : h1 ≠ h2) :
    ∃ u v : W.Moment,
      W.mem_hist u h1 ∧ W.mem_hist v h2 ∧
      W.Precedence t u ∧ W.Precedence t v ∧
      ¬ W.Precedence u v ∧ u ≠ v ∧ ¬ W.Precedence v u := by
  exact W.divergent_futures_witness (t := t) h1 h2 ht1 ht2 hne


/-- Single-end attainability under bundle `b` in the given `ActionFrame`. -/
def ActionFrame.AttainsEnd (W : ActionFrame) (b : W.Means → ℕ) (e : W.Ends) : Prop :=
  Praxeology.AttainsEnd W.requirement b e

/-- Joint attainability of a finite set of ends `S` under bundle `b` in the given `ActionFrame`. -/
def ActionFrame.JointlyAttains (W : ActionFrame) (b : W.Means → ℕ) (S : Finset W.Ends) : Prop :=
  Praxeology.JointlyAttains W.requirement b S

/-- Teleological bundle dominance in the given `ActionFrame`. -/
def ActionFrame.TeleologicalBundleDominates (W : ActionFrame) (b1 b2 : W.Means → ℕ) : Prop :=
  Praxeology.TeleologicalBundleDominates W.requirement b1 b2

/-- Agent- and node-specific dominance over valued ends. -/
def ActionFrame.SubjectiveTeleologicalDominates (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (b1 b2 : W.Means → ℕ) : Prop :=
  @Praxeology.SubjectiveTeleologicalDominates W.Ends W.Means W.instDecidableEqEnds
    W.requirement (W.ValuedEnd i t h) b1 b2

def ActionFrame.MaturationEnd (W : ActionFrame) (i : W.Agent) (α : W.Action)
    (t : W.Moment) (h' : W.History) : W.Ends :=
  let t' := W.tau i t h'
  W.OutcomeOf i α t' (W.ExpectedMaturation i α t' (W.sigma i t' α h')) (W.sigma i t' α h')

/-- A valid decision node is a moment-history pair incident on that history. -/
abbrev ActionFrame.DecisionIndex (W : ActionFrame) :=
  {p : W.Moment × W.History // W.mem_hist p.1 p.2}

def ActionFrame.decisionIndex (W : ActionFrame) (t : W.Moment) (h : W.History)
    (ht : W.mem_hist t h) : W.DecisionIndex :=
  ⟨(t, h), ht⟩

def ActionFrame.DecisionIndex.moment (W : ActionFrame) (x : W.DecisionIndex) : W.Moment :=
  x.1.1

def ActionFrame.DecisionIndex.history (W : ActionFrame) (x : W.DecisionIndex) : W.History :=
  x.1.2

/-- Decision indices for distinct moments on one history are distinct. -/
theorem ActionFrame.decision_indices_differ_at_different_moments (W : ActionFrame)
    (t₁ t₂ : W.Moment) (h : W.History)
    (ht₁ : W.mem_hist t₁ h) (ht₂ : W.mem_hist t₂ h) (hne : t₁ ≠ t₂) :
    W.decisionIndex t₁ h ht₁ ≠ W.decisionIndex t₂ h ht₂ := by
  intro heq
  have hm := congrArg (fun x : W.DecisionIndex => x.1.1) heq
  exact hne hm

/-- The valid plausible decision node associated with a history in the
agent's minimal plausibility set. -/
def ActionFrame.projectedDecisionIndex (W : ActionFrame) (i : W.Agent)
    (t : W.Moment) (h' : W.History) (hh' : h' ∈ W.MinPlausible i t) :
    W.DecisionIndex :=
  W.decisionIndex (W.tau i t h') h'
    (W.min_plausible_node_incidence i t h' hh')

/-- One correspondence describes outcomes under circumstances held fixed.
Admissibility is anchored at a valid decision index and need not be restricted
to the agent's plausible histories. -/
structure ActionFrame.ContextCorrespondence (W : ActionFrame) (Context : Type) where
  compatible : W.Agent → W.Moment → W.History → Context → Prop
  context_nonempty : ∀ i (x : W.DecisionIndex),
    ∃ c, compatible i x.moment x.history c
  admissible : W.Agent → W.DecisionIndex → Context → W.Action →
    W.History → W.Moment → Prop
  admissible_sound : ∀ i (x : W.DecisionIndex) c α hOut τ,
    admissible i x c α hOut τ →
      compatible i x.moment x.history c ∧
      compatible i x.moment hOut c ∧
      W.mem_hist x.moment hOut ∧
      W.enacted i x.moment hOut = α ∧
      (∀ j, j ≠ i →
        W.enacted j x.moment hOut = W.enacted j x.moment x.history) ∧
      W.mem_hist τ hOut ∧
      (x.moment = τ ∨ W.Precedence x.moment τ)
  admissible_nonempty : ∀ i (x : W.DecisionIndex) c α,
    compatible i x.moment x.history c →
    α ∈ W.A_feas i x.moment x.history →
    ∃ hOut τ, admissible i x c α hOut τ
  admissible_centering : ∀ i (x : W.DecisionIndex) c,
    compatible i x.moment x.history c →
    ∃ τ, admissible i x c (W.enacted i x.moment x.history) x.history τ

namespace ActionFrame.ContextCorrespondence

variable {W : ActionFrame} {Context : Type}

/-- Ends available for an action under one compatible context. -/
def Outcomes (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action) : Set W.Ends :=
  {e | ∃ hOut τ, C.admissible i x c α hOut τ ∧
    e = W.OutcomeOf i α x.moment τ hOut}

/-- Every feasible action has an admitted outcome in a compatible context. -/
theorem outcomes_nonempty (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action)
    (hc : C.compatible i x.moment x.history c)
    (hα : α ∈ W.A_feas i x.moment x.history) :
    (C.Outcomes i x c α).Nonempty := by
  obtain ⟨hOut, τ, hadm⟩ := C.admissible_nonempty i x c α hc hα
  exact ⟨W.OutcomeOf i α x.moment τ hOut, hOut, τ, hadm, rfl⟩

/-- An admissible history agrees with the anchor's physical endowment at the
decision moment. This follows from shared moment incidence and the frame's
history invariance law. -/
theorem admissible_preserves_anchor_endowment
    (C : W.ContextCorrespondence Context)
    (i j : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action)
    (hOut : W.History) (τ : W.Moment)
    (hadm : C.admissible i x c α hOut τ) (m : W.Means) :
    W.omega j x.moment hOut m = W.omega j x.moment x.history m := by
  have hs := C.admissible_sound i x c α hOut τ hadm
  exact W.omega_bundle_invariant j x.moment m hs.2.2.1 x.2

/-- The outcome selected by the frame's existing sigma and maturation fields. -/
def SelectedOutcome (W : ActionFrame) (i : W.Agent) (x : W.DecisionIndex)
    (α : W.Action) : W.Ends :=
  W.OutcomeOf i α x.moment
    (W.ExpectedMaturation i α x.moment (W.sigma i x.moment α x.history))
    (W.sigma i x.moment α x.history)

/-- A correspondence admits the frame's selected realization. -/
def SelectorAdmissible (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action) : Prop :=
  C.admissible i x c α (W.sigma i x.moment α x.history)
    (W.ExpectedMaturation i α x.moment (W.sigma i x.moment α x.history))

/-- All admitted outcomes coincide. This is weaker than requiring the selector
itself to represent them. -/
def OutcomesUnique (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action) : Prop :=
  ∀ e₁ ∈ C.Outcomes i x c α, ∀ e₂ ∈ C.Outcomes i x c α, e₁ = e₂

/-- Every admitted outcome is represented by the frame's selected outcome. -/
def SelectorRepresentsOutcomes (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex) (c : Context) (α : W.Action) : Prop :=
  ∀ e ∈ C.Outcomes i x c α, e = ActionFrame.ContextCorrespondence.SelectedOutcome W i x α

end ActionFrame.ContextCorrespondence

/-- The frame's selector gives a deterministic correspondence for the unique
unit context. -/
def ActionFrame.deterministicCorrespondence (W : ActionFrame) :
    W.ContextCorrespondence Unit where
  compatible := fun _ _ _ _ => True
  context_nonempty := by intro _ _; exact ⟨(), trivial⟩
  admissible := fun i x _ α hOut τ =>
    α ∈ W.A_feas i x.moment x.history ∧
    hOut = W.sigma i x.moment α x.history ∧
    τ = W.ExpectedMaturation i α x.moment (W.sigma i x.moment α x.history)
  admissible_sound := by
    intro i x c α hOut τ hadm
    rcases hadm with ⟨hα, rfl, rfl⟩
    have hreal := W.sigma_realization i x.moment x.history x.history
      x.2 hα x.2
    have hmat := W.expected_maturation_mem_future i α x.moment
      (W.sigma i x.moment α x.history) hreal.1 hreal.2
    refine ⟨trivial, trivial, hreal.1, hreal.2, ?_, hmat.1, hmat.2⟩
    intro j hne
    exact W.sigma_co_agency i j x.moment x.history x.history
      (Ne.symm hne) x.2 hα x.2
  admissible_nonempty := by
    intro i x c α _ hα
    exact ⟨W.sigma i x.moment α x.history,
      W.ExpectedMaturation i α x.moment (W.sigma i x.moment α x.history),
      hα, rfl, rfl⟩
  admissible_centering := by
    intro i x c _
    have hα := W.enacted_in_A_feas i x.moment x.history x.2
    have hsigma := W.sigma_centering i x.moment x.history x.2 rfl
    refine ⟨W.ExpectedMaturation i (W.enacted i x.moment x.history) x.moment x.history,
      hα, hsigma.symm, ?_⟩
    simp [hsigma]

/-- In the deterministic correspondence, the sole outcome is the selected
maturation outcome. -/
theorem ActionFrame.deterministicCorrespondence_outcomes_eq (W : ActionFrame)
    (i : W.Agent) (x : W.DecisionIndex) (α : W.Action)
    (hα : α ∈ W.A_feas i x.moment x.history) :
    W.deterministicCorrespondence.Outcomes i x () α =
      {ActionFrame.ContextCorrespondence.SelectedOutcome W i x α} := by
  ext e
  constructor
  · rintro ⟨hOut, τ, hadm, he⟩
    rcases hadm with ⟨_, rfl, rfl⟩
    simpa [ActionFrame.ContextCorrespondence.SelectedOutcome] using he
  · intro he
    have heq := Set.mem_singleton_iff.mp he
    subst e
    exact ⟨W.sigma i x.moment α x.history,
      W.ExpectedMaturation i α x.moment (W.sigma i x.moment α x.history),
      ⟨hα, rfl, rfl⟩, rfl⟩

/-- Every action feasible at the actual node remains feasible at all projected
plausible nodes, when this frame-level invariance condition holds. -/
def ActionFrame.ProjectedFeasibility (W : ActionFrame) : Prop :=
  ∀ i t h h' α, W.mem_hist t h → h' ∈ W.MinPlausible i t →
    α ∈ W.A_feas i t h → α ∈ W.A_feas i (W.tau i t h') h'

/-- Feasibility of an action at every projected plausible history. -/
def ActionFrame.ProjectedAppraisable (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (α : W.Action) : Prop :=
  ∀ h' ∈ W.MinPlausible i t, α ∈ W.A_feas i (W.tau i t h') h'

/-- Actions preferred at every history in `P`. -/
def ActionFrame.UnanimousDominates (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History)
    (α β : W.Action) : Prop :=
  ∀ h' ∈ P, W.Preference i t h (W.MaturationEnd i α t h')
    (W.MaturationEnd i β t h')

/-- Weak Pareto comparison over projected outcomes. -/
def ActionFrame.WeakParetoDominates (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History)
    (α β : W.Action) : Prop :=
  (∀ h' ∈ P, W.MaturationEnd i α t h' = W.MaturationEnd i β t h' ∨
    W.Preference i t h (W.MaturationEnd i α t h') (W.MaturationEnd i β t h')) ∧
  (∃ h' ∈ P, W.Preference i t h (W.MaturationEnd i α t h')
    (W.MaturationEnd i β t h'))

/-- Sure-thing dominance rules out reverse preference everywhere and requires
strict preference on at least one history. -/
def ActionFrame.SureThingDominates (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History)
    (α β : W.Action) : Prop :=
  (∀ h' ∈ P, ¬ W.Preference i t h (W.MaturationEnd i β t h')
    (W.MaturationEnd i α t h')) ∧
  (∃ h' ∈ P, W.Preference i t h (W.MaturationEnd i α t h')
    (W.MaturationEnd i β t h'))

/-- Preference for one action over another at some history in `P`. -/
def ActionFrame.PlausibleSupport (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History)
    (α β : W.Action) : Prop :=
  ∃ h' ∈ P, W.Preference i t h (W.MaturationEnd i α t h')
    (W.MaturationEnd i β t h')

/-- The frame's selector enacts a feasible action at its selected history. -/
theorem ActionFrame.projected_sigma_enacted (W : ActionFrame) (i : W.Agent)
    (t : W.Moment) (h' : W.History) (α : W.Action)
    (hh' : h' ∈ W.MinPlausible i t)
    (hα : α ∈ W.A_feas i (W.tau i t h') h') :
    W.mem_hist (W.tau i t h') (W.sigma i (W.tau i t h') α h') ∧
      W.enacted i (W.tau i t h') (W.sigma i (W.tau i t h') α h') = α := by
  have ht' := W.min_plausible_node_incidence i t h' hh'
  exact W.sigma_realization i (W.tau i t h') h' h' ht' hα ht'

/-- Minimal plausible histories satisfying an observed event. -/
def ActionFrame.DELUpdate (W : ActionFrame) (i : W.Agent) (t : W.Moment)
    (ε : W.History → Prop) : Set W.History :=
  {h' ∈ W.MinPlausible i t | ε h'}

/-- Preference at `⟨t, h⟩` implies dominance on all plausible histories. -/
def ActionFrame.IsUnanimousAppraisal (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) : Prop :=
  ∀ α β, W.ProjectedAppraisable i t α → W.ProjectedAppraisable i t β →
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) →
    W.UnanimousDominates i t h (W.MinPlausible i t) α β

/-- Preference at `⟨t, h⟩` implies `WeakParetoDominates` on plausible histories. -/
def ActionFrame.IsSureThingAppraisal (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) : Prop :=
  ∀ α β, W.ProjectedAppraisable i t α → W.ProjectedAppraisable i t β →
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) →
    W.WeakParetoDominates i t h (W.MinPlausible i t) α β

theorem ActionFrame.sure_thing_dominates_irrefl (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History) (α : W.Action) :
    ¬ W.SureThingDominates i t h P α α := by
  intro ⟨h_all, ⟨h', hh', h_pref⟩⟩
  exact h_all h' hh' h_pref

theorem ActionFrame.sure_thing_dominates_asymm (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History) (α β : W.Action) :
    W.SureThingDominates i t h P α β → ¬ W.SureThingDominates i t h P β α := by
  intro ⟨_, ⟨h_wit, hh_wit, h_pref⟩⟩ ⟨h_all2, _⟩
  exact h_all2 h_wit hh_wit h_pref

theorem ActionFrame.weak_pareto_implies_sure_thing (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History) (α β : W.Action) :
    W.WeakParetoDominates i t h P α β → W.SureThingDominates i t h P α β := by
  intro ⟨h_all, h_ex⟩
  refine ⟨?_, h_ex⟩
  intro h' hh' h_pref_rev
  cases h_all h' hh' with
  | inl h_eq =>
    rw [h_eq] at h_pref_rev
    exact W.pref_asymm i t h h_pref_rev h_pref_rev
  | inr h_pref =>
    exact W.pref_asymm i t h h_pref h_pref_rev

theorem ActionFrame.unanimous_implies_weak_pareto (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History) (α β : W.Action)
    (hP : P.Nonempty) (h_unan : W.UnanimousDominates i t h P α β) :
    W.WeakParetoDominates i t h P α β := by
  obtain ⟨h0, hh0⟩ := hP
  refine ⟨fun h' hh' => Or.inr (h_unan h' hh'), ⟨h0, hh0, h_unan h0 hh0⟩⟩

theorem ActionFrame.unanimous_implies_sure_thing (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (P : Set W.History) (α β : W.Action)
    (hP : P.Nonempty) (h_unan : W.UnanimousDominates i t h P α β) :
    W.SureThingDominates i t h P α β :=
  ActionFrame.weak_pareto_implies_sure_thing W i t h P α β
    (ActionFrame.unanimous_implies_weak_pareto W i t h P α β hP h_unan)

theorem ActionFrame.doxastic_weak_pareto_bridge (W : ActionFrame)
    (i : W.Agent) (α β : W.Action) (t : W.Moment) (h : W.History)
    (h_app : W.ProjectedAppraisable i t α ∧ W.ProjectedAppraisable i t β)
    (h_wp : W.WeakParetoDominates i t h (W.MinPlausible i t) α β) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) :=
  W.doxastic_sure_thing_bridge i α β t h (by
    intro h' hh'
    exact ⟨h_app.1 h' hh', h_app.2 h' hh'⟩) h_wp.1 h_wp.2

theorem ActionFrame.doxastic_unanimous_bridge (W : ActionFrame)
    (i : W.Agent) (α β : W.Action) (t : W.Moment) (h : W.History)
    (h_app : W.ProjectedAppraisable i t α ∧ W.ProjectedAppraisable i t β)
    (h_unan : W.UnanimousDominates i t h (W.MinPlausible i t) α β) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) := by
  have h_wp :=
    ActionFrame.unanimous_implies_weak_pareto W i t h (W.MinPlausible i t) α β
      (W.min_plausible_nonempty i t) h_unan
  exact ActionFrame.doxastic_weak_pareto_bridge W i α β t h h_app h_wp

theorem ActionFrame.is_unanimous_appraisal_of_singleton (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h h_pl : W.History)
    (h_sing : W.MinPlausible i t = {h_pl}) :
    W.IsUnanimousAppraisal i t h := by
  intro α β h_app_α' h_app_β' h_pref h' hh'
  rw [h_sing, Set.mem_singleton_iff] at hh'
  subst hh'
  obtain ⟨h_wit, hh_wit, h_wit_pref⟩ := W.doxastic_plausible_support i α β t h
    (by intro h' hh'; exact ⟨h_app_α' h' hh', h_app_β' h' hh'⟩) h_pref
  rw [h_sing, Set.mem_singleton_iff] at hh_wit
  subst hh_wit
  exact h_wit_pref

theorem ActionFrame.is_sure_thing_appraisal_of_singleton (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h h_pl : W.History)
    (h_sing : W.MinPlausible i t = {h_pl}) :
    W.IsSureThingAppraisal i t h := by
  intro α β h_app_α' h_app_β' h_pref
  have h_unan := ActionFrame.is_unanimous_appraisal_of_singleton W i t h h_pl h_sing
    α β h_app_α' h_app_β' h_pref
  have h_nonempty : (W.MinPlausible i t).Nonempty :=
    ⟨h_pl, by rw [h_sing]; exact Set.mem_singleton h_pl⟩
  exact ActionFrame.unanimous_implies_weak_pareto W i t h (W.MinPlausible i t) α β h_nonempty h_unan

theorem ActionFrame.doxastic_teleological_bridge_singleton (W : ActionFrame)
    (i : W.Agent) (α β : W.Action) (t : W.Moment) (h h_pl : W.History)
    (h_app : W.ProjectedAppraisable i t α ∧ W.ProjectedAppraisable i t β)
    (h_sing : W.MinPlausible i t = {h_pl}) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) ↔
      ∀ h' ∈ W.MinPlausible i t,
        W.Preference i t h (W.MaturationEnd i α t h') (W.MaturationEnd i β t h') := by
  constructor
  · intro h_pref
    exact ActionFrame.is_unanimous_appraisal_of_singleton W i t h h_pl h_sing
      α β h_app.1 h_app.2 h_pref
  · intro h_all
    exact ActionFrame.doxastic_unanimous_bridge W i α β t h h_app h_all

/-- Physical endowment at `⟨τ, h⟩` represented as an end. -/
def ActionFrame.physical_outcome (W : ActionFrame) (i : W.Agent)
    (τ : W.Moment) (h : W.History) : W.Ends :=
  W.BundleEnd (W.omega i τ h)


def ActionFrame.OutcomesGroundedInEndowments (W : ActionFrame) : Prop :=
  ∀ i α t τ h, W.OutcomeOf i α t τ h = W.BundleEnd (W.omega i τ h)

/-- Whether one agent's outcomes equal its endowment bundle. -/
def ActionFrame.OutcomesGroundedInEndowmentsFor (W : ActionFrame) (i : W.Agent) : Prop :=
  ∀ α t τ h, W.OutcomeOf i α t τ h = W.BundleEnd (W.omega i τ h)

/-- The outcome equals the physical endowment bundle at `⟨τ, h⟩`. -/
def ActionFrame.IsPhysicallyGroundedAt (W : ActionFrame) (i : W.Agent)
    (α : W.Action) (t τ : W.Moment) (h : W.History) : Prop :=
  W.OutcomeOf i α t τ h = W.physical_outcome i τ h


theorem ActionFrame.teleological_dominance_induces_preference (W : ActionFrame)
    (i : W.Agent) (α β : W.Action) (t : W.Moment) (h : W.History)
    (h_app : W.ProjectedAppraisable i t α ∧ W.ProjectedAppraisable i t β)
    (h_ground_α : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.IsPhysicallyGroundedAt i α t'
        (W.ExpectedMaturation i α t' (W.sigma i t' α h')) (W.sigma i t' α h'))
    (h_ground_β : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.IsPhysicallyGroundedAt i β t'
        (W.ExpectedMaturation i β t' (W.sigma i t' β h')) (W.sigma i t' β h'))
    (h_dom_all : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.SubjectiveTeleologicalDominates i t h
        (W.omega i (W.ExpectedMaturation i α t' (W.sigma i t' α h')) (W.sigma i t' α h'))
        (W.omega i (W.ExpectedMaturation i β t' (W.sigma i t' β h')) (W.sigma i t' β h'))) :
    W.Preference i t h (W.End_of i α t h) (W.End_of i β t h) := by
  have h_unanimous : W.UnanimousDominates i t h (W.MinPlausible i t) α β := by
    intro h' hh'
    let t' := W.tau i t h'
    have h_stock_pref := W.teleological_bundle_dominance_induces_preference i t h
      (W.omega i (W.ExpectedMaturation i α t' (W.sigma i t' α h'))
        (W.sigma i t' α h'))
      (W.omega i (W.ExpectedMaturation i β t' (W.sigma i t' β h'))
        (W.sigma i t' β h'))
      (h_dom_all h' hh')
    have h_ground_a := h_ground_α h' hh'
    have h_ground_b := h_ground_β h' hh'
    change W.OutcomeOf i α t' (W.ExpectedMaturation i α t' (W.sigma i t' α h'))
        (W.sigma i t' α h') =
      W.BundleEnd (W.omega i (W.ExpectedMaturation i α t' (W.sigma i t' α h'))
        (W.sigma i t' α h')) at h_ground_a
    change W.OutcomeOf i β t' (W.ExpectedMaturation i β t' (W.sigma i t' β h'))
        (W.sigma i t' β h') =
      W.BundleEnd (W.omega i (W.ExpectedMaturation i β t' (W.sigma i t' β h'))
        (W.sigma i t' β h')) at h_ground_b
    change W.Preference i t h
      (W.OutcomeOf i α t' (W.ExpectedMaturation i α t' (W.sigma i t' α h'))
        (W.sigma i t' α h'))
      (W.OutcomeOf i β t' (W.ExpectedMaturation i β t' (W.sigma i t' β h'))
        (W.sigma i t' β h'))
    rw [h_ground_a, h_ground_b]
    exact h_stock_pref
  exact W.doxastic_unanimous_bridge i α β t h h_app h_unanimous

/-- ActionFrame preference is irreflexive. -/
theorem ActionFrame.pref_irrefl (W : ActionFrame) (i : W.Agent)
    (t : W.Moment) (h : W.History) (e : W.Ends) :
    ¬ W.Preference i t h e e :=
  fun h_pref => W.pref_asymm i t h h_pref h_pref


theorem ActionFrame.instantaneous_maturation_outcome_eq_of_endowments (W : ActionFrame)
    (i : W.Agent) (α : W.Action) (t : W.Moment) (h' : W.History)
    (h_pl : h' ∈ W.MinPlausible i t)
    (h_mat_α : W.ExpectedMaturation i α (W.tau i t h')
      (W.sigma i (W.tau i t h') α h') = W.tau i t h')
    (h_mat_α0 : W.ExpectedMaturation i W.alpha_zero (W.tau i t h')
      (W.sigma i (W.tau i t h') W.alpha_zero h') = W.tau i t h')
    (h_feas_α : α ∈ W.A_feas i (W.tau i t h') h')
    (h_ground : W.OutcomesGroundedInEndowments) :
    W.MaturationEnd i α t h' = W.MaturationEnd i W.alpha_zero t h' := by
  let t' := W.tau i t h'
  have ht' : W.mem_hist t' h' := W.min_plausible_node_incidence i t h' h_pl
  have h_α0_feas : W.alpha_zero ∈ W.A_feas i t' h' := W.alpha_zero_feasible i t' h'
  have hσα : W.mem_hist t' (W.sigma i t' α h') :=
    (W.sigma_realization i t' h' h' ht' h_feas_α ht').1
  have hσα0 : W.mem_hist t' (W.sigma i t' W.alpha_zero h') :=
    (W.sigma_realization i t' h' h' ht' h_α0_feas ht').1
  dsimp [ActionFrame.MaturationEnd]
  rw [h_mat_α, h_mat_α0]
  rw [h_ground i α t' t' (W.sigma i t' α h')]
  rw [h_ground i W.alpha_zero t' t' (W.sigma i t' W.alpha_zero h')]
  congr 1
  ext m
  rw [W.omega_bundle_invariant i t' m hσα ht']
  rw [W.omega_bundle_invariant i t' m hσα0 ht']


theorem ActionFrame.instantaneous_maturation_sterility_of_endowments (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action)
    (h_feas_all : ∀ h' ∈ W.MinPlausible i t, α ∈ W.A_feas i (W.tau i t h') h')
    (h_mat_all : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.ExpectedMaturation i α t' (W.sigma i t' α h') = t' ∧
      W.ExpectedMaturation i W.alpha_zero t' (W.sigma i t' W.alpha_zero h') = t')
    (h_ground : W.OutcomesGroundedInEndowments) :
    ¬ W.Preference i t h (W.End_of i α t h) (W.End_of i W.alpha_zero t h) := by
  intro h_pref
  obtain ⟨h', hh', h_pref_mat⟩ := W.doxastic_plausible_support i α W.alpha_zero t h
    (fun h' hh' => ⟨h_feas_all h' hh', W.alpha_zero_feasible i (W.tau i t h') h'⟩)
    h_pref
  have h_equal := W.instantaneous_maturation_outcome_eq_of_endowments i α t h' hh'
    (h_mat_all h' hh').1 (h_mat_all h' hh').2 (h_feas_all h' hh') h_ground
  change W.MaturationEnd i α t h' = W.MaturationEnd i W.alpha_zero t h' at h_equal
  dsimp only [ActionFrame.MaturationEnd] at h_equal h_pref_mat
  rw [h_equal] at h_pref_mat
  exact W.pref_irrefl i t h _ h_pref_mat

theorem ActionFrame.active_purposeful_act_requires_strict_future_maturation_of_endowments
    (W : ActionFrame)
    (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action)
    (h_feas_all : ∀ h' ∈ W.MinPlausible i t, α ∈ W.A_feas i (W.tau i t h') h')
    (h_act : W.Preference i t h (W.End_of i α t h) (W.End_of i W.alpha_zero t h))
    (h_ground : W.OutcomesGroundedInEndowments) :
    ∃ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.Precedence t' (W.ExpectedMaturation i α t' (W.sigma i t' α h')) ∨
      W.Precedence t' (W.ExpectedMaturation i W.alpha_zero t' (W.sigma i t' W.alpha_zero h')) := by
  by_contra h_none
  have h_not_prec : ∀ h' ∈ W.MinPlausible i t,
      ¬ (W.Precedence (W.tau i t h')
            (W.ExpectedMaturation i α (W.tau i t h') (W.sigma i (W.tau i t h') α h')) ∨
         W.Precedence (W.tau i t h')
            (W.ExpectedMaturation i W.alpha_zero (W.tau i t h')
              (W.sigma i (W.tau i t h') W.alpha_zero h'))) := by
    intro h' hh' h_or
    exact h_none ⟨h', hh', h_or⟩
  have h_all_instant : ∀ h' ∈ W.MinPlausible i t,
      let t' := W.tau i t h'
      W.ExpectedMaturation i α t' (W.sigma i t' α h') = t' ∧
      W.ExpectedMaturation i W.alpha_zero t' (W.sigma i t' W.alpha_zero h') = t' := by
    intro h' hh'
    have ht' := W.min_plausible_node_incidence i t h' hh'
    have h_α_feas := h_feas_all h' hh'
    have h_α0_feas := W.alpha_zero_feasible i (W.tau i t h') h'
    have h_sig_α := W.sigma_realization i (W.tau i t h') h' h' ht' h_α_feas ht'
    have h_sig_α0 := W.sigma_realization i (W.tau i t h') h' h' ht' h_α0_feas ht'
    obtain ⟨_, h_mat_or_α⟩ := W.expected_maturation_mem_future i α (W.tau i t h')
      (W.sigma i (W.tau i t h') α h') h_sig_α.1 h_sig_α.2
    obtain ⟨_, h_mat_or_α0⟩ := W.expected_maturation_mem_future i W.alpha_zero (W.tau i t h')
      (W.sigma i (W.tau i t h') W.alpha_zero h') h_sig_α0.1 h_sig_α0.2
    have h_np := h_not_prec h' hh'
    cases h_mat_or_α with
    | inl h_eq =>
      cases h_mat_or_α0 with
      | inl h_eq0 => exact ⟨h_eq.symm, h_eq0.symm⟩
      | inr h_prec0 => exact False.elim (h_np (Or.inr h_prec0))
    | inr h_prec => exact False.elim (h_np (Or.inl h_prec))
  exact W.instantaneous_maturation_sterility_of_endowments i t h α
    h_feas_all h_all_instant h_ground h_act

/-- A reflexive, transitive, and total relation on histories. -/
structure PlausibilityPreorder (History : Type) where
  le : History → History → Prop
  refl : ∀ h, le h h
  trans : ∀ {h1 h2 h3}, le h1 h2 → le h2 h3 → le h1 h3
  total : ∀ h1 h2, le h1 h2 ∨ le h2 h1

/-- Histories in `S` related by `P.le` to every history in `S`. -/
def MinimalPlausibleStratum {History : Type} (P : PlausibilityPreorder History)
    (S : Set History) : Set History :=
  { h ∈ S | ∀ h' ∈ S, P.le h h' }

/-- Return an element of `x :: xs` related by `P.le` to every element in the list. -/
def listMinPlausible {History : Type} (P : PlausibilityPreorder History) [DecidableRel P.le] :
    History → List History → History
  | x, [] => x
  | x, y :: rest =>
    let m := listMinPlausible P y rest
    if P.le x m then x else m

/-- The result belongs to the list and is related by `P.le` to every list element. -/
theorem listMinPlausible_mem_and_le {History : Type} (P : PlausibilityPreorder History)
    [DecidableRel P.le]
    (x : History) (xs : List History) :
    listMinPlausible P x xs ∈ x :: xs ∧ ∀ y ∈ x :: xs, P.le (listMinPlausible P x xs) y := by
  induction xs generalizing x with
  | nil =>
    dsimp [listMinPlausible]
    refine ⟨by simp, ?_⟩
    intro y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact P.refl x
  | cons y rest ih =>
    dsimp [listMinPlausible]
    have ⟨hm_in, hm_le⟩ := ih y
    split_ifs with hle
    · refine ⟨by simp, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with heq | hz
      · rw [heq]; exact P.refl x
      · exact P.trans hle (hm_le z (List.mem_cons.mpr hz))
    · have h_m_le_x : P.le (listMinPlausible P y rest) x := by
        rcases P.total x (listMinPlausible P y rest) with h1 | h2
        · exact (hle h1).elim
        · exact h2
      refine ⟨by simp [hm_in], ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with heq | hz
      · rw [heq]; exact h_m_le_x
      · exact hm_le z (List.mem_cons.mpr hz)

/-- A finite non-empty set of histories has a non-empty minimal stratum. -/
theorem minimal_plausible_stratum_nonempty {History : Type} [Finite History]
    (P : PlausibilityPreorder History) (S : Set History) (hS : S.Nonempty) :
    (MinimalPlausibleStratum P S).Nonempty := by
  cases nonempty_fintype History
  classical
  rcases hS with ⟨x, hx⟩
  let s_fin : Finset History := Finset.univ.filter (fun h => h ∈ S)
  let rest := (s_fin.erase x).toList
  have ⟨hm_in, hm_le⟩ := listMinPlausible_mem_and_le P x rest
  have hm_s_fin : listMinPlausible P x rest ∈ s_fin := by
    simp only [List.mem_cons] at hm_in
    rcases hm_in with heq | hm_rest
    · rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    · have := Finset.mem_toList.mp hm_rest
      exact Finset.mem_of_mem_erase this
  have hm_S : listMinPlausible P x rest ∈ S := (Finset.mem_filter.mp hm_s_fin).2
  refine ⟨listMinPlausible P x rest, hm_S, ?_⟩
  intro h' hh'
  have hh'_fin : h' ∈ s_fin := Finset.mem_filter.mpr ⟨Finset.mem_univ h', hh'⟩
  have hh'_in_cons : h' ∈ x :: rest := by
    by_cases h_eq : h' = x
    · subst h_eq; exact List.Mem.head _
    · right
      apply Finset.mem_toList.mpr
      exact Finset.mem_erase.mpr ⟨h_eq, hh'_fin⟩
  exact hm_le h' hh'_in_cons


def LexicographicUpgrade {History : Type} (P : PlausibilityPreorder History) (ψ : Set History) :
    PlausibilityPreorder History where
  le h1 h2 := (h1 ∈ ψ ∧ h2 ∉ ψ) ∨ ((h1 ∈ ψ ↔ h2 ∈ ψ) ∧ P.le h1 h2)
  refl := by
    intro h
    right
    exact ⟨Iff.rfl, P.refl h⟩
  trans := by
    intro h1 h2 h3 h12 h23
    rcases h12 with ⟨h1ψ, h2not⟩ | ⟨h12iff, h12le⟩
    · rcases h23 with ⟨h2ψ, h3not⟩ | ⟨h23iff, _⟩
      · exact (h2not h2ψ).elim
      · left
        have h3not : h3 ∉ ψ := by intro h3ψ; exact h2not (h23iff.mpr h3ψ)
        exact ⟨h1ψ, h3not⟩
    · rcases h23 with ⟨h2ψ, h3not⟩ | ⟨h23iff, h23le⟩
      · left
        have h1ψ : h1 ∈ ψ := h12iff.mpr h2ψ
        exact ⟨h1ψ, h3not⟩
      · right
        exact ⟨h12iff.trans h23iff, P.trans h12le h23le⟩
  total := by
    intro h1 h2
    let _ : Decidable (h1 ∈ ψ) := Classical.propDecidable _
    let _ : Decidable (h2 ∈ ψ) := Classical.propDecidable _
    by_cases h1ψ : h1 ∈ ψ <;> by_cases h2ψ : h2 ∈ ψ
    · have hiff : h1 ∈ ψ ↔ h2 ∈ ψ := ⟨fun _ => h2ψ, fun _ => h1ψ⟩
      rcases P.total h1 h2 with h12 | h21
      · left; right; exact ⟨hiff, h12⟩
      · right; right; exact ⟨hiff.symm, h21⟩
    · left; left; exact ⟨h1ψ, h2ψ⟩
    · right; left; exact ⟨h2ψ, h1ψ⟩
    · have hiff : h1 ∈ ψ ↔ h2 ∈ ψ := ⟨fun h => (h1ψ h).elim, fun h => (h2ψ h).elim⟩
      rcases P.total h1 h2 with h12 | h21
      · left; right; exact ⟨hiff, h12⟩
      · right; right; exact ⟨hiff.symm, h21⟩


theorem lexicographic_upgrade_fallback_disjoint {History : Type}
    (P : PlausibilityPreorder History) (ψ S : Set History) (h_disj : S ∩ ψ = ∅) :
    MinimalPlausibleStratum (LexicographicUpgrade P ψ) S = MinimalPlausibleStratum P S := by
  ext h
  simp only [MinimalPlausibleStratum, Set.mem_ofPred]
  constructor
  · rintro ⟨hS, hmin⟩
    refine ⟨hS, ?_⟩
    intro h' hh'
    have hnot : h ∉ ψ := by
      intro hψ
      have : h ∈ S ∩ ψ := ⟨hS, hψ⟩
      rw [h_disj] at this
      exact this
    have hnot' : h' ∉ ψ := by
      intro hψ'
      have : h' ∈ S ∩ ψ := ⟨hh', hψ'⟩
      rw [h_disj] at this
      exact this
    have hup := hmin h' hh'
    rcases hup with ⟨hψ, _⟩ | ⟨_, hle⟩
    · exact (hnot hψ).elim
    · exact hle
  · rintro ⟨hS, hmin⟩
    refine ⟨hS, ?_⟩
    intro h' hh'
    have hnot : h ∉ ψ := by
      intro hψ
      have : h ∈ S ∩ ψ := ⟨hS, hψ⟩
      rw [h_disj] at this
      exact this
    have hnot' : h' ∉ ψ := by
      intro hψ'
      have : h' ∈ S ∩ ψ := ⟨hh', hψ'⟩
      rw [h_disj] at this
      exact this
    right
    refine ⟨⟨fun hψ => (hnot hψ).elim, fun hψ' => (hnot' hψ').elim⟩, hmin h' hh'⟩


theorem lexicographic_upgrade_promotes_signal {History : Type}
    (P : PlausibilityPreorder History) (ψ S : Set History) (h_int : (S ∩ ψ).Nonempty) :
    MinimalPlausibleStratum (LexicographicUpgrade P ψ) S = MinimalPlausibleStratum P (S ∩ ψ) := by
  ext h
  simp only [MinimalPlausibleStratum, Set.mem_ofPred, Set.mem_inter_iff]
  constructor
  · rintro ⟨hS, hmin⟩
    obtain ⟨w, hwS, hwψ⟩ := h_int
    have hle_w := hmin w hwS
    have hψ : h ∈ ψ := by
      rcases hle_w with ⟨hψ, _⟩ | ⟨hiff, _⟩
      · exact hψ
      · exact hiff.mpr hwψ
    refine ⟨⟨hS, hψ⟩, ?_⟩
    intro h' ⟨hh'S, hh'ψ⟩
    have hup := hmin h' hh'S
    rcases hup with ⟨_, hnot⟩ | ⟨_, hle⟩
    · exact (hnot hh'ψ).elim
    · exact hle
  · rintro ⟨⟨hS, hψ⟩, hmin⟩
    refine ⟨hS, ?_⟩
    intro h' hh'S
    let _ : Decidable (h' ∈ ψ) := Classical.propDecidable _
    by_cases hh'ψ : h' ∈ ψ
    · right
      refine ⟨⟨fun _ => hh'ψ, fun _ => hψ⟩, hmin h' ⟨hh'S, hh'ψ⟩⟩
    · left
      exact ⟨hψ, hh'ψ⟩

section ActionFrameTheory

variable [W : ActionFrame]

/-- Agent type of the current `ActionFrame`. -/
abbrev Agent := W.Agent
/-- Moment type of the current `ActionFrame`. -/
abbrev Moment := W.Moment
/-- History type of the current `ActionFrame`. -/
abbrev History := W.History
/-- Action type of the current `ActionFrame`. -/
abbrev Action := W.Action
/-- Means type of the current `ActionFrame`. -/
abbrev Means := W.Means
/-- End type of the current `ActionFrame`. -/
abbrev Ends := W.Ends

/-- Bundle dominance implies the frame's preference relation. -/
theorem teleological_bundle_dominance_induces_preference (i : Agent) (t : Moment) (h : History)
    (b1 b2 : Means → ℕ) (h_dom : W.SubjectiveTeleologicalDominates i t h b1 b2) :
    W.Preference i t h (W.BundleEnd b1) (W.BundleEnd b2) :=
  W.teleological_bundle_dominance_induces_preference i t h b1 b2 h_dom

/-- Maturation outcome for action `α` on history `h'`. -/
def MaturationEnd (i : Agent) (α : Action) (t : Moment) (h' : History) : Ends :=
  W.MaturationEnd i α t h'

instance : Nonempty Agent := W.instNonemptyAgent
instance : Fintype Agent := W.instFintypeAgent
instance : DecidableEq Agent := W.instDecidableEqAgent
instance : DecidableEq Moment := W.instDecidableEqMoment
instance : DecidableEq History := W.instDecidableEqHistory
instance : Nonempty Action := W.instNonemptyAction
instance : DecidableEq Action := W.instDecidableEqAction
instance : DecidableEq Means := W.instDecidableEqMeans
instance : DecidableEq Ends := W.instDecidableEqEnds

/-- Baseline action `alpha_zero`. -/
abbrev alpha_zero : Action := W.alpha_zero
notation "α₀" => alpha_zero


-- 2. Temporal Relations and Branching


/-- Temporal precedence relation (<) on Moment. -/
abbrev Precedence : Moment → Moment → Prop := W.Precedence

instance : LT Moment where
  lt := W.Precedence

/-- Precedence is irreflexive. -/
theorem moment_lt_irrefl (t : Moment) : ¬(t < t) :=
  W.moment_lt_irrefl t

/-- Precedence is transitive. -/
theorem moment_lt_trans {t1 t2 t3 : Moment} : t1 < t2 → t2 < t3 → t1 < t3 :=
  W.moment_lt_trans

/-- Precedence is asymmetric. -/
theorem moment_lt_asymm {t1 t2 : Moment} (h1 : t1 < t2) (h2 : t2 < t1) : False :=
  moment_lt_irrefl t1 (moment_lt_trans h1 h2)

/-- Backward linearity: the temporal past of any moment is linearly ordered. -/
theorem backward_linearity {t1 t2 t3 : Moment} :
    t1 < t3 → t2 < t3 → t1 < t2 ∨ t1 = t2 ∨ t2 < t1 :=
  W.backward_linearity


-- 3. Histories and History Bundles


instance : Membership Moment History where
  mem h t := W.mem_hist t h

/-- Every history is a maximal linear chain of moments under temporal precedence. -/
theorem histories_maximal_linear (h : History) :
    IsMaximalLinearChain (· < ·) { t : Moment | t ∈ h } :=
  W.histories_maximal_linear h

/-- Every moment belongs to at least one history branch. -/
theorem moment_in_history (t : Moment) : ∃ h : History, t ∈ h :=
  W.moment_in_history t

/-- The history bundle passing through moment t: H(t) := { h : History | t ∈ h }. -/
def HistoryBundle (t : Moment) : Type :=
  { h : History // t ∈ h }


-- 4. Actions and Choice Partitions


/-- Contemplated menu of actions for agent i at ⟨t, h⟩. -/
abbrev A_cont (i : Agent) (t : Moment) (h : History) : Finset Action :=
  W.A_cont i t h

/-- Physical endowment ω : Agent → Moment → History → Means → ℕ. -/
abbrev omega (i : Agent) (t : Moment) (h : History) (m : Means) : ℕ :=
  W.omega i t h m

/-- Agent physical endowment of means. -/
abbrev endowment (i : Agent) (t : Moment) (h : History) (m : Means) : ℕ :=
  W.omega i t h m

/-- Production means requirements. -/
abbrev use_means (α : Action) (m : Means) : ℕ :=
  W.use_means α m

/-- Production means yields. -/
abbrev yield_means (α : Action) (m : Means) : ℕ :=
  W.yield_means α m

/-- Feasible menu of actions for agent i at ⟨t, h⟩. -/
abbrev A_feas (i : Agent) (t : Moment) (h : History) : Finset Action :=
  W.A_feas i t h

/-- The feasible menu at `t` is invariant across histories in `H(t)`. -/
theorem A_feas_bundle_invariant (i : Agent) (t : Moment) {h1 h2 : History}
    (h1_in : t ∈ h1) (h2_in : t ∈ h2) :
    A_feas i t h1 = A_feas i t h2 :=
  W.A_feas_bundle_invariant i t h1_in h2_in

/-- Preference at `t` is invariant across histories in `H(t)`. -/
theorem Preference_bundle_invariant (i : Agent) (t : Moment) {h1 h2 : History}
    (h1_in : t ∈ h1) (h2_in : t ∈ h2) :
    W.Preference i t h1 = W.Preference i t h2 :=
  W.Preference_bundle_invariant i t h1_in h2_in

/-- The passive/inertial baseline action α₀ is always feasible. -/
theorem alpha_zero_feasible (i : Agent) (t : Moment) (h : History) :
    α₀ ∈ A_feas i t h :=
  W.alpha_zero_feasible i t h

/-- Feasible menu is always non-empty. -/
theorem A_feas_nonempty (i : Agent) (t : Moment) (h : History) :
    (A_feas i t h).Nonempty :=
  ⟨α₀, alpha_zero_feasible i t h⟩

/-- Feasible actions never exceed current physical endowment. -/
theorem phys_feas_of_mem_feas (i : Agent) (t : Moment) (h : History) (α : Action) :
    α ∈ A_feas i t h → ∀ m, use_means α m ≤ omega i t h m :=
  fun h_mem => (W.A_feas_coupling i t h α).mp h_mem |>.2

/-- Proposition 2.13: Inaction preserves endowments across temporal transitions when uninvaded. -/
theorem inaction_preserves_endowments (i : Agent) (t t' : Moment) (h : History)
    (h_enacted : W.enacted i t h = α₀)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    ∀ m, omega i t' h m = omega i t h m :=
  W.inaction_preserves_endowments i t t' h h_enacted h_uninvaded h_next

/-- Proposition 2.14 (Part 1): Pure production reflects yield in ending inventory when uninvaded. -/
theorem pure_production_yield_only (i : Agent) (t t' : Moment) (h : History)
    (α : Action) (m : Means)
    (h_not_trade : ¬ W.IsTradeAction α)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_use : use_means α m = 0)
    (h_enacted : W.enacted i t h = α)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    omega i t' h m = omega i t h m + yield_means α m :=
  W.pure_production_yield_only i t t' h α m h_not_trade h_uninvaded h_use h_enacted h_next

/-- Proposition 2.14 (Part 2):
Pure consumption reflects use in ending inventory balance when uninvaded. -/
theorem pure_consumption_use_only (i : Agent) (t t' : Moment) (h : History)
    (α : Action) (m : Means)
    (h_not_trade : ¬ W.IsTradeAction α)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (W.enacted j t h) i)
    (h_yield : yield_means α m = 0)
    (h_enacted : W.enacted i t h = α)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    omega i t' h m + use_means α m = omega i t h m :=
  W.pure_consumption_use_only i t t' h α m h_not_trade h_uninvaded h_yield h_enacted h_next

/-- Enacted trajectory primitive: the physical action enacted by agent i at ⟨t, h⟩. -/
abbrev enacted (i : Agent) (t : Moment) (h : History) : Action :=
  W.enacted i t h

/-- Enacted actions are feasible whenever the moment belongs to the history. -/
theorem enacted_in_A_feas (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) :
    enacted i t h ∈ A_feas i t h :=
  W.enacted_in_A_feas i t h ht

/-- Histories through `t` on which agent `i` enacts action `α`. -/
def ChoicePartition (i : Agent) (t : Moment) (α : Action) : Set History :=
  { h : History | t ∈ h ∧ enacted i t h = α }

/-- Every history in the choice partition cell passes through moment t. -/
theorem choice_partition_subset_bundle (i : Agent) (t : Moment) (α : Action) :
  ∀ h ∈ ChoicePartition i t α, t ∈ h :=
  fun _ hh => hh.1

/-- Every history through `t` realizes some feasible action. -/
theorem choice_partition_cover (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) :
  ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α :=
  ⟨enacted i t h, enacted_in_A_feas i t h ht, ht, rfl⟩

/-- Partition cells are mutually disjoint for distinct actions. -/
theorem choice_partition_disjoint (i : Agent) (t : Moment) {α β : Action} (hne : α ≠ β) :
    Disjoint (ChoicePartition i t α) (ChoicePartition i t β) := by
  refine Set.disjoint_left.2 ?_
  intro h ⟨_, ha⟩ ⟨_, hb⟩
  subst ha hb
  exact hne rfl

/-- Partition cells are non-empty for all feasible actions along any passing branch. -/
theorem choice_partition_nonempty (i : Agent) (t : Moment) (h : History)
    (ht : t ∈ h) {α : Action} (hα : α ∈ A_feas i t h) :
    ∃ h' : History, h' ∈ ChoicePartition i t α := by
  have ⟨h_mem, h_enact⟩ := W.sigma_realization i t h h ht hα ht
  exact ⟨W.sigma i t α h, h_mem, h_enact⟩

/-- Standalone ActionFrame projection of choice partition non-emptiness. -/
theorem choice_partition_nonempty_expanded (i : Agent) (t : Moment) (h : History)
    (ht : t ∈ h) {α : Action} (hα : α ∈ A_feas i t h) :
    ∃ h' : History, t ∈ h' ∧ enacted i t h' = α := by
  have ⟨h_mem, h_enact⟩ := W.sigma_realization i t h h ht hα ht
  exact ⟨W.sigma i t α h, h_mem, h_enact⟩


-- 5. Execution Predicates


/-- Agent `i` executes `α` at `t` on histories in the choice partition. -/
def Exec (i : Agent) (t : Moment) (α : Action) : History → Prop :=
  fun h => h ∈ ChoicePartition i t α


def DynamicBox (i : Agent) (t : Moment) (α : Action) (ψ : History → Prop) : Prop :=
  ∀ h' : History, h' ∈ ChoicePartition i t α → ψ h'

/-- Histories in the same choice partition cell as `h`. -/
def STITChoiceCell (i : Agent) (t : Moment) (h : History) : Set History :=
  { h' : History | ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α ∧ h' ∈ ChoicePartition i t α }


def dstit (i : Agent) (t : Moment) (ψ : History → Prop) (h : History) : Prop :=
  (∀ h' ∈ STITChoiceCell i t h, ψ h') ∧
  (∃ h'' : History, t ∈ h'' ∧ ¬ ψ h'')

/-- If `h` enacts `α`, every history in its cell enacts `α`. -/
theorem choiceCell_subset_partition (i : Agent) (t : Moment) (h : History)
    {α : Action} (hh : h ∈ ChoicePartition i t α) :
    STITChoiceCell i t h ⊆ ChoicePartition i t α := by
  intro h' hh'
  rcases hh' with ⟨β, _, hh_β, hh'_β⟩
  by_cases h_eq : β = α
  · subst h_eq; exact hh'_β
  · have h_disj := choice_partition_disjoint i t h_eq
    exact False.elim (Set.disjoint_left.mp h_disj hh_β hh)

/-- If `Exec` holds throughout the choice cell, it holds at `h`. -/
theorem dstit_exec_mem (i : Agent) (t : Moment) (h : History) (α : Action)
    (ht : t ∈ h) (h_dstit : dstit i t (Exec i t α) h) :
    Exec i t α h := by
  obtain ⟨β, hβ, hhβ⟩ := choice_partition_cover i t h ht
  have h_in_cell : h ∈ STITChoiceCell i t h := ⟨β, hβ, hhβ, hhβ⟩
  have h_pos := h_dstit.1 h h_in_cell
  exact h_pos


-- 6. Action Horizon


def IsPostHorizon (i : Agent) (t : Moment) (h : History) : Prop :=
  A_feas i t h = {α₀}


-- 7. Beliefs and Event Updates


/-- Minimal plausibility worlds for agent i at moment t. -/
abbrev MinPlausible (i : Agent) (t : Moment) : Set History :=
  W.MinPlausible i t

/-- Projected moment for agent `i` and history `h'`. -/
abbrev tau (i : Agent) (t : Moment) (h' : History) : Moment :=
  W.tau i t h'

/-- History branch incidence relation. -/
abbrev mem_hist (t : Moment) (h : History) : Prop :=
  W.mem_hist t h

/-- Every plausible history contains its projected moment. -/
theorem min_plausible_node_incidence (i : Agent) (t : Moment) :
    ∀ h' ∈ MinPlausible i t, tau i t h' ∈ h' :=
  W.min_plausible_node_incidence i t

/-- A history through `t` projects to `t`. -/
theorem tau_centering (i : Agent) (t : Moment) (h : History) (h_mem : t ∈ h) :
    tau i t h = t :=
  W.tau_centering i t h h_mem

/-- The minimal plausibility set is non-empty. -/
theorem min_plausible_nonempty (i : Agent) (t : Moment) : (MinPlausible i t).Nonempty :=
  W.min_plausible_nonempty i t

/-- `ψ` holds on every plausible history for agent `i` at `t`. -/
def Belief (i : Agent) (t : Moment) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ MinPlausible i t, ψ h'

/-- Plausible histories after restricting to those satisfying `ε`. -/
def DELUpdate (i : Agent) (t : Moment) (ε : History → Prop) : Set History :=
  W.DELUpdate i t ε

/-- `ψ` holds on every history in the update by `ε`. -/
def BeliefAfterUpdate (i : Agent) (t : Moment) (ε : History → Prop) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ DELUpdate i t ε, ψ h'

/-- Histories that contain their projected moment. -/
def EpistemicBundle (i : Agent) (t : Moment) : Set History :=
  { h' : History | mem_hist (tau i t h') h' }

/-- The projected epistemic horizon bundle is non-empty. -/
theorem epistemic_bundle_nonempty (i : Agent) (t : Moment) :
    (EpistemicBundle i t).Nonempty := by
  obtain ⟨h_pl, hh_pl⟩ := min_plausible_nonempty i t
  exact ⟨h_pl, min_plausible_node_incidence i t h_pl hh_pl⟩


def LexicographicBeliefUpdate (i : Agent) (t : Moment)
    (P : PlausibilityPreorder History) (ψ : Set History) : Set History :=
  MinimalPlausibleStratum (LexicographicUpgrade P ψ) (EpistemicBundle i t)


theorem lexicographic_belief_update_nonempty [Finite History] (i : Agent) (t : Moment)
    (P : PlausibilityPreorder History) (ψ : Set History) :
    (LexicographicBeliefUpdate i t P ψ).Nonempty :=
  minimal_plausible_stratum_nonempty (LexicographicUpgrade P ψ) (EpistemicBundle i t)
    (epistemic_bundle_nonempty i t)


theorem lexicographic_belief_update_fallback_disjoint
    (i : Agent) (t : Moment) (P : PlausibilityPreorder History) (ψ : Set History)
    (h_disj : EpistemicBundle i t ∩ ψ = ∅) :
    LexicographicBeliefUpdate i t P ψ = MinimalPlausibleStratum P (EpistemicBundle i t) :=
  lexicographic_upgrade_fallback_disjoint P ψ (EpistemicBundle i t) h_disj


theorem lexicographic_belief_update_promotes_signal
    (i : Agent) (t : Moment) (P : PlausibilityPreorder History) (ψ : Set History)
    (h_int : (EpistemicBundle i t ∩ ψ).Nonempty) :
    LexicographicBeliefUpdate i t P ψ = MinimalPlausibleStratum P (EpistemicBundle i t ∩ ψ) :=
  lexicographic_upgrade_promotes_signal P ψ (EpistemicBundle i t) h_int

/-- The baseline inertial action α₀ is never a trade action. -/
theorem alpha_zero_not_trade : ¬ W.IsTradeAction α₀ :=
  W.alpha_zero_not_trade

end ActionFrameTheory


-- Section 8: Bilateral Trade and Resource Transitions


section MultiAgentTransitions

variable [W : ActionFrame] [BilateralExchangeFrame W]


theorem bilateral_exchange_conserves_means
    (i j : Agent) (t t' : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_distinct_agents : i ≠ j)
    (h_distinct_goods : mA ≠ mB)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h)
    (h_exec_i : enacted i t h = W.Offer i j qA mA qB mB)
    (h_exec_j : enacted j t h = W.Accept j i qA mA qB mB) :
    omega i t' h mA + omega j t' h mA = omega i t h mA + omega j t h mA ∧
    omega i t' h mB + omega j t' h mB = omega i t h mB + omega j t h mB := by
  have ⟨h_tr_i_mA, h_tr_j_mA⟩ :=
    W.bilateral_transfer_law i j qA mA qB mB t t' h mA h_distinct_agents h_exec_i h_exec_j h_next
  have ⟨h_tr_i_mB, h_tr_j_mB⟩ :=
    W.bilateral_transfer_law i j qA mA qB mB t t' h mB h_distinct_agents h_exec_i h_exec_j h_next
  simp only [h_distinct_goods, ite_true, ite_false] at h_tr_i_mA h_tr_j_mA
  simp only [h_distinct_goods.symm, ite_true, ite_false] at h_tr_i_mB h_tr_j_mB
  dsimp [omega]
  constructor
  · omega
  · omega

/-- Characterizes whether agent `i`'s offer is matched by a corresponding accept from `j`. -/
def IsMatchedOffer (profile : Agent → Action) (i : Agent) : Prop :=
  ∃ j qA mA qB mB, i ≠ j ∧
    profile i = W.Offer i j qA mA qB mB ∧ profile j = W.Accept j i qA mA qB mB

/-- Characterizes whether agent `i`'s accept is matched by a corresponding offer from `j`. -/
def IsMatchedAccept (profile : Agent → Action) (i : Agent) : Prop :=
  ∃ j qA mA qB mB, i ≠ j ∧
    profile i = W.Accept i j qA mA qB mB ∧ profile j = W.Offer j i qA mA qB mB

/-- Characterizes whether agent `i` enacts a unilateral, unmatched trade action. -/
def IsUnilateralTrade (profile : Agent → Action) (i : Agent) : Prop :=
  (∃ j qA mA qB mB, profile i = W.Offer i j qA mA qB mB ∧
    (i = j ∨ profile j ≠ W.Accept j i qA mA qB mB)) ∨
  (∃ j qA mA qB mB, profile i = W.Accept i j qA mA qB mB ∧
    (i = j ∨ profile j ≠ W.Offer j i qA mA qB mB))

/-- Realized consumption of means by agent `i` under joint action profile `profile`.
    Unmatched trade offers/accepts consume 0 means. -/
noncomputable def realized_use_means (i : Agent) (profile : Agent → Action) (m : Means) : ℕ :=
  let _ : Decidable (IsMatchedOffer profile i ∨ IsMatchedAccept profile i) :=
    Classical.propDecidable _
  let _ : Decidable (IsUnilateralTrade profile i) := Classical.propDecidable _
  if IsMatchedOffer profile i ∨ IsMatchedAccept profile i then
    W.use_means (profile i) m
  else if IsUnilateralTrade profile i then
    0
  else
    W.use_means (profile i) m

/-- Realized yield of means for agent `i` under joint action profile `profile`.
    Unmatched trade offers/accepts yield 0 means. -/
noncomputable def realized_yield_means (i : Agent) (profile : Agent → Action) (m : Means) : ℕ :=
  let _ : Decidable (IsMatchedOffer profile i ∨ IsMatchedAccept profile i) :=
    Classical.propDecidable _
  let _ : Decidable (IsUnilateralTrade profile i) := Classical.propDecidable _
  if IsMatchedOffer profile i ∨ IsMatchedAccept profile i then
    W.yield_means (profile i) m
  else if IsUnilateralTrade profile i then
    0
  else
    W.yield_means (profile i) m

/-- Trade action enacted by agent `i` names `i` as offering or accepting party. -/
def IsSelfTradeAction (i : Agent) (α : Action) : Prop :=
  (∃ j qA mA qB mB, α = W.Offer i j qA mA qB mB) ∨
  (∃ j qA mA qB mB, α = W.Accept i j qA mA qB mB)


theorem joint_profile_conservation_law
    (i : Agent) (t t' : Moment) (h : History) (m : Means)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h)
    (h_uninvaded : ∀ j, ¬ W.IsInvasiveOn (enacted j t h) i)
    (h_self : W.IsTradeAction (enacted i t h) → IsSelfTradeAction i (enacted i t h)) :
    omega i t' h m + realized_use_means i (fun a => enacted a t h) m =
    omega i t h m + realized_yield_means i (fun a => enacted a t h) m := by
  set α := enacted i t h
  set profile : Agent → Action := fun a => enacted a t h
  by_cases h_match : IsMatchedOffer profile i ∨ IsMatchedAccept profile i
  · have h_use_eq : realized_use_means i profile m = W.use_means α m := by
      dsimp [realized_use_means]
      simp only [h_match, ↓reduceIte]
      rfl
    have h_yield_eq : realized_yield_means i profile m = W.yield_means α m := by
      dsimp [realized_yield_means]
      simp only [h_match, ↓reduceIte]
      rfl
    rw [h_use_eq, h_yield_eq]
    rcases h_match with ⟨j, qA, mA, qB, mB, h_ne, h_off, h_acc⟩ |
      ⟨j, qA, mA, qB, mB, h_ne, h_acc, h_off⟩
    · have h_tr := (W.bilateral_transfer_law i j qA mA qB mB t t' h m h_ne h_off h_acc h_next).1
      have h_use := W.use_means_offer i j qA mA qB mB m
      have h_yield := W.yield_means_offer i j qA mA qB mB m
      rw [← h_off] at h_use h_yield
      rw [h_use, h_yield]
      exact h_tr
    · have h_tr :=
        (W.bilateral_transfer_law j i qA mA qB mB t t' h m h_ne.symm h_off h_acc h_next).2
      have h_use := W.use_means_accept i j qA mA qB mB m
      have h_yield := W.yield_means_accept i j qA mA qB mB m
      rw [← h_acc] at h_use h_yield
      rw [h_use, h_yield]
      exact h_tr
  · by_cases h_uni : IsUnilateralTrade profile i
    · have h_use_zero : realized_use_means i profile m = 0 := by
        dsimp [realized_use_means]
        simp only [h_match, h_uni, ↓reduceIte]
      have h_yield_zero : realized_yield_means i profile m = 0 := by
        dsimp [realized_yield_means]
        simp only [h_match, h_uni, ↓reduceIte]
      rw [h_use_zero, h_yield_zero, Nat.add_zero, Nat.add_zero]
      rcases h_uni with ⟨j, qA, mA, qB, mB, h_off, h_not_acc⟩ |
        ⟨j, qA, mA, qB, mB, h_acc, h_not_off⟩
      · by_cases h_eq : i = j
        · subst h_eq
          have h_ne_acc : profile i ≠ W.Accept i i qA mA qB mB := by
            intro h_same
            rw [h_off] at h_same
            exact W.offer_ne_accept h_same
          exact W.unilateral_offer_noop i i qA mA qB mB t t' h m h_off h_ne_acc h_next
        · rcases h_not_acc with h_eq2 | h_not_acc
          · exact (h_eq h_eq2).elim
          · exact W.unilateral_offer_noop i j qA mA qB mB t t' h m h_off h_not_acc h_next
      · by_cases h_eq : i = j
        · subst h_eq
          have h_ne_off : profile i ≠ W.Offer i i qA mA qB mB := by
            intro h_same
            rw [h_acc] at h_same
            exact W.offer_ne_accept h_same.symm
          exact W.unilateral_accept_noop i i qA mA qB mB t t' h m h_acc h_ne_off h_next
        · rcases h_not_off with h_eq2 | h_not_off
          · exact (h_eq h_eq2).elim
          · exact W.unilateral_accept_noop i j qA mA qB mB t t' h m h_acc h_not_off h_next
    · have h_use_eq : realized_use_means i profile m = W.use_means α m := by
        dsimp [realized_use_means]
        simp only [h_match, h_uni, ↓reduceIte]
        rfl
      have h_yield_eq : realized_yield_means i profile m = W.yield_means α m := by
        dsimp [realized_yield_means]
        simp only [h_match, h_uni, ↓reduceIte]
        rfl
      rw [h_use_eq, h_yield_eq]
      have h_not_tr : ¬ W.IsTradeAction α := by
        intro h_tr
        have h_self_tr := h_self h_tr
        rcases h_self_tr with ⟨j, qA, mA, qB, mB, h_off⟩ | ⟨j, qA, mA, qB, mB, h_acc⟩
        · by_cases h_eq : i = j
          · apply h_uni
            left
            exact ⟨j, qA, mA, qB, mB, h_off, Or.inl h_eq⟩
          · by_cases h_acc_j : profile j = W.Accept j i qA mA qB mB
            · apply h_match
              left
              exact ⟨j, qA, mA, qB, mB, h_eq, h_off, h_acc_j⟩
            · apply h_uni
              left
              exact ⟨j, qA, mA, qB, mB, h_off, Or.inr h_acc_j⟩
        · by_cases h_eq : i = j
          · apply h_uni
            right
            exact ⟨j, qA, mA, qB, mB, h_acc, Or.inl h_eq⟩
          · by_cases h_off_j : profile j = W.Offer j i qA mA qB mB
            · apply h_match
              right
              exact ⟨j, qA, mA, qB, mB, h_eq, h_acc, h_off_j⟩
            · apply h_uni
              right
              exact ⟨j, qA, mA, qB, mB, h_acc, Or.inr h_off_j⟩
      exact W.law_in_re_transition i t t' h α m h_not_tr h_uninvaded rfl h_next

end MultiAgentTransitions


def STITAgentIndependence (F : ActionFrame) (t : F.Moment) : Prop :=
  ∀ (s : F.Agent → F.Action),
    (∀ i h, F.mem_hist t h → s i ∈ F.A_feas i t h) →
    ∃ h' : F.History, F.mem_hist t h' ∧ ∀ i, F.enacted i t h' = s i

section CapitalPathDependence

variable [W : ActionFrame]

/-- Actions requiring more physical means than available in endowment are infeasible. -/
theorem infeasible_of_insufficient_endowment
    (i : Agent) (t : Moment) (h : History) (β : Action) (m : Means)
    (h_insufficient : omega i t h m < use_means β m) :
    β ∉ A_feas i t h := by
  intro h_mem
  have h_le := phys_feas_of_mem_feas i t h β h_mem m
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_insufficient h_le)


theorem hulsmann_path_dependent_availability
    (i : Agent) (t t1' t2' : Moment) (h1 h2 : History)
    (α_build α_consume β_downstream : Action) (m_cap : Means)
    (h_next1 : IsNextMoment Precedence W.mem_hist t t1' h1)
    (h_next2 : IsNextMoment Precedence W.mem_hist t t2' h2)
    (h_not_tr1 : ¬ W.IsTradeAction α_build)
    (h_not_tr2 : ¬ W.IsTradeAction α_consume)
    (h_uninv1 : ∀ j, ¬ W.IsInvasiveOn (enacted j t h1) i)
    (h_uninv2 : ∀ j, ¬ W.IsInvasiveOn (enacted j t h2) i)
    (h_init1 : omega i t h1 m_cap = 0)
    (h_init2 : omega i t h2 m_cap = 0)
    (h_exec1 : enacted i t h1 = α_build)
    (h_exec2 : enacted i t h2 = α_consume)
    (h_use_build : use_means α_build m_cap = 0)
    (h_yield_build : yield_means α_build m_cap = 1)
    (h_use_cons : use_means α_consume m_cap = 0)
    (h_yield_cons : yield_means α_consume m_cap = 0)
    (h_req_down : use_means β_downstream m_cap = 1) :
    omega i t1' h1 m_cap = 1 ∧
    omega i t2' h2 m_cap = 0 ∧
    β_downstream ∉ A_feas i t2' h2 := by
  dsimp [use_means, yield_means, omega] at h_use_build h_yield_build h_use_cons h_yield_cons
  dsimp [use_means, yield_means, omega] at h_init1 h_init2 h_req_down
  have h_tr1 := W.law_in_re_transition i t t1' h1 α_build m_cap h_not_tr1 h_uninv1 h_exec1 h_next1
  rw [h_use_build, h_init1, h_yield_build, Nat.add_zero, Nat.zero_add] at h_tr1
  have h_tr2 := W.law_in_re_transition i t t2' h2 α_consume m_cap h_not_tr2 h_uninv2 h_exec2 h_next2
  rw [h_use_cons, h_init2, h_yield_cons, Nat.add_zero, Nat.zero_add] at h_tr2
  refine ⟨h_tr1, h_tr2, ?_⟩
  apply infeasible_of_insufficient_endowment i t2' h2 β_downstream m_cap
  change W.omega i t2' h2 m_cap < W.use_means β_downstream m_cap
  rw [h_tr2, h_req_down]
  exact Nat.zero_lt_one

end CapitalPathDependence



end Praxeology

end
