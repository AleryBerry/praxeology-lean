/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Production
public import Praxeology.Marginal
public import Praxeology.ExactNat
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Basic

/-!
# Catallactics: Exchange, Money, and Capital

This module formalizes Austrian catallactics, including the Mengerian theory
of the emergence of media of exchange, Ricardian comparative advantage,
multilateral cohort market clearing, and monetary economic calculation.
-/

@[expose] public section


namespace Praxeology


-- Section 1: Bilateral Exchange and Coercion


/-- Joint counterfactual branch at `⟨t, h⟩` where `i` enacts `α_i` and `j` enacts `α_j`,
constructed by sequentially selecting counterfactual branches using `W.sigma`. -/
def jointBranch [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : W.History :=
  W.sigma j t α_j (W.sigma i t α_i h)

theorem jointBranch_realizes_pair [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) (h_ij : i ≠ j) (ht : W.mem_hist t h)
    (h_feas_i : α_i ∈ W.A_feas i t h) (h_feas_j : α_j ∈ W.A_feas j t (W.sigma i t α_i h)) :
    W.mem_hist t (jointBranch i j t h α_i α_j) ∧
    W.enacted i t (jointBranch i j t h α_i α_j) = α_i ∧
    W.enacted j t (jointBranch i j t h α_i α_j) = α_j := by
  dsimp [jointBranch]
  have h_real_i := W.sigma_realization i t h h ht h_feas_i ht
  have h_real_j := W.sigma_realization j t (W.sigma i t α_i h) (W.sigma i t α_i h)
    h_real_i.1 h_feas_j h_real_i.1
  have h_co_i := W.sigma_co_agency j i t (W.sigma i t α_i h) (W.sigma i t α_i h)
    h_ij.symm h_real_i.1 h_feas_j h_real_i.1
  refine ⟨h_real_j.1, ?_, ?_⟩
  · rw [h_co_i, h_real_i.2]
  · exact h_real_j.2

/-- Outcome end of agent `i` under a joint action pair, evaluated at the
action's declared maturation moment on its own counterfactual history. -/
def jointEndI [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : W.Ends :=
  let branch := jointBranch i j t h α_i α_j
  W.OutcomeOf i α_i t (W.ExpectedMaturation i α_i t branch) branch

/-- Outcome end of agent `j` under a joint action pair, evaluated at the
action's declared maturation moment on its own counterfactual history. -/
def jointEndJ [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : W.Ends :=
  let branch := jointBranch i j t h α_i α_j
  W.OutcomeOf j α_j t (W.ExpectedMaturation j α_j t branch) branch

/-- Action `α_j` enacted by `j` at `⟨t, h⟩` is endogenously invasive against `i` along `t → t'`
if executing `α_j` while `i` is passive (`α₀`) contracts `i`'s physical stock of some means below
their baseline endowment. -/
def EndogenouslyInvasiveJ [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_j : W.Action) : Prop :=
  let branch := jointBranch i j t h W.alpha_zero α_j
  ∃ m : W.Means,
    W.omega i (W.ExpectedMaturation i W.alpha_zero t branch) branch m < W.omega i t h m

/-- Action `α_i` enacted by `i` at `⟨t, h⟩` is endogenously invasive against `j` along `t → t'`
if executing `α_i` while `j` is passive (`α₀`) contracts `j`'s physical stock of some means below
their baseline endowment. -/
def EndogenouslyInvasiveI [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i : W.Action) : Prop :=
  let branch := jointBranch i j t h α_i W.alpha_zero
  ∃ m : W.Means,
    W.omega j (W.ExpectedMaturation j W.alpha_zero t branch) branch m < W.omega j t h m

/-- Purposeful response of agent `i` to `j`'s action `α_j`: `i` strictly prefers
the outcome of executing `α_i` to remaining passive `α₀`, holding `j`'s action fixed. -/
def PurposefulResponseI [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  W.Preference i t h (jointEndI i j t h α_i α_j) (jointEndI i j t h W.alpha_zero α_j)

/-- Voluntary (catallactic) exchange between agents `i` and `j` at `⟨t, t', h⟩`:
neither agent invades the other's physical stock, and both strictly prefer the
joint exchange outcome to their autarkic/status-quo baseline. -/
def IsVoluntaryExchange [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_j ∧
  W.Preference i t h (jointEndI i j t h α_i α_j)
    (jointEndI i j t h W.alpha_zero W.alpha_zero) ∧
  W.Preference j t h (jointEndJ i j t h α_i α_j)
    (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Coercive extortion (hegemonic extraction / taxation) by `j` against `i` at `⟨t, t', h⟩`:
`j`'s threat/policy `α_threat` is physically invasive against `i`, victim `i` purposefully complies
because compliance beats being punished under the invasion, but `i` strictly prefers the uninvaded
baseline to the extortion outcome, while aggressor `j` strictly prefers the extortion outcome. -/
def IsCoerciveExtortion [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_threat : W.Action) : Prop :=
  EndogenouslyInvasiveJ i j t h α_threat ∧
  PurposefulResponseI i j t h α_i α_threat ∧
  W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
    (jointEndI i j t h α_i α_threat) ∧
  W.Preference j t h (jointEndJ i j t h α_i α_threat)
    (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Market competition by `j` against `i` at `⟨t, t', h⟩`:
neither agent invades the other's property, competitor `j` benefits from their action,
and even if `i`'s end is worse than baseline, this loss occurs through peaceful preference shifts
without physical invasion. -/
def IsMarketCompetition [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_comp : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_comp ∧
  W.Preference j t h (jointEndJ i j t h α_i α_comp) (jointEndJ i j t h α_i W.alpha_zero) ∧
  W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
    (jointEndI i j t h α_i α_comp)

/-- Action `α_j` strips contemplated actions from `i`'s menu along `t → t'` when some action
feasible given `i`'s initial endowment exceeds `i`'s post-invasion stock. -/
def MenuStrippingInvasiveJ [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_j : W.Action) : Prop :=
  ∃ β, (∀ m, W.use_means β m ≤ W.omega i t h m) ∧
    ¬ (∀ m, W.use_means β m ≤
      W.omega i
        (W.ExpectedMaturation i W.alpha_zero t (jointBranch i j t h W.alpha_zero α_j))
        (jointBranch i j t h W.alpha_zero α_j) m)

theorem highwayman_is_purposeful_but_not_catallactic
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i α_threat : W.Action)
    (h_ext : IsCoerciveExtortion i j t h α_i α_threat) :
    PurposefulResponseI i j t h α_i α_threat ∧
    ¬ IsVoluntaryExchange i j t h α_i α_threat := by
  refine ⟨h_ext.2.1, ?_⟩
  intro h_vol
  exact h_vol.2.1 h_ext.1

theorem rothbard_demonstrated_welfare_dichotomy
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i_star α_j_star : W.Action) :
    (IsVoluntaryExchange i j t h α_i_star α_j_star →
      W.Preference i t h (jointEndI i j t h α_i_star α_j_star)
        (jointEndI i j t h W.alpha_zero W.alpha_zero) ∧
      W.Preference j t h (jointEndJ i j t h α_i_star α_j_star)
        (jointEndJ i j t h W.alpha_zero W.alpha_zero)) ∧
    (IsCoerciveExtortion i j t h α_i_star α_j_star →
      W.Preference j t h (jointEndJ i j t h α_i_star α_j_star)
        (jointEndJ i j t h W.alpha_zero W.alpha_zero) ∧
      W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
        (jointEndI i j t h α_i_star α_j_star)) := by
  refine ⟨fun h_cat => ⟨h_cat.2.2.1, h_cat.2.2.2⟩,
          fun h_ext => ⟨h_ext.2.2.2, h_ext.2.2.1⟩⟩

theorem competition_is_not_coercion
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i α_comp : W.Action)
    (h_comp : IsMarketCompetition i j t h α_i α_comp) :
    ¬ IsCoerciveExtortion i j t h α_i α_comp := by
  intro h_ext
  exact h_comp.2.1 h_ext.1

/-- Autarkic non-interference: neither agent invades the other's stock, agent `i`'s
realized end equals the passive baseline, and agent `j` strictly prefers the joint outcome
to the passive baseline. -/
def IsAutarkicNonInterference [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_j ∧
  jointEndI i j t h α_i α_j = jointEndI i j t h W.alpha_zero W.alpha_zero ∧
  W.Preference j t h (jointEndJ i j t h α_i α_j)
    (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Unilateral gift: neither agent invades the other's stock, recipient `i` strictly prefers
the joint outcome to baseline, and donor `j` does not strictly prefer the outcome. -/
def IsUnilateralGift [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_j ∧
  W.Preference i t h (jointEndI i j t h α_i α_j)
    (jointEndI i j t h W.alpha_zero W.alpha_zero) ∧
  ¬ W.Preference j t h (jointEndJ i j t h α_i α_j)
    (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Destructive aggression: agent `j` physically invades `i`'s stock without purposeful
compliance by `i`, reducing `i`'s stock below clean title `title_i`, while `i` strictly
prefers the uninvaded baseline to the outcome and does not invade `j`. -/
def IsPureDestructiveAggression [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (title_i : W.Means → ℕ) (α_i α_j : W.Action) : Prop :=
  let branch := jointBranch i j t h W.alpha_zero α_j
  EndogenouslyInvasiveJ i j t h α_j ∧
  ¬ PurposefulResponseI i j t h α_i α_j ∧
  (∃ m : W.Means,
    W.omega i (W.ExpectedMaturation i W.alpha_zero t branch) branch m < title_i m) ∧
  W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
    (jointEndI i j t h α_i α_j) ∧
  ¬ EndogenouslyInvasiveI i j t h α_i

/-- Defensive title recovery: agent `j` reduces `i`'s present physical possession without
extortive compliance, while preserving all of `i`'s legitimate title `title_i`, and `j`
strictly prefers the outcome to baseline. -/
def IsRestitutionRecovery [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (title_i : W.Means → ℕ) (α_i α_j : W.Action) : Prop :=
  let branch := jointBranch i j t h W.alpha_zero α_j
  EndogenouslyInvasiveJ i j t h α_j ∧
  ¬ PurposefulResponseI i j t h α_i α_j ∧
  (∀ m : W.Means,
    title_i m ≤ W.omega i (W.ExpectedMaturation i W.alpha_zero t branch) branch m) ∧
  W.Preference j t h (jointEndJ i j t h α_i α_j)
    (jointEndJ i j t h W.alpha_zero W.alpha_zero)

/-- Mutual combat / bilateral war: both agents enact physically invasive actions against each other,
neither complies under threat, and both strictly prefer the autonomous baseline (peace) to the
destructive combat outcome. -/
def IsMutualCombat [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  EndogenouslyInvasiveI i j t h α_i ∧
  EndogenouslyInvasiveJ i j t h α_j ∧
  ¬ PurposefulResponseI i j t h α_i α_j ∧
  W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
    (jointEndI i j t h α_i α_j) ∧
  W.Preference j t h (jointEndJ i j t h W.alpha_zero W.alpha_zero)
    (jointEndJ i j t h α_i α_j)

/-- Coordination failure / bilateral malinvestment: neither agent physically invades the other,
but through uncoordinated action, both agents strictly prefer the autonomous baseline
to the realized joint outcome, and agent `j` fails to gain even conditionally. -/
def IsCoordinationFailure [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_j ∧
  W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
    (jointEndI i j t h α_i α_j) ∧
  W.Preference j t h (jointEndJ i j t h W.alpha_zero W.alpha_zero)
    (jointEndJ i j t h α_i α_j) ∧
  ¬ W.Preference j t h (jointEndJ i j t h α_i α_j) (jointEndJ i j t h α_i W.alpha_zero)

/-- Passive inaction / peaceful coexistence: both agents refrain from acting,
producing exact autonomous baseline outcomes for both agents. -/
def IsPassiveInaction [W : ActionFrame] (i j : W.Agent) (t : W.Moment) (h : W.History)
    (α_i α_j : W.Action) : Prop :=
  ¬ EndogenouslyInvasiveI i j t h α_i ∧
  ¬ EndogenouslyInvasiveJ i j t h α_j ∧
  jointEndI i j t h α_i α_j = jointEndI i j t h W.alpha_zero W.alpha_zero ∧
  jointEndJ i j t h α_i α_j = jointEndJ i j t h W.alpha_zero W.alpha_zero

/-- When agent `j`'s invasive action physically contracts agent `i`'s stock of means `m`
below the requirement for a valued end `e` that `i`'s baseline stock attains, `i`'s baseline
bundle teleologically dominates the invaded bundle, precluding respondent gain. -/
theorem physical_invasion_depriving_valued_end_precludes_respondent_gain
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i α_j : W.Action) (m : W.Means) (e : W.Ends)
    (b_base b_inv : W.Means → ℕ)
    (h_base_end : jointEndI i j t h W.alpha_zero W.alpha_zero = W.BundleEnd b_base)
    (h_inv_end : jointEndI i j t h α_i α_j = W.BundleEnd b_inv)
    (h_valued : W.ValuedEnd i t h e)
    (h_unique : ∀ e', W.ValuedEnd i t h e' → e' = e)
    (h_req_base : ∀ m', W.requirement e m' ≤ b_base m')
    (h_inv_short : b_inv m < W.requirement e m) :
    ¬ W.Preference i t h (jointEndI i j t h α_i α_j)
        (jointEndI i j t h W.alpha_zero W.alpha_zero) := by
  have h_dom : W.SubjectiveTeleologicalDominates i t h b_base b_inv := by
    have h_attains : JointlyAttains W.requirement b_base {e} := by
      intro m'
      rw [Finset.sum_singleton]
      exact h_req_base m'
    have h_misses : ¬ JointlyAttains W.requirement b_inv {e} := by
      intro h_att
      have h_m := h_att m
      rw [Finset.sum_singleton] at h_m
      exact (Nat.not_le_of_gt h_inv_short) h_m
    exact subjective_teleological_dominates_of_unique_valued_end
      W.requirement (W.ValuedEnd i t h) e b_base b_inv h_unique h_valued h_attains h_misses
  have h_base_pref :=
    W.teleological_bundle_dominance_induces_preference i t h b_base b_inv h_dom
  rw [← h_base_end, ← h_inv_end] at h_base_pref
  exact W.pref_asymm i t h h_base_pref

/-- Pairwise mutual exclusivity across all ten bilateral interaction classes:
voluntary exchange, coercive extortion, market competition, autarkic non-interference,
unilateral gift, pure destructive aggression, defensive restitution, mutual combat,
coordination failure, and passive inaction. -/
theorem praxeological_interaction_classes_pairwise_mutual_exclusivity
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (title_i : W.Means → ℕ) (α_i α_j : W.Action) :
    ¬ (IsVoluntaryExchange i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsVoluntaryExchange i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsCoerciveExtortion i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsAutarkicNonInterference i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsUnilateralGift i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsPureDestructiveAggression i j t h title_i α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsRestitutionRecovery i j t h title_i α_i α_j ∧
        IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsMutualCombat i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsCoordinationFailure i j t h α_i α_j ∧ IsMutualCombat i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsVoluntaryExchange i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsCoerciveExtortion i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsMarketCompetition i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsAutarkicNonInterference i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsUnilateralGift i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧
        IsPureDestructiveAggression i j t h title_i α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧
        IsRestitutionRecovery i j t h title_i α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsMutualCombat i j t h α_i α_j) ∧
    ¬ (IsPassiveInaction i j t h α_i α_j ∧ IsCoordinationFailure i j t h α_i α_j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h_vol, h_ext⟩; exact h_vol.2.1 h_ext.1
  · rintro ⟨h_vol, h_comp⟩; exact W.pref_asymm i t h h_vol.2.2.1 h_comp.2.2.2
  · rintro ⟨h_ext, h_comp⟩; exact h_comp.2.1 h_ext.1
  · rintro ⟨h_aut, h_vol⟩
    have h_p := h_vol.2.2.1
    rw [h_aut.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_aut, h_ext⟩; exact h_aut.2.1 h_ext.1
  · rintro ⟨h_aut, h_comp⟩
    have h_p := h_comp.2.2.2
    rw [h_aut.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_aut, h_gift⟩
    have h_p := h_gift.2.2.1
    rw [h_aut.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_aut, h_dest⟩; exact h_aut.2.1 h_dest.1
  · rintro ⟨h_aut, h_rec⟩; exact h_aut.2.1 h_rec.1
  · rintro ⟨h_gift, h_vol⟩; exact h_gift.2.2.2 h_vol.2.2.2
  · rintro ⟨h_gift, h_ext⟩; exact h_gift.2.1 h_ext.1
  · rintro ⟨h_gift, h_comp⟩; exact W.pref_asymm i t h h_gift.2.2.1 h_comp.2.2.2
  · rintro ⟨h_gift, h_dest⟩; exact h_gift.2.1 h_dest.1
  · rintro ⟨h_gift, h_rec⟩; exact h_gift.2.1 h_rec.1
  · rintro ⟨h_dest, h_vol⟩; exact h_vol.2.1 h_dest.1
  · rintro ⟨h_dest, h_ext⟩; exact h_dest.2.1 h_ext.2.1
  · rintro ⟨h_dest, h_comp⟩; exact h_comp.2.1 h_dest.1
  · rintro ⟨h_dest, h_rec⟩
    obtain ⟨m, h_lt⟩ := h_dest.2.2.1
    have h_ge := h_rec.2.2.1 m
    exact Nat.not_le_of_gt h_lt h_ge
  · rintro ⟨h_rec, h_vol⟩; exact h_vol.2.1 h_rec.1
  · rintro ⟨h_rec, h_ext⟩; exact h_rec.2.1 h_ext.2.1
  · rintro ⟨h_rec, h_comp⟩; exact h_comp.2.1 h_rec.1
  · rintro ⟨h_com, h_vol⟩; exact h_vol.2.1 h_com.2.1
  · rintro ⟨h_com, h_ext⟩; exact h_com.2.2.1 h_ext.2.1
  · rintro ⟨h_com, h_comp⟩; exact h_comp.2.1 h_com.2.1
  · rintro ⟨h_com, h_aut⟩; exact h_aut.2.1 h_com.2.1
  · rintro ⟨h_com, h_gift⟩; exact h_gift.2.1 h_com.2.1
  · rintro ⟨h_com, h_dest⟩; exact h_dest.2.2.2.2 h_com.1
  · rintro ⟨h_com, h_rec⟩; exact W.pref_asymm j t h h_rec.2.2.2 h_com.2.2.2.2
  · rintro ⟨h_cf, h_vol⟩; exact W.pref_asymm i t h h_vol.2.2.1 h_cf.2.2.1
  · rintro ⟨h_cf, h_ext⟩; exact h_cf.2.1 h_ext.1
  · rintro ⟨h_cf, h_comp⟩; exact h_cf.2.2.2.2 h_comp.2.2.1
  · rintro ⟨h_cf, h_aut⟩
    have h_p := h_cf.2.2.1
    rw [h_aut.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_cf, h_gift⟩; exact W.pref_asymm i t h h_gift.2.2.1 h_cf.2.2.1
  · rintro ⟨h_cf, h_dest⟩; exact h_cf.2.1 h_dest.1
  · rintro ⟨h_cf, h_rec⟩; exact h_cf.2.1 h_rec.1
  · rintro ⟨h_cf, h_com⟩; exact h_cf.2.1 h_com.2.1
  · rintro ⟨h_in, h_vol⟩
    have h_p := h_vol.2.2.1
    rw [h_in.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_in, h_ext⟩; exact h_in.2.1 h_ext.1
  · rintro ⟨h_in, h_comp⟩
    have h_p := h_comp.2.2.2
    rw [h_in.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_in, h_aut⟩
    have h_p := h_aut.2.2.2
    rw [h_in.2.2.2] at h_p
    exact W.pref_irrefl j t h _ h_p
  · rintro ⟨h_in, h_gift⟩
    have h_p := h_gift.2.2.1
    rw [h_in.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p
  · rintro ⟨h_in, h_dest⟩; exact h_in.2.1 h_dest.1
  · rintro ⟨h_in, h_rec⟩; exact h_in.2.1 h_rec.1
  · rintro ⟨h_in, h_com⟩; exact h_in.2.1 h_com.2.1
  · rintro ⟨h_in, h_cf⟩
    have h_p := h_cf.2.2.1
    rw [h_in.2.2.1] at h_p
    exact W.pref_irrefl i t h _ h_p

theorem endogenous_invasion_iff_menu_stripping
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (h_rich : ∀ m : W.Means, ∃ β, (∀ m', W.use_means β m' ≤ W.omega i t h m') ∧
      W.use_means β m = W.omega i t h m)
    (α_j : W.Action) :
    EndogenouslyInvasiveJ i j t h α_j ↔ MenuStrippingInvasiveJ i j t h α_j := by
  constructor
  · rintro ⟨m_inv, h_contract⟩
    obtain ⟨β, h_title, h_tight⟩ := h_rich m_inv
    refine ⟨β, h_title, ?_⟩
    intro h_feas
    have h_le := h_feas m_inv
    rw [h_tight] at h_le
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_contract h_le)
  · rintro ⟨β, h_title, h_infeas⟩
    by_contra h_not_inv
    apply h_infeas
    intro m
    have h_not_lt :
        ¬ W.omega i
            (W.ExpectedMaturation i W.alpha_zero t
              (jointBranch i j t h W.alpha_zero α_j))
            (jointBranch i j t h W.alpha_zero α_j) m < W.omega i t h m := by
      intro h_lt
      exact h_not_inv ⟨m, h_lt⟩
    have h_ge : W.omega i t h m ≤ W.omega i
        (W.ExpectedMaturation i W.alpha_zero t
          (jointBranch i j t h W.alpha_zero α_j))
        (jointBranch i j t h W.alpha_zero α_j) m :=
      Nat.le_of_not_lt h_not_lt
    exact le_trans (h_title m) h_ge

theorem peaceful_competition_preserves_stock_and_menu
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (α_i α_comp : W.Action)
    (h_comp : IsMarketCompetition i j t h α_i α_comp) :
    ¬ EndogenouslyInvasiveJ i j t h α_comp ∧
    (∀ m, W.omega i t h m ≤ W.omega i
      (W.ExpectedMaturation i W.alpha_zero t
        (jointBranch i j t h W.alpha_zero α_comp))
      (jointBranch i j t h W.alpha_zero α_comp) m) ∧
    (∀ β, (∀ m, W.use_means β m ≤ W.omega i t h m) →
      (∀ m, W.use_means β m ≤ W.omega i
        (W.ExpectedMaturation i W.alpha_zero t
          (jointBranch i j t h W.alpha_zero α_comp))
        (jointBranch i j t h W.alpha_zero α_comp) m)) ∧
    W.Preference i t h (jointEndI i j t h W.alpha_zero W.alpha_zero)
      (jointEndI i j t h α_i α_comp) := by
  have h_not_inv := h_comp.2.1
  have h_pref := h_comp.2.2.2
  have h_pres :
      ∀ m, W.omega i t h m ≤ W.omega i
        (W.ExpectedMaturation i W.alpha_zero t
          (jointBranch i j t h W.alpha_zero α_comp))
        (jointBranch i j t h W.alpha_zero α_comp) m := by
    intro m
    by_contra h_lt
    exact h_not_inv ⟨m, Nat.lt_of_not_ge h_lt⟩
  refine ⟨h_not_inv, h_pres, ?_, h_pref⟩
  intro β h_feas_title m
  exact le_trans (h_feas_title m) (h_pres m)

/-- Autonomous precommitment vs external menu stripping:
an agent's own prior precommitment prunes temptation from their own menu,
whereas external invasion by another agent contracts clean-title stocks
and strips previously feasible actions from the victim's choice menu. -/
theorem self_precommitment_vs_external_menu_stripping
    [W : ActionFrame] {i j : W.Agent} {t : W.Moment} {h : W.History}
    (h_ij : i ≠ j) (ht : W.mem_hist t h)
    (α_tax : W.Action)
    (h_feas_tax : α_tax ∈ W.A_feas j t (W.sigma i t W.alpha_zero h))
    (h_rich : ∀ m : W.Means, ∃ β, (∀ m', W.use_means β m' ≤ W.omega i t h m') ∧
      W.use_means β m = W.omega i t h m)
    (h_invasive : EndogenouslyInvasiveJ i j t h α_tax) :
    let branch := jointBranch i j t h W.alpha_zero α_tax
    (∃ m : W.Means, W.omega i (W.ExpectedMaturation i W.alpha_zero t branch) branch m <
      W.omega i t h m) ∧
    MenuStrippingInvasiveJ i j t h α_tax ∧
    W.mem_hist t branch ∧
    W.enacted i t branch = W.alpha_zero ∧
    W.enacted j t branch = α_tax := by
  intro branch
  have h_pair := jointBranch_realizes_pair i j t h W.alpha_zero α_tax h_ij ht
    (W.alpha_zero_feasible i t h) h_feas_tax
  have h_menu := (endogenous_invasion_iff_menu_stripping h_rich α_tax).mp h_invasive
  exact ⟨h_invasive, h_menu, h_pair.1, h_pair.2.1, h_pair.2.2⟩


structure RicardianEconomy where
  L_i : ℕ
  L_j : ℕ
  a_i : Fin 2 → ℕ
  a_j : Fin 2 → ℕ
  h_pos_Li : 0 < L_i
  h_pos_Lj : 0 < L_j
  h_pos_ai : ∀ g : Fin 2, 0 < a_i g
  h_pos_aj : ∀ g : Fin 2, 0 < a_j g
  h_comp_adv : a_i 0 * a_j 1 < a_j 0 * a_i 1

/-- A production certificate accounts for every unit of labor, including the
unused remainder. -/
structure RicardianProduction (labor : ℕ) (requirements : Fin 2 → ℕ) where
  output : ℕ × ℕ
  unusedLabor : ℕ
  laborBalance : output.1 * requirements 0 + output.2 * requirements 1 +
    unusedLabor = labor

/-- A Ricardian plan contains certified autarky and pre-exchange production,
the transfers, the resulting bundles, and all four exact commodity balances. -/
structure RicardianTradePlan (E : RicardianEconomy) where
  baselineI : RicardianProduction E.L_i E.a_i
  baselineJ : RicardianProduction E.L_j E.a_j
  producedI : RicardianProduction E.L_i E.a_i
  producedJ : RicardianProduction E.L_j E.a_j
  x0 : ℕ
  x1 : ℕ
  afterI : ℕ × ℕ
  afterJ : ℕ × ℕ
  afterI_good0_balance : afterI.1 + x0 = producedI.output.1
  afterI_good1_balance : afterI.2 = producedI.output.2 + x1
  afterJ_good0_balance : afterJ.1 = producedJ.output.1 + x0
  afterJ_good1_balance : afterJ.2 + x1 = producedJ.output.2

/-- `b1` has at least as much of each good as `b2` and more of one good. -/
def PairBundleDominates (b1 b2 : ℕ × ℕ) : Prop :=
  b1.1 ≥ b2.1 ∧ b1.2 ≥ b2.2 ∧ (b1.1 > b2.1 ∨ b1.2 > b2.2)

/-- Both traders weakly retain each baseline good and strictly gain at least
one good. -/
structure RicardianTradeGains {E : RicardianEconomy} (P : RicardianTradePlan E) : Prop where
  agentI : PairBundleDominates P.afterI P.baselineI.output
  agentJ : PairBundleDominates P.afterJ P.baselineJ.output

/-- Comparative advantage yields integer production and trade plans whenever
labor endowments cover the stated cross-multiplied requirements. The theorem
needs sufficient labor, not an exact multiple that would erase remainders. -/
theorem ricardian_comparative_advantage_universal
    (E : RicardianEconomy)
    (h_Li : 2 * (E.a_i 0 * E.a_j 0) * E.a_i 1 ≤ E.L_i)
    (h_Lj : 2 * (E.a_i 0 * E.a_j 1) * E.a_j 0 ≤ E.L_j) :
    ∃ P : RicardianTradePlan E, RicardianTradeGains P := by
  let ai0 := E.a_i 0
  let ai1 := E.a_i 1
  let aj0 := E.a_j 0
  let aj1 := E.a_j 1
  have h_ai0 : 0 < ai0 := E.h_pos_ai 0
  have h_ai1 : 0 < ai1 := E.h_pos_ai 1
  have h_aj0 : 0 < aj0 := E.h_pos_aj 0
  have h_aj1 : 0 < aj1 := E.h_pos_aj 1
  have h_comp : ai0 * aj1 < aj0 * ai1 := E.h_comp_adv
  let K := ai0 * aj0
  let C_lo := ai0 * aj1
  let C_hi := aj0 * ai1
  let gainRemainder := NatRemainder.ofLE C_hi C_lo (Nat.le_of_lt h_comp)
  let δ := gainRemainder.remaining
  have h_gain_positive : 0 < δ := (NatRemainder.remaining_pos_iff gainRemainder).2 h_comp
  have h_gain_balance : C_lo + δ = C_hi := gainRemainder.balance
  have h_i_baseline_labor : 0 * ai0 + (2 * K) * ai1 = 2 * K * ai1 := by ring
  have h_i_produced_labor : (2 * C_hi) * ai0 + 0 * ai1 = 2 * K * ai1 := by
    dsimp [C_hi, K, ai0, ai1, aj0]
    ring
  have h_j_baseline_labor : (2 * C_lo) * aj0 + 0 * aj1 = 2 * C_lo * aj0 := by ring
  have h_j_produced_labor : 0 * aj0 + (2 * K) * aj1 = 2 * C_lo * aj0 := by
    dsimp [C_lo, K, ai0, aj0, aj1]
    ring
  let iLaborRemainder := NatRemainder.ofLE E.L_i (2 * K * ai1) (by
    simpa [K, ai0, ai1, aj0, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h_Li)
  let jLaborRemainder := NatRemainder.ofLE E.L_j (2 * C_lo * aj0) (by
    simpa [C_lo, ai0, aj0, aj1, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h_Lj)
  let baselineI : RicardianProduction E.L_i E.a_i := {
    output := (0, 2 * K)
    unusedLabor := iLaborRemainder.remaining
    laborBalance := by
      dsimp [iLaborRemainder]
      rw [h_i_baseline_labor]
      exact NatRemainder.balance _
  }
  let baselineJ : RicardianProduction E.L_j E.a_j := {
    output := (2 * C_lo, 0)
    unusedLabor := jLaborRemainder.remaining
    laborBalance := by
      dsimp [jLaborRemainder]
      rw [h_j_baseline_labor]
      exact NatRemainder.balance _
  }
  let producedI : RicardianProduction E.L_i E.a_i := {
    output := (2 * C_hi, 0)
    unusedLabor := iLaborRemainder.remaining
    laborBalance := by
      dsimp [iLaborRemainder]
      rw [h_i_produced_labor]
      exact NatRemainder.balance _
  }
  let producedJ : RicardianProduction E.L_j E.a_j := {
    output := (0, 2 * K)
    unusedLabor := jLaborRemainder.remaining
    laborBalance := by
      dsimp [jLaborRemainder]
      rw [h_j_produced_labor]
      exact NatRemainder.balance _
  }
  let P : RicardianTradePlan E := {
    baselineI := baselineI
    baselineJ := baselineJ
    producedI := producedI
    producedJ := producedJ
    x0 := C_hi + C_lo
    x1 := 2 * K
    afterI := (δ, 2 * K)
    afterJ := (2 * C_lo + δ, 0)
    afterI_good0_balance := by
      dsimp [C_hi, C_lo]
      dsimp [producedI]
      omega
    afterI_good1_balance := by
      change 2 * K = 0 + 2 * K
      omega
    afterJ_good0_balance := by
      dsimp [C_hi, C_lo]
      dsimp [producedJ]
      omega
    afterJ_good1_balance := by
      change 0 + 2 * K = 2 * K
      omega
  }
  refine ⟨P, ?_⟩
  constructor
  · dsimp [PairBundleDominates, P, baselineI]
    exact ⟨Nat.zero_le _, by rfl, Or.inl h_gain_positive⟩
  · dsimp [PairBundleDominates, P, baselineJ]
    have h_j_gain : 2 * C_lo < 2 * C_lo + δ := by omega
    exact ⟨by omega, by rfl, Or.inl h_j_gain⟩


theorem mises_law_of_association_universal
    (a_i a_j : Fin 2 → ℕ)
    (h_pos_i : ∀ g, 0 < a_i g) (h_pos_j : ∀ g, 0 < a_j g)
    (h_comp : a_i 0 * a_j 1 < a_j 0 * a_i 1) :
    ∃ (E : RicardianEconomy) (P : RicardianTradePlan E),
      RicardianTradeGains P := by
  let E : RicardianEconomy := {
    L_i := 4 * a_i 0 * a_i 1 * a_j 0
    L_j := 4 * a_i 0 * a_j 1 * a_j 0
    a_i := a_i
    a_j := a_j
    h_pos_Li := by
      have h0 := h_pos_i 0
      have h1 := h_pos_i 1
      have h2 := h_pos_j 0
      positivity
    h_pos_Lj := by
      have h0 := h_pos_i 0
      have h1 := h_pos_j 1
      have h2 := h_pos_j 0
      positivity
    h_pos_ai := h_pos_i
    h_pos_aj := h_pos_j
    h_comp_adv := h_comp
  }
  obtain ⟨P, h_gains⟩ := ricardian_comparative_advantage_universal E
    (by dsimp [E]; ring_nf; omega) (by dsimp [E]; ring_nf; omega)
  exact ⟨E, P, h_gains⟩


def TwoSectorRicardianEconomy : RicardianEconomy where
  L_i := 120
  L_j := 240
  a_i := fun g => if g = 0 then 1 else 2
  a_j := fun g => if g = 0 then 6 else 3
  h_pos_Li := by decide
  h_pos_Lj := by decide
  h_pos_ai := by intro g; revert g; decide
  h_pos_aj := by intro g; revert g; decide
  h_comp_adv := by decide


theorem mises_law_of_association_under_absolute_advantage :
    ∃ (P : RicardianTradePlan TwoSectorRicardianEconomy),
      (∀ g : Fin 2, TwoSectorRicardianEconomy.a_i g < TwoSectorRicardianEconomy.a_j g) ∧
      RicardianTradeGains P := by
  have h_Li : 2 * (TwoSectorRicardianEconomy.a_i 0 * TwoSectorRicardianEconomy.a_j 0) *
      TwoSectorRicardianEconomy.a_i 1 ≤ TwoSectorRicardianEconomy.L_i := by decide
  have h_Lj : 2 * (TwoSectorRicardianEconomy.a_i 0 * TwoSectorRicardianEconomy.a_j 1) *
      TwoSectorRicardianEconomy.a_j 0 ≤ TwoSectorRicardianEconomy.L_j := by decide
  obtain ⟨P, h_cat⟩ := ricardian_comparative_advantage_universal
    TwoSectorRicardianEconomy h_Li h_Lj
  refine ⟨P, ?_, h_cat⟩
  intro g
  revert g
  decide

/-- A comparative-advantage economy with one unit of unused labor for each
trader.  The explicit plan records the same output as the tight example while
preserving each labor remainder. -/
def RicardianSlackEconomy : RicardianEconomy where
  L_i := 37
  L_j := 25
  a_i := fun g => if g = 0 then 2 else 3
  a_j := fun g => if g = 0 then 3 else 2
  h_pos_Li := by decide
  h_pos_Lj := by decide
  h_pos_ai := by intro g; fin_cases g <;> decide
  h_pos_aj := by intro g; fin_cases g <;> decide
  h_comp_adv := by decide

/-- Regression witness for nonzero unused labor. -/
def RicardianSlackPlan : RicardianTradePlan RicardianSlackEconomy where
  baselineI := ⟨(0, 12), 1, by decide⟩
  baselineJ := ⟨(8, 0), 1, by decide⟩
  producedI := ⟨(18, 0), 1, by decide⟩
  producedJ := ⟨(0, 12), 1, by decide⟩
  x0 := 13
  x1 := 12
  afterI := (5, 12)
  afterJ := (13, 0)
  afterI_good0_balance := by decide
  afterI_good1_balance := by decide
  afterJ_good0_balance := by decide
  afterJ_good1_balance := by decide

theorem ricardian_slack_plan_gains :
    RicardianTradeGains RicardianSlackPlan := by
  constructor <;> dsimp [PairBundleDominates, RicardianSlackPlan,
    RicardianSlackEconomy] <;> decide

/-- At the exact labor threshold, no unused labor is silently lost. -/
def RicardianTightEconomy : RicardianEconomy where
  L_i := 36
  L_j := 24
  a_i := fun g => if g = 0 then 2 else 3
  a_j := fun g => if g = 0 then 3 else 2
  h_pos_Li := by decide
  h_pos_Lj := by decide
  h_pos_ai := by intro g; fin_cases g <;> decide
  h_pos_aj := by intro g; fin_cases g <;> decide
  h_comp_adv := by decide

def RicardianTightPlan : RicardianTradePlan RicardianTightEconomy where
  baselineI := ⟨(0, 12), 0, by decide⟩
  baselineJ := ⟨(8, 0), 0, by decide⟩
  producedI := ⟨(18, 0), 0, by decide⟩
  producedJ := ⟨(0, 12), 0, by decide⟩
  x0 := 13
  x1 := 12
  afterI := (5, 12)
  afterJ := (13, 0)
  afterI_good0_balance := by decide
  afterI_good1_balance := by decide
  afterJ_good0_balance := by decide
  afterJ_good1_balance := by decide

theorem ricardian_tight_plan_gains :
    RicardianTradeGains RicardianTightPlan := by
  constructor <;> dsimp [PairBundleDominates, RicardianTightPlan,
    RicardianTightEconomy] <;> decide

/-- Below the minimum labor needed for the stated specialized output, an exact
production certificate cannot exist. This catches accidental floor-division
or truncated-subtraction loss at the boundary. -/
theorem ricardian_below_threshold_specialization_impossible :
    ¬ ∃ unused : ℕ, 18 * 2 + 0 * 3 + unused = 35 := by omega

/-- An exchange example where `a_i` is below `a_j` for both goods. -/
theorem mises_law_of_association_non_vacuous :
    ∃ (E : RicardianEconomy) (P : RicardianTradePlan E),
      (∀ g : Fin 2, E.a_i g < E.a_j g) ∧
      RicardianTradeGains P := by
  obtain ⟨P, h_abs, h_gains⟩ := mises_law_of_association_under_absolute_advantage
  exact ⟨TwoSectorRicardianEconomy, P, h_abs, h_gains⟩


theorem no_ricardian_surplus_of_equal_opportunity_costs
    (a_i a_j : Fin 2 → ℕ)
    (h_pos_ai : ∀ g, 0 < a_i g) (h_pos_aj : ∀ g, 0 < a_j g)
    (h_equal_opp : a_i 0 * a_j 1 = a_j 0 * a_i 1)
    (x0 x1 r_i s_j : ℕ)
    (h_i_g0 : x0 * a_i 0 ≤ r_i * a_i 1)
    (h_i_g1 : r_i ≤ x1)
    (h_j_g0 : s_j ≤ x0)
    (h_j_g1 : x1 * a_j 1 ≤ s_j * a_j 0)
    (h_strict_i : x0 * a_i 0 < r_i * a_i 1 ∨ r_i < x1) :
    False := by
  have h_le_i : x0 * a_i 0 ≤ x1 * a_i 1 :=
    le_trans h_i_g0 (Nat.mul_le_mul_right (a_i 1) h_i_g1)
  have h_le_j : x1 * a_j 1 ≤ x0 * a_j 0 :=
    le_trans h_j_g1 (Nat.mul_le_mul_right (a_j 0) h_j_g0)
  have h1 : x0 * a_i 0 * a_j 1 ≤ x1 * a_i 1 * a_j 1 :=
    Nat.mul_le_mul_right (a_j 1) h_le_i
  have h2 : x1 * a_j 1 * a_i 1 ≤ x0 * a_j 0 * a_i 1 :=
    Nat.mul_le_mul_right (a_i 1) h_le_j
  have h_eq1 : x0 * a_i 0 * a_j 1 = x0 * (a_i 0 * a_j 1) := by ring
  have h_eq2 : x0 * a_j 0 * a_i 1 = x0 * (a_j 0 * a_i 1) := by ring
  have h_eq3 : x1 * a_i 1 * a_j 1 = x1 * a_j 1 * a_i 1 := by ring
  have h_strict : x0 * a_i 0 < x1 * a_i 1 := by
    rcases h_strict_i with h_lt0 | h_lt1
    · exact lt_of_lt_of_le h_lt0 (Nat.mul_le_mul_right (a_i 1) h_i_g1)
    · have h_lt : r_i * a_i 1 < x1 * a_i 1 := Nat.mul_lt_mul_of_pos_right h_lt1 (h_pos_ai 1)
      exact lt_of_le_of_lt h_i_g0 h_lt
  have h_strict_mul : x0 * a_i 0 * a_j 1 < x1 * a_i 1 * a_j 1 :=
    Nat.mul_lt_mul_of_pos_right h_strict (h_pos_aj 1)
  rw [h_eq1, h_equal_opp, ← h_eq2, h_eq3] at h_strict_mul
  omega


/-- Named data and certificates for the one-sided surplus result. The
producer's labor balances, transfers, post-trade balances, private gain, and
aggregate surplus can be consumed independently by later proofs. -/
structure RicardianSurplusCertificate
    (a_i a_j : Fin 2 → ℕ) (q_i q_j : ℕ × ℕ) where
  producedI : ℕ × ℕ
  producedJ : ℕ × ℕ
  x0 : ℕ
  x1 : ℕ
  afterI : ℕ × ℕ
  afterJ : ℕ × ℕ
  laborI : producedI.1 * a_i 0 + producedI.2 * a_i 1 =
    q_i.1 * a_i 0 + q_i.2 * a_i 1
  laborJ : producedJ.1 * a_j 0 + producedJ.2 * a_j 1 =
    q_j.1 * a_j 0 + q_j.2 * a_j 1
  good0TransferCovered : x0 ≤ producedI.1
  good1TransferCovered : x1 ≤ producedJ.2
  positiveGood0Production : 0 < producedI.1
  positiveGood1Production : 0 < producedJ.2
  producedI_good1_balance : a_i 0 * a_j 0 + producedI.2 = q_i.2
  producedJ_good0_balance : a_i 0 * a_j 1 + producedJ.1 = q_j.1
  afterI_good0_balance : afterI.1 + x0 = producedI.1
  afterI_good1_balance : afterI.2 = producedI.2 + x1
  afterJ_good0_balance : afterJ.1 = producedJ.1 + x0
  afterJ_good1_balance : afterJ.2 + x1 = producedJ.2
  agentIGains : PairBundleDominates afterI q_i
  agentJUnchanged : afterJ = q_j
  aggregateGood0Surplus : afterI.1 + afterJ.1 > q_i.1 + q_j.1
  aggregateGood1Conserved : afterI.2 + afterJ.2 = q_i.2 + q_j.2

def ricardian_surplus_of_any_positive_autarky
    (a_i a_j : Fin 2 → ℕ)
    (h_pos_ai : ∀ g, 0 < a_i g) (h_pos_aj : ∀ g, 0 < a_j g)
    (h_comp : a_i 0 * a_j 1 < a_j 0 * a_i 1)
    (q_i0 q_i1 q_j0 q_j1 : ℕ)
    (h_autarky_i1 : a_i 0 * a_j 0 ≤ q_i1)
    (h_autarky_j0 : a_i 0 * a_j 1 ≤ q_j0) :
    RicardianSurplusCertificate a_i a_j (q_i0, q_i1) (q_j0, q_j1) := by
  let prod_i1_remainder := NatRemainder.ofLE q_i1 (a_i 0 * a_j 0) h_autarky_i1
  let prod_j0_remainder := NatRemainder.ofLE q_j0 (a_i 0 * a_j 1) h_autarky_j0
  let gain0_remainder := NatRemainder.ofLE (a_j 0 * a_i 1) (a_i 0 * a_j 1)
    (Nat.le_of_lt h_comp)
  let q_prod_i0 := q_i0 + a_j 0 * a_i 1
  let q_prod_i1 := prod_i1_remainder.remaining
  let q_prod_j0 := prod_j0_remainder.remaining
  let q_prod_j1 := q_j1 + a_i 0 * a_j 0
  let x0 := a_i 0 * a_j 1
  let x1 := a_i 0 * a_j 0
  have h_x0_le : x0 ≤ q_prod_i0 := by
    dsimp [x0, q_prod_i0]
    omega
  have h_x1_le : x1 ≤ q_prod_j1 := by
    dsimp [x1, q_prod_j1]
    omega
  let post_i0_remainder := NatRemainder.ofLE q_prod_i0 x0 h_x0_le
  let post_j1_remainder := NatRemainder.ofLE q_prod_j1 x1 h_x1_le
  let q_post_i0 := post_i0_remainder.remaining
  let q_post_i1 := q_prod_i1 + x1
  let q_post_j0 := q_prod_j0 + x0
  let q_post_j1 := post_j1_remainder.remaining
  have h_prod_i1_balance : a_i 0 * a_j 0 + q_prod_i1 = q_i1 := by
    exact prod_i1_remainder.balance
  have h_prod_j0_balance : a_i 0 * a_j 1 + q_prod_j0 = q_j0 := by
    exact prod_j0_remainder.balance
  have h_i_multiplier_balance :
      q_prod_i1 * a_i 1 + (a_i 0 * a_j 0) * a_i 1 = q_i1 * a_i 1 := by
    calc
      q_prod_i1 * a_i 1 + (a_i 0 * a_j 0) * a_i 1 =
          (q_prod_i1 + a_i 0 * a_j 0) * a_i 1 := by rw [Nat.add_mul]
      _ = q_i1 * a_i 1 := by rw [show q_prod_i1 + a_i 0 * a_j 0 = q_i1 by omega]
  have h_labor_i :
      q_prod_i0 * a_i 0 + q_prod_i1 * a_i 1 = q_i0 * a_i 0 + q_i1 * a_i 1 := by
    dsimp [q_prod_i0]
    calc
      (q_i0 + a_j 0 * a_i 1) * a_i 0 + q_prod_i1 * a_i 1 =
          q_i0 * a_i 0 + ((a_i 0 * a_j 0) * a_i 1 + q_prod_i1 * a_i 1) := by ring
      _ = q_i0 * a_i 0 + q_i1 * a_i 1 := by
        rw [add_comm ((a_i 0 * a_j 0) * a_i 1) (q_prod_i1 * a_i 1), h_i_multiplier_balance]
  have h_j_multiplier_balance :
      q_prod_j0 * a_j 0 + x0 * a_j 0 = q_j0 * a_j 0 := by
    have h_commuted : q_prod_j0 + x0 = q_j0 := by
      dsimp [q_prod_j0, x0]
      omega
    calc
      q_prod_j0 * a_j 0 + x0 * a_j 0 = (q_prod_j0 + x0) * a_j 0 := by rw [Nat.add_mul]
      _ = q_j0 * a_j 0 := by rw [h_commuted]
  have h_j_offset : (a_i 0 * a_j 0) * a_j 1 = x0 * a_j 0 := by
    dsimp [x0]
    ring
  have h_labor_j :
      q_prod_j0 * a_j 0 + q_prod_j1 * a_j 1 = q_j0 * a_j 0 + q_j1 * a_j 1 := by
    dsimp [q_prod_j1]
    nlinarith [h_j_multiplier_balance, h_j_offset]
  have h_pos_prod_i0 : 0 < q_prod_i0 := by
    dsimp [q_prod_i0]
    have h1 := h_pos_aj 0
    have h2 := h_pos_ai 1
    have hproduct : 0 < a_j 0 * a_i 1 := Nat.mul_pos h1 h2
    omega
  have h_pos_prod_j1 : 0 < q_prod_j1 := by
    dsimp [q_prod_j1]
    have h1 := h_pos_ai 0
    have h2 := h_pos_aj 0
    have hproduct : 0 < a_i 0 * a_j 0 := Nat.mul_pos h1 h2
    omega
  have h_post_i0_gain : q_post_i0 = q_i0 + gain0_remainder.remaining := by
    have h_post := post_i0_remainder.balance
    have h_gain := gain0_remainder.balance
    change x0 + q_post_i0 = q_prod_i0 at h_post
    change x0 + gain0_remainder.remaining = a_j 0 * a_i 1 at h_gain
    dsimp [q_prod_i0] at h_post
    omega
  have h_post_i0_balance : q_post_i0 + x0 = q_prod_i0 := by
    have h_post := post_i0_remainder.balance
    change x0 + q_post_i0 = q_prod_i0 at h_post
    omega
  have h_post_i1_eq : q_post_i1 = q_i1 := by
    dsimp [q_post_i1]
    omega
  have h_post_j0_eq : q_post_j0 = q_j0 := by
    dsimp [q_post_j0]
    omega
  have h_post_j1_eq : q_post_j1 = q_j1 := by
    have h_post := post_j1_remainder.balance
    change x1 + q_post_j1 = q_prod_j1 at h_post
    dsimp [q_prod_j1, x1] at h_post
    omega
  have h_post_j1_balance : q_post_j1 + x1 = q_prod_j1 := by
    have h_post := post_j1_remainder.balance
    change x1 + q_post_j1 = q_prod_j1 at h_post
    omega
  have h_gain_pos : 0 < gain0_remainder.remaining :=
    (NatRemainder.remaining_pos_iff gain0_remainder).2 h_comp
  have h_gain_i : PairBundleDominates (q_post_i0, q_post_i1) (q_i0, q_i1) := by
    dsimp [PairBundleDominates]
    rw [h_post_i0_gain, h_post_i1_eq]
    exact ⟨by omega, by omega, Or.inl (by omega)⟩
  have h_gain_j : (q_post_j0, q_post_j1) = (q_j0, q_j1) := by
    rw [h_post_j0_eq, h_post_j1_eq]
  have h_total_good0 : q_post_i0 + q_post_j0 > q_i0 + q_j0 := by
    rw [h_post_i0_gain, h_post_j0_eq]
    omega
  have h_total_good1 : q_post_i1 + q_post_j1 = q_i1 + q_j1 := by
    rw [h_post_i1_eq, h_post_j1_eq]
  exact {
    producedI := (q_prod_i0, q_prod_i1)
    producedJ := (q_prod_j0, q_prod_j1)
    x0 := x0
    x1 := x1
    afterI := (q_post_i0, q_post_i1)
    afterJ := (q_post_j0, q_post_j1)
    laborI := h_labor_i
    laborJ := h_labor_j
    good0TransferCovered := h_x0_le
    good1TransferCovered := h_x1_le
    positiveGood0Production := h_pos_prod_i0
    positiveGood1Production := h_pos_prod_j1
    producedI_good1_balance := h_prod_i1_balance
    producedJ_good0_balance := h_prod_j0_balance
    afterI_good0_balance := h_post_i0_balance
    afterI_good1_balance := rfl
    afterJ_good0_balance := rfl
    afterJ_good1_balance := h_post_j1_balance
    agentIGains := h_gain_i
    agentJUnchanged := h_gain_j
    aggregateGood0Surplus := h_total_good0
    aggregateGood1Conserved := h_total_good1 }
theorem ricardian_terms_of_trade_interval
    (a_i a_j : Fin 2 → ℕ)
    (h_pos_ai : ∀ g, 0 < a_i g) (h_pos_aj : ∀ g, 0 < a_j g)
    (h_comp : a_i 0 * a_j 1 < a_j 0 * a_i 1) :
    ∃ (x0 x1 : ℕ),
      0 < x0 ∧ 0 < x1 ∧
      x0 * a_i 0 < x1 * a_i 1 ∧
      x1 * a_j 1 < x0 * a_j 0 := by
  let x0 := 2 * a_i 1 * a_j 1
  let x1 := a_i 0 * a_j 1 + a_j 0 * a_i 1
  have h_x0_pos : 0 < x0 := by
    dsimp [x0]
    have h1 := h_pos_ai 1
    have h2 := h_pos_aj 1
    have h_2ai : 0 < 2 * a_i 1 := Nat.mul_pos (by decide : 0 < 2) h1
    exact Nat.mul_pos h_2ai h2
  have h_x1_pos : 0 < x1 := by
    dsimp [x1]
    have h1 := h_pos_ai 0
    have h2 := h_pos_aj 1
    have : 0 < a_i 0 * a_j 1 := Nat.mul_pos h1 h2
    omega
  have h_i : x0 * a_i 0 < x1 * a_i 1 := by
    dsimp [x0, x1]
    have h_step : 2 * (a_i 0 * a_j 1) < a_i 0 * a_j 1 + a_j 0 * a_i 1 := by omega
    have h_mul : 2 * (a_i 0 * a_j 1) * a_i 1 < (a_i 0 * a_j 1 + a_j 0 * a_i 1) * a_i 1 :=
      Nat.mul_lt_mul_of_pos_right h_step (h_pos_ai 1)
    have h_left : 2 * a_i 1 * a_j 1 * a_i 0 = 2 * (a_i 0 * a_j 1) * a_i 1 := by ring
    rw [h_left]
    exact h_mul
  have h_j : x1 * a_j 1 < x0 * a_j 0 := by
    dsimp [x0, x1]
    have h_step : a_i 0 * a_j 1 + a_j 0 * a_i 1 < 2 * (a_j 0 * a_i 1) := by omega
    have h_mul : (a_i 0 * a_j 1 + a_j 0 * a_i 1) * a_j 1 < 2 * (a_j 0 * a_i 1) * a_j 1 :=
      Nat.mul_lt_mul_of_pos_right h_step (h_pos_aj 1)
    have h_right : 2 * a_i 1 * a_j 1 * a_j 0 = 2 * (a_j 0 * a_i 1) * a_j 1 := by ring
    rw [h_right]
    exact h_mul
  exact ⟨x0, x1, h_x0_pos, h_x1_pos, h_i, h_j⟩


-- Section 1b: Bilateral Exchange in ActionFrame


section BilateralActionFrameCatallactics

variable [W : ActionFrame]

/-- Action `α_j` enacted by `j` at `⟨t, h⟩` is invasive against `i` along transition `t → t'`
if executing `α_j` while `i` is passive (`α₀`, without consent) contracts `i`'s physical stock
of some means below clean title. -/
def IsActionFrameInvasion (i j : Agent) (t t' : Moment) (h : History)
    (title_i : Means → ℕ) (α_j : Action) : Prop :=
  ∃ m : Means, omega i t' (jointBranch i j t h α₀ α_j) m < title_i m ∧
    omega i t' (jointBranch i j t h α₀ α_j) m < omega i t h m

/-- Action-Axiom Menu-Stripping: Physical invasion by `j` against `i` strictly contracts `i`'s
clean-title stock and strips tight contemplated actions from `i`'s feasible menu. -/
theorem actionFrame_invasion_strips_feasible_menu
    (i j : Agent) (t t' : Moment) (h : History)
    (title : Agent → Means → ℕ) (α_j : Action) (m_inv : Means) (β : Action)
    (h_clean : title i m_inv ≤ omega i t (jointBranch i j t h α₀ α_j) m_inv)
    (h_contract : omega i t' (jointBranch i j t h α₀ α_j) m_inv < title i m_inv)
    (h_feas : β ∈ A_feas i t (jointBranch i j t h α₀ α_j))
    (h_cont : β ∈ A_cont i t' (jointBranch i j t h α₀ α_j))
    (h_tight : use_means β m_inv = title i m_inv) :
    FeasibleMenuStripped i t t' (jointBranch i j t h α₀ α_j) β ∧
    IsPathDependentTitleInvasion title i t t'
      (jointBranch i j t h α₀ α_j) m_inv := by
  have h_menu_stripped :
      FeasibleMenuStripped i t t' (jointBranch i j t h α₀ α_j) β := by
    refine ⟨h_feas, h_cont, ?_⟩
    intro h_feas'
    have h_le :=
      (W.A_feas_coupling i t' (jointBranch i j t h α₀ α_j) β).mp h_feas' |>.2 m_inv
    dsimp [use_means, omega] at *
    rw [h_tight] at h_le
    omega
  refine ⟨h_menu_stripped, ?_⟩
  dsimp [IsPathDependentTitleInvasion]
  exact ⟨h_contract, lt_of_lt_of_le h_contract h_clean⟩

theorem actionFrame_invasion_strips_menu_of_history
    (i j : Agent) (t t' : Moment) (h : History)
    (title : Agent → Means → ℕ) (α_j : Action) (m_inv : Means) (β : Action)
    (ht : mem_hist t h)
    (ht_branch : mem_hist t (jointBranch i j t h α₀ α_j))
    (h_clean : ∀ m, title i m ≤ omega i t h m)
    (h_contract : omega i t' (jointBranch i j t h α₀ α_j) m_inv < title i m_inv)
    (h_feas : β ∈ A_feas i t h)
    (h_cont : β ∈ A_cont i t' (jointBranch i j t h α₀ α_j))
    (h_tight : use_means β m_inv = title i m_inv) :
    FeasibleMenuStripped i t t' (jointBranch i j t h α₀ α_j) β ∧
    IsPathDependentTitleInvasion title i t t'
      (jointBranch i j t h α₀ α_j) m_inv := by
  have h_feas_joint : β ∈ A_feas i t (jointBranch i j t h α₀ α_j) := by
    have h_eq : A_feas i t (jointBranch i j t h α₀ α_j) = A_feas i t h :=
      A_feas_bundle_invariant i t ht_branch ht
    rwa [h_eq]
  have h_clean_branch : title i m_inv ≤ omega i t (jointBranch i j t h α₀ α_j) m_inv := by
    have h_omega := W.omega_bundle_invariant i t m_inv ht ht_branch
    calc
      title i m_inv ≤ omega i t h m_inv := h_clean m_inv
      _ = omega i t (jointBranch i j t h α₀ α_j) m_inv := h_omega
  exact actionFrame_invasion_strips_feasible_menu i j t t' h title α_j m_inv β
    h_clean_branch h_contract h_feas_joint h_cont h_tight

/-- Purposeful action by `i` on a joint branch `(α_i, α_j)` strictly improves upon
the conditional baseline `(α₀, α_j)` holding `j`'s action fixed. -/
theorem purposeful_action_beats_conditional_baseline
    (i j : Agent) (t : Moment) (h : History) (α_i α_j : Action)
    (h_purp_i : PurposefulAct i t (jointBranch i j t h α_i α_j) α_i)
    (h_ne : α_i ≠ α₀) :
    Preference i t (jointBranch i j t h α_i α_j)
      (End_of i α_i t (jointBranch i j t h α_i α_j))
      (End_of i α₀ t (jointBranch i j t h α_i α_j)) := by
  rcases h_purp_i.2.2.1 with rfl | h_pref
  · contradiction
  · exact h_pref

/-- Both distinct agents perform purposeful actions different from `α₀` at `⟨t, h⟩`. -/
def BilateralExchangeAction (i j : Agent) (t : Moment) (h : History) (α_i α_j : Action) : Prop :=
  i ≠ j ∧ PurposefulAct i t h α_i ∧ α_i ≠ α₀ ∧ PurposefulAct j t h α_j ∧ α_j ≠ α₀

/-- Both exchange actions are active purposeful actions. -/
theorem bilateral_exchange_active (i j : Agent) (t : Moment) (h : History) (α_i α_j : Action)
    (h_act : BilateralExchangeAction i j t h α_i α_j) :
    ActivePurposefulAct i t h α_i ∧ ActivePurposefulAct j t h α_j := by
  have ⟨_, hi, hne_i, hj, hne_j⟩ := h_act
  exact ⟨(active_purposeful_act_iff_ne_alpha_zero i t h α_i).mpr ⟨hi, hne_i⟩,
         (active_purposeful_act_iff_ne_alpha_zero j t h α_j).mpr ⟨hj, hne_j⟩⟩

variable [BilateralExchangeFrame W]

/-- Action of offering an exchange:
    agent i offers qA units of mA to agent j in exchange for qB units of mB. -/
abbrev Offer (i j : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action :=
  W.Offer i j qA mA qB mB

/-- Action of accepting an exchange:
    agent j accepts qA units of mA from agent i in exchange for qB units of mB. -/
abbrev Accept (j i : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action :=
  W.Accept j i qA mA qB mB

/-- Both distinct agents purposefully enact the corresponding offer and acceptance at `⟨t, h⟩`. -/
def BilateralExchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Prop :=
  i ≠ j ∧ mA ≠ mB ∧
  BilateralExchangeAction i j t h (Offer i j qA mA qB mB) (Accept j i qA mA qB mB)

/-- Price, quantities, parties, and decision node for one bilateral exchange. -/
structure BilateralTradeTerms where
  seller : Agent
  buyer : Agent
  moment : Moment
  history : History
  qA : ℕ
  mA : Means
  qB : ℕ
  mB : Means
  distinctAgents : seller ≠ buyer
  distinctGoods : mA ≠ mB

def BilateralTradeTerms.offer (T : BilateralTradeTerms) : Action :=
  Offer T.seller T.buyer T.qA T.mA T.qB T.mB

def BilateralTradeTerms.accept (T : BilateralTradeTerms) : Action :=
  Accept T.buyer T.seller T.qA T.mA T.qB T.mB

/-- Feasibility, nonzero action, and enactment evidence for the two sides. -/
structure BilateralTradeExecution (T : BilateralTradeTerms) where
  offerNonzero : T.offer ≠ α₀
  offerFeasible : T.offer ∈ A_feas T.seller T.moment T.history
  offerEnacted : Exec T.seller T.moment T.offer T.history
  acceptNonzero : T.accept ≠ α₀
  acceptFeasible : T.accept ∈ A_feas T.buyer T.moment T.history
  acceptEnacted : Exec T.buyer T.moment T.accept T.history

/-- Each feasible menu contains only passivity or the specified trade action. -/
structure BilateralTradeMenus (T : BilateralTradeTerms) where
  offerMenu : ∀ β ∈ A_feas T.seller T.moment T.history,
    β = α₀ ∨ β = T.offer
  acceptMenu : ∀ β ∈ A_feas T.buyer T.moment T.history,
    β = α₀ ∨ β = T.accept

/-- Both agents' bundle outcomes and teleological gain evidence. -/
structure BilateralSubjectiveGains (T : BilateralTradeTerms) where
  beforeSeller : Means → ℕ
  afterSeller : Means → ℕ
  beforeBuyer : Means → ℕ
  afterBuyer : Means → ℕ
  offerOutcome : End_of T.seller T.offer T.moment T.history = W.BundleEnd afterSeller
  sellerBaseline : End_of T.seller α₀ T.moment T.history = W.BundleEnd beforeSeller
  acceptOutcome : End_of T.buyer T.accept T.moment T.history = W.BundleEnd afterBuyer
  buyerBaseline : End_of T.buyer α₀ T.moment T.history = W.BundleEnd beforeBuyer
  sellerDominates : W.SubjectiveTeleologicalDominates T.seller T.moment T.history
    afterSeller beforeSeller
  buyerDominates : W.SubjectiveTeleologicalDominates T.buyer T.moment T.history
    afterBuyer beforeBuyer

/-- Complete appraisal, menu, execution, and outcome evidence for a bilateral
trade synthesis. -/
structure BilateralTradeScenario where
  terms : BilateralTradeTerms
  execution : BilateralTradeExecution terms
  menus : BilateralTradeMenus terms
  gains : BilateralSubjectiveGains terms

/-- Named exchange and preference conclusions for both parties. -/
structure BilateralTradeConclusion (T : BilateralTradeTerms) : Prop where
  exchange : BilateralExchange T.seller T.buyer T.moment T.history T.qA T.mA T.qB T.mB
  sellerPrefers : Preference T.seller T.moment T.history
    (End_of T.seller T.offer T.moment T.history) (End_of T.seller α₀ T.moment T.history)
  buyerPrefers : Preference T.buyer T.moment T.history
    (End_of T.buyer T.accept T.moment T.history) (End_of T.buyer α₀ T.moment T.history)


theorem double_inequality_of_exchange (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_exch : BilateralExchange i j t h qA mA qB mB) :
    Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h) ∧
    Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h) := by
  have ⟨_, h_act_i, h_ne_i, h_act_j, h_ne_j⟩ := h_exch.2.2
  exact ⟨purposeful_act_pref_of_ne_alpha_zero i t h (Offer i j qA mA qB mB) h_act_i h_ne_i,
         purposeful_act_pref_of_ne_alpha_zero j t h (Accept j i qA mA qB mB) h_act_j h_ne_j⟩


theorem ricardian_bilateral_exchange_purposeful
    (i j : Agent) (t : Moment) (h : History)
    (mA mB : Means) (qA qB : ℕ)
    (h_ij : i ≠ j) (h_m : mA ≠ mB)
    (h_purp_i : PurposefulAct i t h (Offer i j qA mA qB mB))
    (h_ne_i : Offer i j qA mA qB mB ≠ α₀)
    (h_purp_j : PurposefulAct j t h (Accept j i qA mA qB mB))
    (h_ne_j : Accept j i qA mA qB mB ≠ α₀) :
    BilateralExchange i j t h qA mA qB mB :=
  ⟨h_ij, h_m, h_ij, h_purp_i, h_ne_i, h_purp_j, h_ne_j⟩


private theorem bilateral_exchange_of_pareto_gain_core
    (i j : Agent) (t : Moment) (h : History)
    (mA mB : Means) (qA qB : ℕ)
    (h_ij : i ≠ j) (h_m : mA ≠ mB)
    (hne_i : Offer i j qA mA qB mB ≠ α₀)
    (hne_j : Accept j i qA mA qB mB ≠ α₀)
    (h_feas_i : Offer i j qA mA qB mB ∈ A_feas i t h)
    (h_exec_i : Exec i t (Offer i j qA mA qB mB) h)
    (h_pref_i : Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h))
    (h_menu_i : ∀ β ∈ A_feas i t h, β = α₀ ∨ β = Offer i j qA mA qB mB)
    (h_feas_j : Accept j i qA mA qB mB ∈ A_feas j t h)
    (h_exec_j : Exec j t (Accept j i qA mA qB mB) h)
    (h_pref_j : Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h))
    (h_menu_j : ∀ β ∈ A_feas j t h, β = α₀ ∨ β = Accept j i qA mA qB mB) :
    BilateralExchange i j t h qA mA qB mB := by
  have h_purp_i : PurposefulAct i t h (Offer i j qA mA qB mB) := by
    refine ⟨h_feas_i, h_exec_i, Or.inr h_pref_i, ?_⟩
    intro β hβ
    rcases h_menu_i β hβ with rfl | rfl
    · intro h_rev
      exact pref_asymm i t h h_pref_i h_rev
    · intro h_self
      exact pref_irrefl i t h _ h_self
  have h_purp_j : PurposefulAct j t h (Accept j i qA mA qB mB) := by
    refine ⟨h_feas_j, h_exec_j, Or.inr h_pref_j, ?_⟩
    intro β hβ
    rcases h_menu_j β hβ with rfl | rfl
    · intro h_rev
      exact pref_asymm j t h h_pref_j h_rev
    · intro h_self
      exact pref_irrefl j t h _ h_self
  exact ricardian_bilateral_exchange_purposeful i j t h mA mB qA qB
    h_ij h_m h_purp_i hne_i h_purp_j hne_j


theorem ricardian_bilateral_exchange_of_pareto_gain
    (S : BilateralTradeScenario) : BilateralTradeConclusion S.terms := by
  let T := S.terms
  let E := S.execution
  let M := S.menus
  let G := S.gains
  have hpref_seller : Preference T.seller T.moment T.history
      (End_of T.seller T.offer T.moment T.history)
      (End_of T.seller α₀ T.moment T.history) := by
    rw [G.offerOutcome, G.sellerBaseline]
    exact W.teleological_bundle_dominance_induces_preference T.seller T.moment
      T.history G.afterSeller G.beforeSeller G.sellerDominates
  have hpref_buyer : Preference T.buyer T.moment T.history
      (End_of T.buyer T.accept T.moment T.history)
      (End_of T.buyer α₀ T.moment T.history) := by
    rw [G.acceptOutcome, G.buyerBaseline]
    exact W.teleological_bundle_dominance_induces_preference T.buyer T.moment
      T.history G.afterBuyer G.beforeBuyer G.buyerDominates
  have hexchange := bilateral_exchange_of_pareto_gain_core
    T.seller T.buyer T.moment T.history T.mA T.mB T.qA T.qB
    T.distinctAgents T.distinctGoods E.offerNonzero E.acceptNonzero
    E.offerFeasible E.offerEnacted hpref_seller M.offerMenu
    E.acceptFeasible E.acceptEnacted hpref_buyer M.acceptMenu
  exact ⟨hexchange, hpref_seller, hpref_buyer⟩


theorem bilateral_exchange_conserves_endowments
    (i j : Agent) (t t' : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_distinct_agents : i ≠ j)
    (h_distinct : mA ≠ mB)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h)
    (h_exec_i : enacted i t h = Offer i j qA mA qB mB)
    (h_exec_j : enacted j t h = Accept j i qA mA qB mB) :
    omega i t' h mA + omega j t' h mA = omega i t h mA + omega j t h mA ∧
    omega i t' h mB + omega j t' h mB = omega i t h mB + omega j t h mB :=
  bilateral_exchange_conserves_means i j t t' h qA mA qB mB
    h_distinct_agents h_distinct h_next h_exec_i h_exec_j

/-- Purposeful bilateral exchange evidence entails the corresponding enacted
offer and acceptance on its history. -/
theorem bilateral_exchange_enacted_actions
    (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_exch : BilateralExchange i j t h qA mA qB mB) :
    enacted i t h = Offer i j qA mA qB mB ∧
    enacted j t h = Accept j i qA mA qB mB := by
  rcases h_exch.2.2 with ⟨_, h_offer, _, h_accept, _⟩
  have h_offer_exec := h_offer.2.1
  have h_accept_exec := h_accept.2.1
  change h ∈ ChoicePartition i t (Offer i j qA mA qB mB) at h_offer_exec
  change h ∈ ChoicePartition j t (Accept j i qA mA qB mB) at h_accept_exec
  exact ⟨h_offer_exec.2, h_accept_exec.2⟩

/-- Bilateral exchange evidence contains purposeful actions by both parties. -/
theorem bilateral_exchange_purposeful_actions
    (i j : Agent) (t : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_exch : BilateralExchange i j t h qA mA qB mB) :
    PurposefulAct i t h (Offer i j qA mA qB mB) ∧
    PurposefulAct j t h (Accept j i qA mA qB mB) := by
  rcases h_exch.2.2 with ⟨_, h_offer, _, h_accept, _⟩
  exact ⟨h_offer, h_accept⟩


theorem bilateral_exchange_commodity_transfers
    (i j : Agent) (t t' : Moment) (h : History)
    (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means)
    (h_distinct_agents : i ≠ j)
    (h_distinct : mA ≠ mB)
    (h_next : IsNextMoment Precedence W.mem_hist t t' h)
    (h_exec_i : enacted i t h = Offer i j qA mA qB mB)
    (h_exec_j : enacted j t h = Accept j i qA mA qB mB) :
    omega i t' h mA + qA = omega i t h mA ∧
    omega j t' h mA = omega j t h mA + qA ∧
    omega i t' h mB = omega i t h mB + qB ∧
    omega j t' h mB + qB = omega j t h mB := by
  have ⟨h_tr_i_A, h_tr_j_A⟩ :=
    W.bilateral_transfer_law i j qA mA qB mB t t' h mA h_distinct_agents h_exec_i h_exec_j h_next
  have ⟨h_tr_i_B, h_tr_j_B⟩ :=
    W.bilateral_transfer_law i j qA mA qB mB t t' h mB h_distinct_agents h_exec_i h_exec_j h_next
  simp only [h_distinct, ite_true, ite_false] at h_tr_i_A h_tr_j_A
  simp only [h_distinct.symm, ite_true, ite_false] at h_tr_i_B h_tr_j_B
  dsimp [omega]
  refine ⟨by omega, by omega, by omega, by omega⟩


private theorem action_frame_mises_law_of_association
    (i j : Agent) (t : Moment) (h : History)
    (mA mB : Means) (qA qB : ℕ)
    (h_ij : i ≠ j) (h_m : mA ≠ mB)
    (hne_i : Offer i j qA mA qB mB ≠ α₀)
    (hne_j : Accept j i qA mA qB mB ≠ α₀)
    (h_feas_i : Offer i j qA mA qB mB ∈ A_feas i t h)
    (h_exec_i : Exec i t (Offer i j qA mA qB mB) h)
    (h_menu_i : ∀ β ∈ A_feas i t h, β = α₀ ∨ β = Offer i j qA mA qB mB)
    (h_feas_j : Accept j i qA mA qB mB ∈ A_feas j t h)
    (h_exec_j : Exec j t (Accept j i qA mA qB mB) h)
    (h_menu_j : ∀ β ∈ A_feas j t h, β = α₀ ∨ β = Accept j i qA mA qB mB)
    (b_autarky_i b_spec_i b_autarky_j b_spec_j : Means → ℕ)
    (h_dom_i : W.SubjectiveTeleologicalDominates i t h b_spec_i b_autarky_i)
    (h_dom_j : W.SubjectiveTeleologicalDominates j t h b_spec_j b_autarky_j)
    (h_end_spec_i : End_of i (Offer i j qA mA qB mB) t h = W.BundleEnd b_spec_i)
    (h_end_aut_i : End_of i α₀ t h = W.BundleEnd b_autarky_i)
    (h_end_spec_j : End_of j (Accept j i qA mA qB mB) t h = W.BundleEnd b_spec_j)
    (h_end_aut_j : End_of j α₀ t h = W.BundleEnd b_autarky_j) :
    BilateralExchange i j t h qA mA qB mB ∧
    Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h) ∧
    Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h) := by
  have h_pref_i : Preference i t h (End_of i (Offer i j qA mA qB mB) t h) (End_of i α₀ t h) := by
    rw [h_end_spec_i, h_end_aut_i]
    exact W.teleological_bundle_dominance_induces_preference i t h b_spec_i b_autarky_i h_dom_i
  have h_pref_j : Preference j t h (End_of j (Accept j i qA mA qB mB) t h) (End_of j α₀ t h) := by
    rw [h_end_spec_j, h_end_aut_j]
    exact W.teleological_bundle_dominance_induces_preference j t h b_spec_j b_autarky_j h_dom_j
  have h_exch := bilateral_exchange_of_pareto_gain_core i j t h mA mB qA qB
    h_ij h_m hne_i hne_j h_feas_i h_exec_i h_pref_i h_menu_i
    h_feas_j h_exec_j h_pref_j h_menu_j
  exact ⟨h_exch, h_pref_i, h_pref_j⟩

end BilateralActionFrameCatallactics

section SubjectiveBilateralTradeWitness

@[reducible] local instance : ActionFrame := SubjectiveBilateralTradeActionFrame
@[reducible] local instance : BilateralExchangeFrame SubjectiveBilateralTradeActionFrame :=
  inferInstance

abbrev tradeAgent0 : Fin 2 := 0
abbrev tradeAgent1 : Fin 2 := 1
abbrev tradeHistory : Fin 4 := 3
abbrev tradeMeans0 : Fin 3 := 0
abbrev tradeMeans1 : Fin 3 := 1


theorem subjective_bilateral_trade_action_frame_witness :
    (∀ i α t τ h,
      SubjectiveBilateralTradeActionFrame.OutcomeOf i α t τ h =
        SubjectiveBilateralTradeActionFrame.BundleEnd
          (SubjectiveBilateralTradeActionFrame.omega i τ h)) ∧
    BilateralExchange (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent0 tradeAgent1 BilateralMoment.root tradeHistory
      1 tradeMeans0 1 tradeMeans1 ∧
    (∀ m : Fin 3,
      bilateral_omega tradeAgent0 .leaf3 tradeHistory m +
          bilateral_omega tradeAgent1 .leaf3 tradeHistory m =
        bilateral_omega tradeAgent0 .root tradeHistory m +
          bilateral_omega tradeAgent1 .root tradeHistory m) ∧
    (Preference (F := SubjectiveBilateralTradeActionFrame)
        tradeAgent0 BilateralMoment.root tradeHistory
        (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0
          (Offer (W := SubjectiveBilateralTradeActionFrame) tradeAgent0 tradeAgent1
            1 tradeMeans0 1 tradeMeans1)
          BilateralMoment.root tradeHistory)
        (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0 ModelAction.idle
          BilateralMoment.root tradeHistory) ∧
     Preference (F := SubjectiveBilateralTradeActionFrame)
        tradeAgent1 BilateralMoment.root tradeHistory
        (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1
          (Accept (W := SubjectiveBilateralTradeActionFrame) tradeAgent1 tradeAgent0
            1 tradeMeans0 1 tradeMeans1)
          BilateralMoment.root tradeHistory)
        (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1 ModelAction.idle
          BilateralMoment.root tradeHistory)) := by
  have hout0 :
      End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0
          (Offer (W := SubjectiveBilateralTradeActionFrame) tradeAgent0 tradeAgent1
            1 tradeMeans0 1 tradeMeans1)
          BilateralMoment.root tradeHistory =
          SubjectiveBilateralTradeActionFrame.BundleEnd
            (bilateral_omega tradeAgent0 .leaf3 tradeHistory) ∧
      End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0 ModelAction.idle
          BilateralMoment.root tradeHistory =
        SubjectiveBilateralTradeActionFrame.BundleEnd
          (bilateral_omega tradeAgent0 .root tradeHistory) := by
    constructor
    · change bilateral_subjective_end tradeAgent0
        (ModelAction.offer tradeAgent0 tradeAgent1 1 tradeMeans0 1 tradeMeans1)
        BilateralMoment.root tradeHistory =
          BilateralEnd.bundle (bilateral_omega tradeAgent0 .leaf3 tradeHistory)
      simp [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_outcome, bilateral_subjective_maturation,
        bilateral_terminal_moment, bilateral_sigma]
    · change bilateral_subjective_end tradeAgent0 ModelAction.idle
        BilateralMoment.root tradeHistory =
          BilateralEnd.bundle (bilateral_omega tradeAgent0 .root tradeHistory)
      dsimp [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_outcome, bilateral_subjective_maturation,
        bilateral_terminal_moment, bilateral_sigma]
      apply congrArg BilateralEnd.bundle
      funext m
      fin_cases m <;> decide
  have hout1 :
      End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1
          (Accept (W := SubjectiveBilateralTradeActionFrame) tradeAgent1 tradeAgent0
            1 tradeMeans0 1 tradeMeans1)
          BilateralMoment.root tradeHistory =
          SubjectiveBilateralTradeActionFrame.BundleEnd
            (bilateral_omega tradeAgent1 .leaf3 tradeHistory) ∧
      End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1 ModelAction.idle
          BilateralMoment.root tradeHistory =
        SubjectiveBilateralTradeActionFrame.BundleEnd
          (bilateral_omega tradeAgent1 .root tradeHistory) := by
    constructor
    · change bilateral_subjective_end tradeAgent1
        (ModelAction.accept tradeAgent1 tradeAgent0 1 tradeMeans0 1 tradeMeans1)
        BilateralMoment.root tradeHistory =
          BilateralEnd.bundle (bilateral_omega tradeAgent1 .leaf3 tradeHistory)
      simp [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_outcome, bilateral_subjective_maturation,
        bilateral_terminal_moment, bilateral_sigma]
    · change bilateral_subjective_end tradeAgent1 ModelAction.idle
        BilateralMoment.root tradeHistory =
          BilateralEnd.bundle (bilateral_omega tradeAgent1 .root tradeHistory)
      dsimp [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_outcome, bilateral_subjective_maturation,
        bilateral_terminal_moment, bilateral_sigma]
      apply congrArg BilateralEnd.bundle
      funext m
      fin_cases m <;> decide
  have hdom0 : SubjectiveTeleologicalDominates bilateral_subjective_requirement
      (bilateral_subjective_valued_end tradeAgent0 BilateralMoment.root tradeHistory)
      (bilateral_omega tradeAgent0 .leaf3 tradeHistory)
      (bilateral_omega tradeAgent0 .root tradeHistory) :=
    bilateral_subjective_trade_dominance tradeAgent0
  have hdom1 : SubjectiveTeleologicalDominates bilateral_subjective_requirement
      (bilateral_subjective_valued_end tradeAgent1 BilateralMoment.root tradeHistory)
      (bilateral_omega tradeAgent1 .leaf3 tradeHistory)
      (bilateral_omega tradeAgent1 .root tradeHistory) :=
    bilateral_subjective_trade_dominance tradeAgent1
  have hpref0 : Preference (F := SubjectiveBilateralTradeActionFrame)
      tradeAgent0 BilateralMoment.root tradeHistory
      (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0
        (Offer (W := SubjectiveBilateralTradeActionFrame) tradeAgent0 tradeAgent1
          1 tradeMeans0 1 tradeMeans1)
        BilateralMoment.root tradeHistory)
      (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent0 ModelAction.idle
        BilateralMoment.root tradeHistory) := by
    rw [hout0.1, hout0.2]
    exact teleological_bundle_dominance_induces_preference
      (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent0 BilateralMoment.root tradeHistory _ _ hdom0
  have hpref1 : Preference (F := SubjectiveBilateralTradeActionFrame)
      tradeAgent1 BilateralMoment.root tradeHistory
      (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1
        (Accept (W := SubjectiveBilateralTradeActionFrame) tradeAgent1 tradeAgent0
          1 tradeMeans0 1 tradeMeans1)
        BilateralMoment.root tradeHistory)
      (End_of (F := SubjectiveBilateralTradeActionFrame) tradeAgent1 ModelAction.idle
        BilateralMoment.root tradeHistory) := by
    rw [hout1.1, hout1.2]
    exact teleological_bundle_dominance_induces_preference
      (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent1 BilateralMoment.root tradeHistory _ _ hdom1
  have hmenu0 : ∀ β ∈ A_feas (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent0 BilateralMoment.root tradeHistory,
      β = ModelAction.idle ∨
        β = Offer (W := SubjectiveBilateralTradeActionFrame) tradeAgent0 tradeAgent1
          1 tradeMeans0 1 tradeMeans1 := by
    intro β hβ
    change β ∈ ({ModelAction.idle, ModelAction.offer 0 1 1 0 1 1} : Finset ModelAction) at hβ
    change β = ModelAction.idle ∨ β = ModelAction.offer 0 1 1 0 1 1
    simpa using hβ
  have hmenu1 : ∀ β ∈ A_feas (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent1 BilateralMoment.root tradeHistory,
      β = ModelAction.idle ∨
        β = Accept (W := SubjectiveBilateralTradeActionFrame) tradeAgent1 tradeAgent0
          1 tradeMeans0 1 tradeMeans1 := by
    intro β hβ
    change β ∈ ({ModelAction.idle, ModelAction.accept 1 0 1 0 1 1} : Finset ModelAction) at hβ
    change β = ModelAction.idle ∨ β = ModelAction.accept 1 0 1 0 1 1
    simpa using hβ
  let T : BilateralTradeTerms (W := SubjectiveBilateralTradeActionFrame) := {
    seller := tradeAgent0
    buyer := tradeAgent1
    moment := BilateralMoment.root
    history := tradeHistory
    qA := 1
    mA := tradeMeans0
    qB := 1
    mB := tradeMeans1
    distinctAgents := by decide
    distinctGoods := by decide }
  have E : BilateralTradeExecution (W := SubjectiveBilateralTradeActionFrame) T := {
    offerNonzero := by decide
    offerFeasible := by simpa [T, BilateralTradeTerms.offer] using
      (show Offer tradeAgent0 tradeAgent1 1 tradeMeans0 1 tradeMeans1 ∈
        A_feas tradeAgent0 BilateralMoment.root tradeHistory by decide)
    offerEnacted := by
      simpa [T, BilateralTradeTerms.offer] using
        (show Exec tradeAgent0 BilateralMoment.root
          (Offer tradeAgent0 tradeAgent1 1 tradeMeans0 1 tradeMeans1) tradeHistory by
          exact ⟨trivial, rfl⟩)
    acceptNonzero := by decide
    acceptFeasible := by simpa [T, BilateralTradeTerms.accept] using
      (show Accept tradeAgent1 tradeAgent0 1 tradeMeans0 1 tradeMeans1 ∈
        A_feas tradeAgent1 BilateralMoment.root tradeHistory by decide)
    acceptEnacted := by
      simpa [T, BilateralTradeTerms.accept] using
        (show Exec tradeAgent1 BilateralMoment.root
          (Accept tradeAgent1 tradeAgent0 1 tradeMeans0 1 tradeMeans1) tradeHistory by
          exact ⟨trivial, rfl⟩) }
  have M : BilateralTradeMenus (W := SubjectiveBilateralTradeActionFrame) T := by
    refine ⟨?_, ?_⟩
    · intro β hβ
      change β = ModelAction.idle ∨
        β = ModelAction.offer tradeAgent0 tradeAgent1 1 tradeMeans0 1 tradeMeans1
      exact hmenu0 β hβ
    · intro β hβ
      change β = ModelAction.idle ∨
        β = ModelAction.accept tradeAgent1 tradeAgent0 1 tradeMeans0 1 tradeMeans1
      exact hmenu1 β hβ
  have G : BilateralSubjectiveGains (W := SubjectiveBilateralTradeActionFrame) T := {
    beforeSeller := bilateral_omega tradeAgent0 .root tradeHistory
    afterSeller := bilateral_omega tradeAgent0 .leaf3 tradeHistory
    beforeBuyer := bilateral_omega tradeAgent1 .root tradeHistory
    afterBuyer := bilateral_omega tradeAgent1 .leaf3 tradeHistory
    offerOutcome := by simpa [T, BilateralTradeTerms.offer] using hout0.1
    sellerBaseline := by
      change End_of tradeAgent0 ModelAction.idle BilateralMoment.root tradeHistory = _
      exact hout0.2
    acceptOutcome := by simpa [T, BilateralTradeTerms.accept] using hout1.1
    buyerBaseline := by
      change End_of tradeAgent1 ModelAction.idle BilateralMoment.root tradeHistory = _
      exact hout1.2
    sellerDominates := hdom0
    buyerDominates := hdom1 }
  let S : BilateralTradeScenario (W := SubjectiveBilateralTradeActionFrame) :=
    ⟨T, E, M, G⟩
  have htrade := ricardian_bilateral_exchange_of_pareto_gain S
  have hexchange : BilateralExchange (W := SubjectiveBilateralTradeActionFrame)
      tradeAgent0 tradeAgent1 BilateralMoment.root tradeHistory 1 tradeMeans0 1 tradeMeans1 := by
    simpa [T] using htrade.exchange
  refine ⟨?_, hexchange, ?_, ⟨hpref0, hpref1⟩⟩
  · intro i α t τ h
    rfl
  · intro m
    fin_cases m <;> decide

end SubjectiveBilateralTradeWitness


-- Section 2.1: Fixed Points of the Acceptance Operator


section MengerBourbakiWitt
variable [W : ActionFrame]

/-- Maps each means to the agents who accept it. -/
def AcceptanceProfile := Means → Finset Agent

/-- Pointwise subset inclusion between acceptance profiles. -/
def ProfileLE (Γ1 Γ2 : AcceptanceProfile) : Prop :=
  ∀ m : Means, Γ1 m ⊆ Γ2 m

/-- The acceptance set for `m` has maximum cardinality in `Γ`. -/
def IsMaxMarketable (Γ : AcceptanceProfile) (m : Means) : Prop :=
  ∀ m' : Means, (Γ m').card ≤ (Γ m).card

/-- Adds agents for whom `m` has maximum acceptance and indirect exchange is feasible.
The decision procedures are explicit so finite instances remain executable. -/
def Phi (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile)
    [∀ m, Decidable (IsMaxMarketable Γ m)] [∀ i m, Decidable (FeasIndirect i m)]
    (m : Means) : Finset Agent :=
  Γ m ∪ Finset.univ.filter (fun i => IsMaxMarketable Γ m ∧ FeasIndirect i m)

/-- `Phi` contains every agent in the input acceptance profile. -/
theorem phi_inflationary (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile)
    [∀ m, Decidable (IsMaxMarketable Γ m)] [∀ i m, Decidable (FeasIndirect i m)] :
    ProfileLE Γ (Phi FeasIndirect Γ) := by
  intro m
  dsimp [Phi]
  exact Finset.subset_union_left

theorem phi_not_globally_monotone
    (FeasIndirect : Agent → Means → Prop)
    (Γ1 Γ2 : AcceptanceProfile) (m : Means) (i : Agent)
    [∀ m, Decidable (IsMaxMarketable Γ1 m)] [∀ m, Decidable (IsMaxMarketable Γ2 m)]
    [∀ i m, Decidable (FeasIndirect i m)]
    (h_max1 : IsMaxMarketable Γ1 m)
    (h_feas : FeasIndirect i m)
    (h_not_in2 : i ∉ Γ2 m)
    (h_not_max2 : ¬ IsMaxMarketable Γ2 m) :
    ¬ ProfileLE (Phi FeasIndirect Γ1) (Phi FeasIndirect Γ2) := by
  classical
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


end MengerBourbakiWitt

/-- A finite profile witness shows that maximum-marketability adoption can
fail to preserve profile inclusion. -/
theorem concrete_phi_non_monotone_witness :
    let Agent := Fin 3
    let Means := Fin 2
    let IsMax := fun (Γ : Means → Finset Agent) (m : Means) =>
      ∀ m', (Γ m').card ≤ (Γ m).card
    let PhiOp := fun (Γ : Means → Finset Agent) (m : Means) =>
      Γ m ∪ Finset.univ.filter (fun _ => IsMax Γ m)
    ∃ (Γ1 Γ2 : Means → Finset Agent),
      (∀ m, Γ1 m ⊆ Γ2 m) ∧
      ¬ (∀ m, PhiOp Γ1 m ⊆ PhiOp Γ2 m) := by
  let Γ1 : Fin 2 → Finset (Fin 3) := fun m =>
    if m = 0 then {0} else {1}
  let Γ2 : Fin 2 → Finset (Fin 3) := fun m =>
    if m = 0 then {0} else {1, 2}
  have h_le : ∀ m, Γ1 m ⊆ Γ2 m := by
    intro m
    fin_cases m <;> decide
  have h_not_mono : ¬ (∀ m : Fin 2,
      (Γ1 m ∪ Finset.univ.filter (fun _ => ∀ m', (Γ1 m').card ≤ (Γ1 m).card)) ⊆
      (Γ2 m ∪ Finset.univ.filter (fun _ => ∀ m', (Γ2 m').card ≤ (Γ2 m).card))) := by
    intro h_mono
    have h_mem : (2 : Fin 3) ∈
        (Γ1 0 ∪ Finset.univ.filter (fun _ => ∀ m', (Γ1 m').card ≤ (Γ1 0).card)) := by
      decide
    have h_sub := h_mono 0 h_mem
    revert h_sub
    decide
  exact ⟨Γ1, Γ2, h_le, h_not_mono⟩

section MengerBourbakiWitt
variable [W : ActionFrame]

/-- `Γ` is unchanged by `Phi`. -/
def IsFixedPoint (FeasIndirect : Agent → Means → Prop) (Γ : AcceptanceProfile)
    [∀ m, Decidable (IsMaxMarketable Γ m)] [∀ i m, Decidable (FeasIndirect i m)] : Prop :=
  Phi FeasIndirect Γ = Γ

/-- Every agent accepts `m_star`. -/
def IsUniversalMoney (Γ : AcceptanceProfile) (m_star : Means) : Prop :=
  Γ m_star = Finset.univ


theorem dominant_medium_one_step_fixed_point (FeasIndirect : Agent → Means → Prop)
    [decMax : ∀ Γ : AcceptanceProfile, ∀ m, Decidable (IsMaxMarketable Γ m)]
    [decFeas : ∀ i m, Decidable (FeasIndirect i m)]
    (Γ0 : AcceptanceProfile) (m_star : Means)
    (h_strict_max : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Γ0 m_star).card)
    (h_all_feas : ∀ i : Agent, FeasIndirect i m_star)
    (h_not_univ : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Finset.univ : Finset Agent).card) :
    ∃ (Γ_star : AcceptanceProfile),
      IsFixedPoint FeasIndirect Γ_star ∧
      ProfileLE Γ0 Γ_star ∧
      IsUniversalMoney Γ_star m_star := by
  let : ∀ m, Decidable (IsMaxMarketable Γ0 m) := decMax Γ0
  let : ∀ i m, Decidable (FeasIndirect i m) := decFeas
  let Γ_star := Phi FeasIndirect Γ0
  use Γ_star
  have h_max_mstar : IsMaxMarketable Γ0 m_star := by
    intro m'
    by_cases h_eq : m' = m_star
    · subst h_eq
      exact le_rfl
    · exact le_of_lt (h_strict_max m' h_eq)
  have h_not_max_other : ∀ m : Means, m ≠ m_star → ¬ IsMaxMarketable Γ0 m := by
    intro m h_ne h_all_le
    have h_le := h_all_le m_star
    have h_lt := h_strict_max m h_ne
    linarith
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
  let : ∀ m, Decidable (IsMaxMarketable Γ_star m) := decMax Γ_star
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
  have h_le : ProfileLE Γ0 Γ_star := phi_inflationary FeasIndirect Γ0
  have h_univ : IsUniversalMoney Γ_star m_star := h_gamma_star_mstar
  exact ⟨h_fixed_point, h_le, h_univ⟩


theorem universal_money_emergence (FeasIndirect : Agent → Means → Prop)
    (Γ_star : AcceptanceProfile)
    [∀ m, Decidable (IsMaxMarketable Γ_star m)] [∀ i m, Decidable (FeasIndirect i m)]
    (m_star : Means)
    (h_fix : IsFixedPoint FeasIndirect Γ_star)
    (h_max : IsMaxMarketable Γ_star m_star)
    (h_all_feas : ∀ i : Agent, FeasIndirect i m_star) :
    IsUniversalMoney Γ_star m_star := by
  classical
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


structure MengerianAdoptionDecision (i : Agent) (t : Moment) (h : History)
    (Γ : AcceptanceProfile) (m_star : Means) where
  α_adopt : Means → Action
  downstreamBundle : Means → (Means → ℕ)
  holdBundle : Means → ℕ
  h_end_adopt : ∀ m, End_of i (α_adopt m) t h = W.BundleEnd (downstreamBundle m)
  h_end_hold : End_of i α₀ t h = W.BundleEnd holdBundle
  h_feas_star : α_adopt m_star ∈ A_feas i t h
  h_unease_star : W.SubjectiveTeleologicalDominates i t h (downstreamBundle m_star) holdBundle
  h_marketability_bundle_dom : ∀ m, (Γ m).card < (Γ m_star).card →
    α_adopt m ∈ A_feas i t h →
    W.SubjectiveTeleologicalDominates i t h (downstreamBundle m_star) (downstreamBundle m)


theorem purposeful_mengerian_money_adoption
    {i : Agent} {t : Moment} {h : History}
    {Γ : AcceptanceProfile} {m_star : Means}
    (dec : MengerianAdoptionDecision i t h Γ m_star)
    (m : Means)
    (h_less_marketable : (Γ m).card < (Γ m_star).card) :
    ¬ PurposefulAct i t h (dec.α_adopt m) := by
  classical
  intro h_purp
  have h_feas_m := h_purp.1
  have h_dom := dec.h_marketability_bundle_dom m h_less_marketable h_feas_m
  have h_pref := W.teleological_bundle_dominance_induces_preference i t h
    (dec.downstreamBundle m_star) (dec.downstreamBundle m) h_dom
  rw [← dec.h_end_adopt m_star, ← dec.h_end_adopt m] at h_pref
  have h_undom := h_purp.2.2.2 (dec.α_adopt m_star) dec.h_feas_star
  exact h_undom h_pref


theorem purposeful_phi_microfoundation
    {i : Agent} {t : Moment} {h : History}
    {Γ0 : AcceptanceProfile} {m_star : Means}
    (h_strict_max : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Γ0 m_star).card)
    (dec : MengerianAdoptionDecision i t h Γ0 m_star) :
    ∀ m : Means, m ≠ m_star → ¬ PurposefulAct i t h (dec.α_adopt m) := by
  classical
  intro m h_ne
  exact purposeful_mengerian_money_adoption dec m (h_strict_max m h_ne)


open Classical in
theorem phi_eq_purposeful_adoption_aggregation
    (FeasIndirect : Agent → Means → Prop)
    (Γ0 : AcceptanceProfile) (m_star : Means) (t : Moment) (h : History)
    (h_strict_max : ∀ m : Means, m ≠ m_star → (Γ0 m).card < (Γ0 m_star).card)
    (dec : ∀ i : Agent, MengerianAdoptionDecision i t h Γ0 m_star)
    (h_purp_iff_feas : ∀ i : Agent,
      PurposefulAct i t h ((dec i).α_adopt m_star) ↔ FeasIndirect i m_star) :
    Phi FeasIndirect Γ0 m_star =
      Γ0 m_star ∪ Finset.univ.filter (fun i => PurposefulAct i t h ((dec i).α_adopt m_star)) := by
  classical
  have h_max_star : IsMaxMarketable Γ0 m_star := by
    intro m'
    by_cases h_eq : m' = m_star
    · subst h_eq; exact le_rfl
    · exact le_of_lt (h_strict_max m' h_eq)
  ext i
  dsimp [Phi]
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_union, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro (h_in | ⟨_, h_feas⟩)
    · exact Or.inl h_in
    · exact Or.inr ((h_purp_iff_feas i).mpr h_feas)
  · rintro (h_in | h_purp)
    · exact Or.inl h_in
    · exact Or.inr ⟨h_max_star, (h_purp_iff_feas i).mp h_purp⟩

end MengerBourbakiWitt

/-- Strict upward step strictly decreases the cardinality of the upper set `{y | x ≤ y}`. -/
lemma upper_set_card_lt_of_lt {L : Type*} [Fintype L] [PartialOrder L]
    [DecidableRel (· ≤ · : L → L → Prop)]
    {x y : L} (h_lt : x < y) :
    (Finset.univ.filter (fun z : L => y ≤ z)).card <
    (Finset.univ.filter (fun z : L => x ≤ z)).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_trans (le_of_lt h_lt) hz.2⟩
  · intro h_eq
    have hx : x ∈ Finset.univ.filter (fun z : L => x ≤ z) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, le_rfl⟩
    rw [← h_eq, Finset.mem_filter] at hx
    exact not_le_of_gt h_lt hx.2


theorem bounded_bourbaki_witt {L : Type u}
    (Φ : L → L) (measure : L → ℕ)
    (h_step : ∀ x, Φ x = x ∨ measure (Φ x) < measure x)
    (x₀ : L) :
    ∃ n : ℕ, Φ (Φ^[n] x₀) = Φ^[n] x₀ := by
  suffices h_aux : ∀ k x, measure x ≤ k → ∃ n, Φ (Φ^[n] x) = Φ^[n] x from
    h_aux (measure x₀) x₀ (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro x hx
    cases h_step x with
    | inl hfix => exact ⟨0, hfix⟩
    | inr hdec =>
      have hlt := Nat.lt_of_lt_of_le hdec hx
      exact False.elim (Nat.not_lt_zero _ hlt)
  | succ k ih =>
    intro x hx
    cases h_step x with
    | inl hfix => exact ⟨0, hfix⟩
    | inr hdec =>
      have h_le : measure (Φ x) ≤ k := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdec hx)
      obtain ⟨n, hn⟩ := ih (Φ x) h_le
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hn


theorem bourbaki_witt_finite_fixed_point
    {L : Type*} [Finite L] [PartialOrder L]
    (Φ : L → L) (h_infl : ∀ x, x ≤ Φ x) (x₀ : L) :
    ∃ n : ℕ, Φ (Φ^[n] x₀) = Φ^[n] x₀ := by
  cases nonempty_fintype L
  classical
  let measure : L → ℕ := fun x => (Finset.univ.filter (fun z : L => x ≤ z)).card
  have h_step : ∀ x, Φ x = x ∨ measure (Φ x) < measure x := by
    intro x
    if h_fix : Φ x = x then
      exact Or.inl h_fix
    else
      have h_lt : x < Φ x := lt_of_le_of_ne (h_infl x) (Ne.symm h_fix)
      exact Or.inr (upper_set_card_lt_of_lt h_lt)
  exact bounded_bourbaki_witt Φ measure h_step x₀


-- Section 2.5: Adoption on Trading Networks

section NetworkAdoption

/-- A graph of agents with a symmetric adjacency relation. -/
structure TradingNetwork (V : Type) where
  adjacent : V → V → Prop
  adj_symm : ∀ i j, adjacent i j → adjacent j i


def NetworkFeasIndirect {V M : Type}
    (G : TradingNetwork V)
    (Supplies : V → M)
    (Demands : V → M → Prop)
    (Γ : M → Finset V)
    (i : V) (m : M) : Prop :=
  ∃ j : V, G.adjacent i j ∧ Demands i (Supplies j) ∧ j ∈ Γ m


def PhiNet {V M : Type} [Fintype V] [DecidableEq V]
    (AdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (AdoptRule Γ i m)]
    (Γ : M → Finset V) (m : M) : Finset V :=
  Γ m ∪ Finset.univ.filter (fun i => AdoptRule Γ i m)

/-- `PhiNet` contains every agent in the input profile. -/
theorem phi_net_le {V M : Type} [Fintype V] [DecidableEq V]
    (AdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (AdoptRule Γ i m)]
    (Γ : M → Finset V) :
    Γ ≤ PhiNet AdoptRule Γ := by
  intro m
  dsimp [PhiNet]
  exact Finset.subset_union_left

theorem network_bourbaki_witt_convergence
    {M V : Type} [Finite M] [Fintype V] [DecidableEq V]
    (AdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (AdoptRule Γ i m)]
    (Γ₀ : M → Finset V) :
    ∃ n : ℕ, (PhiNet AdoptRule) (((PhiNet AdoptRule)^[n]) Γ₀) = ((PhiNet AdoptRule)^[n]) Γ₀ := by
  cases nonempty_fintype M
  classical
  exact bourbaki_witt_finite_fixed_point (PhiNet AdoptRule) (phi_net_le AdoptRule) Γ₀

/-- `PhiNet` using indirect exchange through `G`. -/
def PhiTradingNet {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M) (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (Γ : M → Finset V) (m : M) : Finset V :=
  PhiNet (NetworkFeasIndirect G Supplies Demands) Γ m

/-- Indirect exchange feasibility is preserved when the profile grows. -/
theorem network_feas_indirect_mono
    {V M : Type}
    (G : TradingNetwork V) (Supplies : V → M) (Demands : V → M → Prop)
    {Γ₁ Γ₂ : M → Finset V} (h_le : Γ₁ ≤ Γ₂) (i : V) (m : M)
    (h_feas : NetworkFeasIndirect G Supplies Demands Γ₁ i m) :
    NetworkFeasIndirect G Supplies Demands Γ₂ i m := by
  rcases h_feas with ⟨j, hadj, hdem, hj⟩
  exact ⟨j, hadj, hdem, h_le m hj⟩

/-- `PhiNet` preserves profile inclusion when `AdoptRule` does. -/
theorem phi_net_mono
    {V M : Type} [Fintype V] [DecidableEq V]
    {AdoptRule : (M → Finset V) → V → M → Prop}
    [∀ Γ i m, Decidable (AdoptRule Γ i m)]
    (h_rule_mono : ∀ Γ₁ Γ₂, Γ₁ ≤ Γ₂ → ∀ i m, AdoptRule Γ₁ i m → AdoptRule Γ₂ i m) :
    Monotone (PhiNet AdoptRule) := by
  classical
  intro Γ₁ Γ₂ h_le m
  dsimp [PhiNet]
  apply Finset.union_subset_union (h_le m)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, h_rule_mono Γ₁ Γ₂ h_le i m hi.2⟩


theorem phi_trading_net_mono
    {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M) (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)] :
    Monotone (PhiTradingNet G Supplies Demands) :=
  phi_net_mono (fun _ _ h_le => network_feas_indirect_mono G Supplies Demands h_le)

/-- Every proper profile containing `seed` has an adjacent unmet demand. -/
def NetworkWantsConnected {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M) (Demands : V → M → Prop)
    (seed : V) : Prop :=
  ∀ S : Finset V, seed ∈ S → S ≠ Finset.univ →
    ∃ (k : V) (j : V), k ∉ S ∧ j ∈ S ∧ G.adjacent k j ∧ Demands k (Supplies j)


/-- Every agent in the network accepts `m_star`. -/
def IsNetworkUniversalMoney {V M : Type} [Fintype V]
    (Γ : M → Finset V) (m_star : M) : Prop :=
  Γ m_star = Finset.univ

/-- An agent adopts a means when it is maximally marketable and available
through a neighbor in the current acceptance network. -/
def NetworkIsMaxMarketable {V M : Type}
    (Γ : M → Finset V) (m : M) : Prop :=
  ∀ m' : M, (Γ m').card ≤ (Γ m).card

def NetworkMarketableAdopt {V M : Type}
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop) (Γ : M → Finset V)
    (i : V) (m : M) : Prop :=
  NetworkIsMaxMarketable Γ m ∧ NetworkFeasIndirect G Supplies Demands Γ i m

/-- Acceptance growth that couples maximum marketability with network access. -/
def PhiNetworkMarketable {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (Γ : M → Finset V) (m : M) : Finset V :=
  PhiNet (NetworkMarketableAdopt G Supplies Demands) Γ m

/-- The coupled operator is inflationary because `PhiNet` retains every
existing accepter. -/
theorem phi_network_marketable_inflationary
    {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (Γ : M → Finset V) :
    Γ ≤ PhiNetworkMarketable G Supplies Demands Γ := by
  exact phi_net_le (NetworkMarketableAdopt G Supplies Demands) Γ

/-- The coupled operator reaches a fixed point because it is inflationary on
the finite lattice of acceptance profiles. -/
theorem network_marketable_bourbaki_witt_convergence
    {V M : Type} [Finite M] [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (Γ₀ : M → Finset V) :
    ∃ n : ℕ,
      PhiNetworkMarketable G Supplies Demands
          ((PhiNetworkMarketable G Supplies Demands)^[n] Γ₀) =
        (PhiNetworkMarketable G Supplies Demands)^[n] Γ₀ := by
  exact network_bourbaki_witt_convergence
    (NetworkMarketableAdopt G Supplies Demands) Γ₀

/-- Public convergence statement for the coupled marketability and network
operator. -/
theorem phi_network_marketable_convergence
    {M V : Type} [Finite M] [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (Γ₀ : M → Finset V) :
    ∃ n : ℕ,
      PhiNetworkMarketable G Supplies Demands
          ((PhiNetworkMarketable G Supplies Demands)^[n] Γ₀) =
        (PhiNetworkMarketable G Supplies Demands)^[n] Γ₀ := by
  exact network_marketable_bourbaki_witt_convergence
    G Supplies Demands Γ₀


/-- Every iterate of the coupled marketability/network operator contains its
initial acceptance profile. -/
lemma le_iterate_phi_network_marketable
    {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M)
    (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (Γ₀ : M → Finset V) (n : ℕ) :
    Γ₀ ≤ (PhiNetworkMarketable G Supplies Demands)^[n] Γ₀ := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
    have h_step : (PhiNetworkMarketable G Supplies Demands)^[k] Γ₀ ≤
        PhiNetworkMarketable G Supplies Demands
          ((PhiNetworkMarketable G Supplies Demands)^[k] Γ₀) :=
      phi_net_le (NetworkMarketableAdopt G Supplies Demands)
        ((PhiNetworkMarketable G Supplies Demands)^[k] Γ₀)
    rw [Function.iterate_succ_apply']
    exact le_trans ih h_step

/-- Every iterate of `PhiTradingNet` contains the initial profile. -/
lemma le_iterate_phi_trading_net
    {V M : Type} [Fintype V] [DecidableEq V]
    (G : TradingNetwork V) (Supplies : V → M) (Demands : V → M → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (Γ₀ : M → Finset V) (n : ℕ) :
    Γ₀ ≤ (PhiTradingNet G Supplies Demands)^[n] Γ₀ := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
    have h_step : (PhiTradingNet G Supplies Demands)^[k] Γ₀ ≤
        PhiTradingNet G Supplies Demands ((PhiTradingNet G Supplies Demands)^[k] Γ₀) :=
      phi_net_le (NetworkFeasIndirect G Supplies Demands)
        ((PhiTradingNet G Supplies Demands)^[k] Γ₀)
    have h_rw : (PhiTradingNet G Supplies Demands)^[k + 1] Γ₀ =
        PhiTradingNet G Supplies Demands ((PhiTradingNet G Supplies Demands)^[k] Γ₀) :=
      Function.iterate_succ_apply' (PhiTradingNet G Supplies Demands) k Γ₀
    rw [h_rw]
    exact le_trans ih h_step

section NetworkMoneyEmergence

variable [W : ActionFrame]


theorem network_universal_money_emergence
    [Finite Means] [Fintype Agent] [DecidableEq Agent]
    (G : TradingNetwork Agent) (Supplies : Agent → Means) (Demands : Agent → Means → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (seed : Agent) (m_star : Means) (Γ₀ : Means → Finset Agent)
    (h_seed : seed ∈ Γ₀ m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed) :
    ∃ (Γ_star : Means → Finset Agent) (n : ℕ),
      Γ_star = (PhiTradingNet G Supplies Demands)^[n] Γ₀ ∧
      PhiTradingNet G Supplies Demands Γ_star = Γ_star ∧
      IsNetworkUniversalMoney Γ_star m_star := by
  classical
  have ⟨n, hn⟩ := network_bourbaki_witt_convergence
    (NetworkFeasIndirect G Supplies Demands) Γ₀
  let Γ_star := (PhiTradingNet G Supplies Demands)^[n] Γ₀
  have h_fix : PhiTradingNet G Supplies Demands Γ_star = Γ_star := hn
  have h_le : Γ₀ ≤ Γ_star := le_iterate_phi_trading_net G Supplies Demands Γ₀ n
  have h_seed_star : seed ∈ Γ_star m_star := (h_le m_star) h_seed
  have h_univ : IsNetworkUniversalMoney Γ_star m_star := by
    dsimp [IsNetworkUniversalMoney]
    by_contra h_not_univ
    have ⟨k, j, hk, hj, hadj, hdem⟩ := h_conn (Γ_star m_star) h_seed_star h_not_univ
    have h_feas : NetworkFeasIndirect G Supplies Demands Γ_star k m_star :=
      ⟨j, hadj, hdem, hj⟩
    have h_in_phi : k ∈ PhiTradingNet G Supplies Demands Γ_star m_star := by
      dsimp [PhiTradingNet, PhiNet]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ k, h_feas⟩
    rw [h_fix] at h_in_phi
    exact hk h_in_phi
  exact ⟨Γ_star, n, rfl, h_fix, h_univ⟩


/-- Coupled Mengerian and network adoption reaches universal acceptance when
the candidate medium stays maximally marketable along the orbit and every
proper seed-containing cohort has an unmet adjacent demand. -/
theorem network_marketable_universal_money_emergence
    [Finite Means] [Fintype Agent] [DecidableEq Agent]
    (G : TradingNetwork Agent) (Supplies : Agent → Means)
    (Demands : Agent → Means → Prop)
    [∀ Γ i m, Decidable (NetworkMarketableAdopt G Supplies Demands Γ i m)]
    (seed : Agent) (m_star : Means) (Γ₀ : Means → Finset Agent)
    (h_seed : seed ∈ Γ₀ m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed)
    (h_max_iter : ∀ n : ℕ,
      NetworkIsMaxMarketable ((PhiNetworkMarketable G Supplies Demands)^[n] Γ₀) m_star) :
    ∃ (Γ_star : Means → Finset Agent) (n : ℕ),
      Γ_star = (PhiNetworkMarketable G Supplies Demands)^[n] Γ₀ ∧
      PhiNetworkMarketable G Supplies Demands Γ_star = Γ_star ∧
      NetworkIsMaxMarketable Γ_star m_star ∧
      IsNetworkUniversalMoney Γ_star m_star := by
  obtain ⟨n, hn⟩ := network_marketable_bourbaki_witt_convergence
    G Supplies Demands Γ₀
  let Γ_star := (PhiNetworkMarketable G Supplies Demands)^[n] Γ₀
  have h_fix : PhiNetworkMarketable G Supplies Demands Γ_star = Γ_star := hn
  have h_max : NetworkIsMaxMarketable Γ_star m_star := h_max_iter n
  have h_le : Γ₀ ≤ Γ_star :=
    le_iterate_phi_network_marketable G Supplies Demands Γ₀ n
  have h_seed_star : seed ∈ Γ_star m_star := (h_le m_star) h_seed
  have h_univ : IsNetworkUniversalMoney Γ_star m_star := by
    dsimp [IsNetworkUniversalMoney]
    by_contra h_not_univ
    obtain ⟨k, j, hk, hj, hadj, hdem⟩ :=
      h_conn (Γ_star m_star) h_seed_star h_not_univ
    have h_feas : NetworkFeasIndirect G Supplies Demands Γ_star k m_star :=
      ⟨j, hadj, hdem, hj⟩
    have h_adopt : NetworkMarketableAdopt G Supplies Demands Γ_star k m_star :=
      ⟨h_max, h_feas⟩
    have h_in_phi : k ∈ PhiNetworkMarketable G Supplies Demands Γ_star m_star := by
      dsimp [PhiNetworkMarketable, PhiNet]
      rw [Finset.mem_union, Finset.mem_filter]
      exact Or.inr ⟨Finset.mem_univ k, h_adopt⟩
    rw [h_fix] at h_in_phi
    exact hk h_in_phi
  exact ⟨Γ_star, n, rfl, h_fix, h_max, h_univ⟩

/-- At a fixed point, maximal marketability and connected unmet demand force
the seed's medium to become universally accepted. -/
theorem coupled_network_universal_money_emergence
    [Fintype Agent] [DecidableEq Agent]
    (G : TradingNetwork Agent) (Supplies : Agent → Means)
    (Demands : Agent → Means → Prop)
    (seed : Agent) (m_star : Means) (Γ_star : Means → Finset Agent)
    (h_seed : seed ∈ Γ_star m_star)
    (h_max : ∀ m' : Means, (Γ_star m').card ≤ (Γ_star m_star).card)
    (h_adoption_closed : ∀ i,
      NetworkMarketableAdopt G Supplies Demands Γ_star i m_star →
        i ∈ Γ_star m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed) :
    IsNetworkUniversalMoney Γ_star m_star := by
  dsimp [IsNetworkUniversalMoney]
  by_contra h_not_univ
  obtain ⟨k, j, hk, hj, hadj, hdem⟩ :=
    h_conn (Γ_star m_star) h_seed h_not_univ
  have h_adopt : NetworkMarketableAdopt G Supplies Demands Γ_star k m_star :=
    ⟨h_max, ⟨j, hadj, hdem, hj⟩⟩
  exact hk (h_adoption_closed k h_adopt)

end NetworkMoneyEmergence

/-- A complete two-agent trading network used to exhibit coexistence of
universally accepted media. -/
def TwoAgentCompleteTradingNetwork : TradingNetwork (Fin 2) where
  adjacent := fun i j => i ≠ j
  adj_symm := by
    intro i j h
    exact h.symm

/-- The existing marketable adoption operator specialized to the two-agent
model and its explicit supply and demand functions. -/
def twoAgentNetworkMarketableUpdate
    (Γ : Fin 2 → Finset (Fin 2)) : Fin 2 → Finset (Fin 2) := by
  letI : ∀ Γ' : Fin 2 → Finset (Fin 2), ∀ i m,
      Decidable (NetworkMarketableAdopt TwoAgentCompleteTradingNetwork
        (fun _ : Fin 2 => (0 : Fin 2))
        (fun (_ : Fin 2) (_ : Fin 2) => True) Γ' i m) := by
    intro Γ' i m
    unfold NetworkMarketableAdopt
    letI : Decidable (NetworkIsMaxMarketable Γ' m) := by
      unfold NetworkIsMaxMarketable
      exact Fintype.decidableForallFintype
    letI : Decidable (NetworkFeasIndirect TwoAgentCompleteTradingNetwork
        (fun _ : Fin 2 => (0 : Fin 2))
        (fun (_ : Fin 2) (_ : Fin 2) => True) Γ' i m) := by
      change Decidable (∃ j : Fin 2, i ≠ j ∧ True ∧ j ∈ Γ' m)
      exact Fintype.decidableExistsFintype
    infer_instance
  exact PhiNetworkMarketable TwoAgentCompleteTradingNetwork
    (fun _ : Fin 2 => (0 : Fin 2))
    (fun (_ : Fin 2) (_ : Fin 2) => True) Γ

/-- Starting with one agent accepting two equally marketable media, the
existing coupled adoption operator extends both to the other agent and then
stabilizes. Thus this operator alone does not imply a unique universal medium.
The witness uses the explicit demand predicate `True` and constant supply
already passed to the operator above. -/
theorem two_universal_media_can_coexist_at_network_fixed_point :
    ∃ Γ₀ Γ₁ : Fin 2 → Finset (Fin 2),
      Γ₀ ≠ Γ₁ ∧
      IsNetworkUniversalMoney Γ₁ 0 ∧
      IsNetworkUniversalMoney Γ₁ 1 ∧
      twoAgentNetworkMarketableUpdate Γ₀ = Γ₁ ∧
      twoAgentNetworkMarketableUpdate Γ₁ = Γ₁ := by
  let Γ₀ : Fin 2 → Finset (Fin 2) := fun _ => {0}
  let Γ₁ : Fin 2 → Finset (Fin 2) := fun _ => Finset.univ
  refine ⟨Γ₀, Γ₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_eval := congrFun h 0
    simp [Γ₀, Γ₁] at h_eval
  · change Γ₁ 0 = Finset.univ
    rfl
  · change Γ₁ 1 = Finset.univ
    rfl
  · funext m
    apply Finset.ext
    intro i
    cases i using Fin.cases with
    | zero => simp [twoAgentNetworkMarketableUpdate, PhiNetworkMarketable,
        PhiNet, Γ₀, Γ₁]
    | succ i =>
        have hi : i = 0 := by omega
        subst i
        simp [twoAgentNetworkMarketableUpdate, PhiNetworkMarketable,
          PhiNet, Γ₀, Γ₁, NetworkMarketableAdopt, NetworkIsMaxMarketable,
          NetworkFeasIndirect, TwoAgentCompleteTradingNetwork]
  · funext m
    simp [twoAgentNetworkMarketableUpdate, PhiNetworkMarketable, PhiNet, Γ₁]


def EndogenousPhiNet {V M : Type} [Fintype V] [DecidableEq V]
    (RetainOrAdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (RetainOrAdoptRule Γ i m)]
    (Γ : M → Finset V) (m : M) : Finset V :=
  Finset.univ.filter (fun i => RetainOrAdoptRule Γ i m)


theorem demonetization_collapse
    {V M : Type} [Fintype V] [DecidableEq V]
    (RetainOrAdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (RetainOrAdoptRule Γ i m)]
    (Γ : M → Finset V) (m : M)
    (h_collapse : ∀ i : V, ¬ RetainOrAdoptRule Γ i m) :
    EndogenousPhiNet RetainOrAdoptRule Γ m = ∅ := by
  classical
  ext i
  simp [EndogenousPhiNet, h_collapse i]


theorem endogenous_money_retention_and_expansion
    {V M : Type} [Fintype V] [DecidableEq V]
    (RetainOrAdoptRule : (M → Finset V) → V → M → Prop)
    [∀ Γ i m, Decidable (RetainOrAdoptRule Γ i m)]
    (Γ : M → Finset V) (m : M)
    (h_retain : ∀ i ∈ Γ m, RetainOrAdoptRule Γ i m) :
    Γ m ⊆ EndogenousPhiNet RetainOrAdoptRule Γ m := by
  classical
  intro i hi
  simp [EndogenousPhiNet, h_retain i hi]


def RingTradingNetwork (N : ℕ) (_hN : 3 ≤ N) : TradingNetwork (Fin N) where
  adjacent := fun i j => (j.val = (i.val + 1) % N) ∨ (i.val = (j.val + 1) % N)
  adj_symm := by
    intro i j h
    rcases h with h1 | h2
    · right; exact h1
    · left; exact h2


def RingDemands (N : ℕ) (i : Fin N) (m : Fin N) : Prop :=
  m.val = (i.val + 1) % N

/-- No two agents on a ring of at least three nodes mutually demand each
other's good, so direct barter cannot satisfy both directed demands. -/
theorem ring_direct_barter_failure (N : ℕ) (hN : 3 ≤ N) (i j : Fin N) :
    ¬ (RingDemands N i j ∧ RingDemands N j i) := by
  intro ⟨h_ij, h_ji⟩
  dsimp [RingDemands] at h_ij h_ji
  have hi : i.val < N := i.isLt
  have hj : j.val < N := j.isLt
  have h_mod_i : (i.val + 1) % N = if i.val + 1 = N then 0 else i.val + 1 := by
    split_ifs with heq
    · rw [heq, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have h_mod_j : (j.val + 1) % N = if j.val + 1 = N then 0 else j.val + 1 := by
    split_ifs with heq
    · rw [heq, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [h_mod_i] at h_ij
  rw [h_mod_j] at h_ji
  split_ifs at h_ij h_ji <;> omega


def ThreeAgentTradingNetwork : TradingNetwork (Fin 3) where
  adjacent := fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ (j = 0 ∨ j = 2)) ∨ (i = 2 ∧ j = 1)
  adj_symm := by
    intro i j h
    fin_cases i <;> fin_cases j <;> revert h <;> decide

theorem three_agent_network_money_emergence_witness
    [∀ Γ i m, Decidable (NetworkFeasIndirect ThreeAgentTradingNetwork id
      (fun i m => (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)) Γ i m)] :
    let G := ThreeAgentTradingNetwork
    let supplies : Fin 3 → Fin 3 := id
    let demands : Fin 3 → Fin 3 → Prop := fun i m =>
      (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)
    let Γ₀ : Fin 3 → Finset (Fin 3) := fun m =>
      if m = 0 then {2} else if m = 1 then {0} else {1}
    (∀ m : Fin 3, (Γ₀ m).card = 1) ∧
    ¬ IsNetworkUniversalMoney Γ₀ 0 ∧
    ¬ IsNetworkUniversalMoney (PhiTradingNet G supplies demands Γ₀) 0 ∧
    IsNetworkUniversalMoney ((PhiTradingNet G supplies demands)^[2] Γ₀) 0 := by
  classical
  intro G supplies demands Γ₀
  have h_init_cards : ∀ m : Fin 3, (Γ₀ m).card = 1 := by
    intro m
    fin_cases m <;> decide
  have h_init_not_univ : ¬ IsNetworkUniversalMoney Γ₀ 0 := by
    dsimp [IsNetworkUniversalMoney, Γ₀]
    decide
  let Φ := PhiTradingNet G supplies demands
  let Γ₁ := Φ Γ₀
  have h_step1_not_univ : ¬ IsNetworkUniversalMoney Γ₁ 0 := by
    dsimp [IsNetworkUniversalMoney]
    intro h_univ
    have h_mem0 : (0 : Fin 3) ∈ Γ₁ 0 := by
      rw [h_univ]
      exact Finset.mem_univ 0
    dsimp [Γ₁, Φ, PhiTradingNet, PhiNet] at h_mem0
    rw [Finset.mem_union, Finset.mem_filter] at h_mem0
    rcases h_mem0 with h_init | ⟨_, ⟨j, hadj, hdem, hj⟩⟩
    · dsimp [Γ₀] at h_init
      revert h_init; decide
    · fin_cases j <;> revert hadj hdem hj <;>
        dsimp [G, ThreeAgentTradingNetwork, demands, supplies, Γ₀] <;> decide
  have h_step2 : IsNetworkUniversalMoney ((PhiTradingNet G supplies demands)^[2] Γ₀) 0 := by
    dsimp [IsNetworkUniversalMoney]
    change Φ Γ₁ 0 = Finset.univ
    apply Finset.eq_univ_of_forall
    intro i
    have h_in_g0_2 : (2 : Fin 3) ∈ Γ₀ 0 := by
      dsimp [Γ₀]
      decide
    have h_sub01 : Γ₀ 0 ⊆ Γ₁ 0 := Finset.subset_union_left
    have h_sub12 : Γ₁ 0 ⊆ Φ Γ₁ 0 := Finset.subset_union_left
    have h_in_g1_2 : (2 : Fin 3) ∈ Γ₁ 0 := h_sub01 h_in_g0_2
    have h_in_g2_2 : (2 : Fin 3) ∈ Φ Γ₁ 0 := h_sub12 h_in_g1_2
    have h_feas_1 : NetworkFeasIndirect G supplies demands Γ₀ 1 0 := by
      dsimp [NetworkFeasIndirect]
      refine ⟨2, ?_, ?_, h_in_g0_2⟩
      · dsimp [G, ThreeAgentTradingNetwork]; decide
      · dsimp [demands, supplies]; decide
    have h_in_g1_1 : (1 : Fin 3) ∈ Γ₁ 0 := by
      dsimp [Γ₁, Φ, PhiTradingNet, PhiNet]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ 1, h_feas_1⟩
    have h_in_g2_1 : (1 : Fin 3) ∈ Φ Γ₁ 0 := h_sub12 h_in_g1_1
    have h_feas_0 : NetworkFeasIndirect G supplies demands Γ₁ 0 0 := by
      dsimp [NetworkFeasIndirect]
      refine ⟨1, ?_, ?_, h_in_g1_1⟩
      · dsimp [G, ThreeAgentTradingNetwork]; decide
      · dsimp [demands, supplies]; decide
    have h_in_g2_0 : (0 : Fin 3) ∈ Φ Γ₁ 0 := by
      dsimp [Φ, PhiTradingNet, PhiNet]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ 0, h_feas_0⟩
    fin_cases i
    · exact h_in_g2_0
    · exact h_in_g2_1
    · exact h_in_g2_2
  exact ⟨h_init_cards, h_init_not_univ, h_step1_not_univ, h_step2⟩

/-- The three-agent cycle is connected along the listed wants. -/
theorem three_agent_network_wants_connected :
    let G := ThreeAgentTradingNetwork
    let supplies : Fin 3 → Fin 3 := id
    let demands : Fin 3 → Fin 3 → Prop := fun i m =>
      (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)
    NetworkWantsConnected G supplies demands 2 := by
  intro G supplies demands S h2 h_ne
  by_cases h1 : (1 : Fin 3) ∈ S
  · have h0 : (0 : Fin 3) ∉ S := by
      intro h0_in
      apply h_ne
      apply Finset.eq_univ_of_forall
      intro x
      fin_cases x
      · exact h0_in
      · exact h1
      · exact h2
    refine ⟨0, 1, h0, h1, ?_, ?_⟩
    · dsimp [G, ThreeAgentTradingNetwork]; exact Or.inl ⟨rfl, rfl⟩
    · dsimp [demands, supplies]; exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨1, 2, h1, h2, ?_, ?_⟩
    · dsimp [G, ThreeAgentTradingNetwork]; exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
    · dsimp [demands, supplies]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)


theorem asymmetric_unique_network_money_emergence_witness
    [∀ Γ i m, Decidable (NetworkFeasIndirect ThreeAgentTradingNetwork id
      (fun i m => (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)) Γ i m)] :
    let G := ThreeAgentTradingNetwork
    let supplies : Fin 3 → Fin 3 := id
    let demands : Fin 3 → Fin 3 → Prop := fun i m =>
      (i = 0 ∧ m = 1) ∨ (i = 1 ∧ m = 2) ∨ (i = 2 ∧ m = 0)
    let Γ₀ : Fin 3 → Finset (Fin 3) := fun m =>
      if m = 0 then {2} else if m = 1 then {0} else ∅
    let Φ := PhiTradingNet G supplies demands
    let Γ_star := Φ^[2] Γ₀
    IsNetworkUniversalMoney Γ_star 0 ∧
    (∀ m : Fin 3, m ≠ 0 → ¬ IsNetworkUniversalMoney Γ_star m) := by
  classical
  intro G supplies demands Γ₀ Φ Γ_star
  have h_univ0 : IsNetworkUniversalMoney Γ_star 0 := by
    dsimp [IsNetworkUniversalMoney, Γ_star, Φ]
    apply Finset.eq_univ_of_forall
    intro i
    have h_in_g0_2 : (2 : Fin 3) ∈ Γ₀ 0 := by dsimp [Γ₀]; decide
    have h_sub01 : Γ₀ 0 ⊆ (Φ Γ₀) 0 := by
      dsimp [Φ, PhiTradingNet, PhiNet]
      exact Finset.subset_union_left
    have h_sub12 : (Φ Γ₀) 0 ⊆ (Φ (Φ Γ₀)) 0 := by
      dsimp [Φ, PhiTradingNet, PhiNet]
      exact Finset.subset_union_left
    have h_in_g1_2 : (2 : Fin 3) ∈ (Φ Γ₀) 0 := h_sub01 h_in_g0_2
    have h_in_g2_2 : (2 : Fin 3) ∈ (Φ (Φ Γ₀)) 0 := h_sub12 h_in_g1_2
    have h_feas_1 : NetworkFeasIndirect G supplies demands Γ₀ 1 0 := by
      dsimp [NetworkFeasIndirect]
      refine ⟨2, ?_, ?_, h_in_g0_2⟩
      · dsimp [G, ThreeAgentTradingNetwork]; decide
      · dsimp [demands, supplies]; decide
    have h_in_g1_1 : (1 : Fin 3) ∈ (Φ Γ₀) 0 := by
      dsimp [Φ, PhiTradingNet, PhiNet]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ 1, h_feas_1⟩
    have h_in_g2_1 : (1 : Fin 3) ∈ (Φ (Φ Γ₀)) 0 := h_sub12 h_in_g1_1
    have h_feas_0 : NetworkFeasIndirect G supplies demands (Φ Γ₀) 0 0 := by
      dsimp [NetworkFeasIndirect]
      refine ⟨1, ?_, ?_, h_in_g1_1⟩
      · dsimp [G, ThreeAgentTradingNetwork]; decide
      · dsimp [demands, supplies]; decide
    have h_in_g2_0 : (0 : Fin 3) ∈ (Φ (Φ Γ₀)) 0 := by
      dsimp [Φ, PhiTradingNet, PhiNet]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ 0, h_feas_0⟩
    fin_cases i
    · exact h_in_g2_0
    · exact h_in_g2_1
    · exact h_in_g2_2
  have h_not_univ_m : ∀ m : Fin 3, m ≠ 0 → ¬ IsNetworkUniversalMoney Γ_star m := by
    intro m hm h_univ
    fin_cases m
    · exact hm rfl
    · dsimp [IsNetworkUniversalMoney] at h_univ
      have h_mem1 : (1 : Fin 3) ∈ Γ_star 1 := by rw [h_univ]; exact Finset.mem_univ 1
      dsimp [Γ_star, Φ, PhiTradingNet, PhiNet] at h_mem1
      rw [Finset.mem_union, Finset.mem_filter] at h_mem1
      rcases h_mem1 with h1 | ⟨_, ⟨j, hadj, hdem, hj⟩⟩
      · rw [Finset.mem_union, Finset.mem_filter] at h1
        rcases h1 with h0 | ⟨_, ⟨k, hadj_k, hdem_k, hk⟩⟩
        · revert h0; dsimp [Γ₀]; decide
        · fin_cases k <;> revert hadj_k hdem_k hk <;>
            dsimp [G, ThreeAgentTradingNetwork, demands, supplies, Γ₀] <;> decide
      · fin_cases j
        · revert hdem; dsimp [demands, supplies]; decide
        · revert hadj; dsimp [G, ThreeAgentTradingNetwork]; decide
        · dsimp [Φ, PhiTradingNet, PhiNet] at hj
          rw [Finset.mem_union, Finset.mem_filter] at hj
          rcases hj with hj0 | ⟨_, ⟨k, hadj_k, _, hk⟩⟩
          · revert hj0; dsimp [Γ₀]; decide
          · fin_cases k <;> revert hadj_k hk <;>
              dsimp [G, ThreeAgentTradingNetwork, Γ₀] <;> decide
    · dsimp [IsNetworkUniversalMoney] at h_univ
      have h_mem0 : (0 : Fin 3) ∈ Γ_star 2 := by rw [h_univ]; exact Finset.mem_univ 0
      have h_empty : Γ₀ 2 = ∅ := rfl
      dsimp [Γ_star, Φ, PhiTradingNet, PhiNet] at h_mem0
      rw [Finset.mem_union, Finset.mem_filter] at h_mem0
      rcases h_mem0 with h1 | ⟨_, ⟨j, _, _, hj⟩⟩
      · rw [Finset.mem_union, Finset.mem_filter] at h1
        rcases h1 with h0 | ⟨_, ⟨k, _, _, hk⟩⟩
        · rw [h_empty] at h0; exact Finset.notMem_empty 0 h0
        · rw [h_empty] at hk; exact Finset.notMem_empty k hk
      · dsimp [Φ, PhiTradingNet, PhiNet] at hj
        rw [Finset.mem_union, Finset.mem_filter] at hj
        rcases hj with hj0 | ⟨_, ⟨k, _, _, hk⟩⟩
        · rw [h_empty] at hj0; exact Finset.notMem_empty j hj0
        · rw [h_empty] at hk; exact Finset.notMem_empty k hk
  exact ⟨h_univ0, h_not_univ_m⟩


end NetworkAdoption

-- Section 3: Discrete Marginal Pairs


theorem marginal_pairs_equilibrium (v_b v_s : ℕ → ℕ) (r_star : ℕ)
    (P : ℕ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + 1) ≤ P)
    (hP_max : P + 1 ≤ min (v_b r_star + 1) (v_s (r_star + 1))) :
    v_s r_star ≤ P ∧ P ≤ v_b r_star ∧
    v_b (r_star + 1) < P ∧ P < v_s (r_star + 1) := by
  have h1 : v_s r_star ≤ P := le_trans (le_max_left _ _) hP_min
  have h2 : P ≤ v_b r_star := by
    have : P + 1 ≤ v_b r_star + 1 := le_trans hP_max (min_le_left _ _)
    omega
  have h3_le : v_b (r_star + 1) + 1 ≤ P := le_trans (le_max_right _ _) hP_min
  have h3 : v_b (r_star + 1) < P := by omega
  have h4_le : P + 1 ≤ v_s (r_star + 1) := le_trans hP_max (min_le_right _ _)
  have h4 : P < v_s (r_star + 1) := by omega
  exact ⟨h1, h2, h3, h4⟩

/-- Price bracket non-emptiness: P_min ≤ P_max whenever market-clearing bounds are satisfied. -/
theorem price_bracket_width_nonneg (v_b v_s : ℕ → ℕ) (r_star : ℕ)
    (P : ℕ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + 1) ≤ P)
    (hP_max : P + 1 ≤ min (v_b r_star + 1) (v_s (r_star + 1))) :
    max (v_s r_star) (v_b (r_star + 1) + 1) ≤ v_b r_star ∧
      max (v_s r_star) (v_b (r_star + 1) + 1) + 1 ≤ v_s (r_star + 1) := by
  have hbuyer : P ≤ v_b r_star := by
    have := le_trans hP_max (min_le_left _ _)
    omega
  have hnext : P + 1 ≤ v_s (r_star + 1) :=
    le_trans hP_max (min_le_right _ _)
  refine ⟨le_trans hP_min hbuyer, ?_⟩
  have hP_lt : P < v_s (r_star + 1) := by omega
  exact Nat.succ_le_of_lt (lt_of_le_of_lt hP_min hP_lt)


section MultilateralMarket

variable [W : ActionFrame]


theorem purposeful_marginal_pairs_deterrence
    (v_b v_s : ℕ → ℕ) (r_star : ℕ) (P : ℕ)
    (hP_min : max (v_s r_star) (v_b (r_star + 1) + 1) ≤ P)
    (hP_max : P + 1 ≤ min (v_b r_star + 1) (v_s (r_star + 1)))
    (i_ext_buyer i_ext_seller : Agent) (t : Moment) (h : History)
    (α_buy α_sell : Action)
    (b0_b b_buy b0_s b_sell : Means → ℕ)
    (h_dom_b : v_b (r_star + 1) < P →
      W.SubjectiveTeleologicalDominates i_ext_buyer t h b0_b b_buy)
    (h_dom_s : P < v_s (r_star + 1) →
      W.SubjectiveTeleologicalDominates i_ext_seller t h b0_s b_sell)
    (h_out_b0 : End_of i_ext_buyer α₀ t h = W.BundleEnd b0_b)
    (h_out_buy : End_of i_ext_buyer α_buy t h = W.BundleEnd b_buy)
    (h_out_s0 : End_of i_ext_seller α₀ t h = W.BundleEnd b0_s)
    (h_out_sell : End_of i_ext_seller α_sell t h = W.BundleEnd b_sell) :
    ¬ ActivePurposefulAct i_ext_buyer t h α_buy ∧
    ¬ ActivePurposefulAct i_ext_seller t h α_sell := by
  have ⟨_, _, h_b_deter, h_s_deter⟩ := marginal_pairs_equilibrium v_b v_s r_star P hP_min hP_max
  have h_buyer_unease :
      ¬ Preference i_ext_buyer t h (End_of i_ext_buyer α_buy t h) (End_of i_ext_buyer α₀ t h) := by
    rw [h_out_buy, h_out_b0]
    have h_dom := h_dom_b h_b_deter
    have h_pref :=
      W.teleological_bundle_dominance_induces_preference i_ext_buyer t h b0_b b_buy h_dom
    exact W.pref_asymm i_ext_buyer t h h_pref
  have h_seller_unease :
      ¬ Preference i_ext_seller t h
        (End_of i_ext_seller α_sell t h) (End_of i_ext_seller α₀ t h) := by
    rw [h_out_sell, h_out_s0]
    have h_dom := h_dom_s h_s_deter
    have h_pref :=
      W.teleological_bundle_dominance_induces_preference i_ext_seller t h b0_s b_sell h_dom
    exact W.pref_asymm i_ext_seller t h h_pref
  exact ⟨fun h_purp => h_buyer_unease h_purp.2, fun h_purp => h_seller_unease h_purp.2⟩

end MultilateralMarket


-- Section 4b: Multilateral Trade and Endowment Conservation

/-- Replacing two entries with the same aggregate preserves a finite sum. -/
theorem finset_sum_pair_update {α : Type*}
    (S : Finset α) (b s : α) (hb : b ∈ S) (hs : s ∈ S) (hbs : b ≠ s)
    (f g : α → ℕ) (h_pair : g b + g s = f b + f s)
    (h_rest : ∀ a ∈ S, a ≠ b → a ≠ s → g a = f a) :
    (∑ a ∈ S, g a) = ∑ a ∈ S, f a := by
  classical
  have hs' : s ∈ S.erase b := Finset.mem_erase.mpr ⟨hbs.symm, hs⟩
  have h_rest_sum :
      (∑ a ∈ (S.erase b).erase s, g a) = ∑ a ∈ (S.erase b).erase s, f a := by
    apply Finset.sum_congr rfl
    intro a ha
    have h_as := Finset.mem_erase.mp ha
    have h_ab := Finset.mem_erase.mp h_as.2
    exact h_rest a h_ab.2 h_ab.1 h_as.1
  rw [← Finset.add_sum_erase S g hb, ← Finset.add_sum_erase (S.erase b) g hs',
      ← Finset.add_sum_erase S f hb, ← Finset.add_sum_erase (S.erase b) f hs', h_rest_sum]
  omega


structure MultilateralCohortMarket (V M : Type*) [DecidableEq V] where
  Buyers : Finset V
  Sellers : Finset V
  h_disjoint : Disjoint Buyers Sellers
  v_b : V → ℕ
  v_s : V → ℕ
  m_good : M
  m_money : M
  h_distinct : m_good ≠ m_money

/-- Buyers whose value is at least `P`. -/
def MultilateralCohortMarket.ActiveBuyers {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) : Finset V :=
  M.Buyers.filter (fun b => P ≤ M.v_b b)

/-- Sellers whose value is at most `P`. -/
def MultilateralCohortMarket.ActiveSellers {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) : Finset V :=
  M.Sellers.filter (fun s => M.v_s s ≤ P)

/-- Buyers whose value is below `P`. -/
def MultilateralCohortMarket.ExtraMarginalBuyers {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) : Finset V :=
  M.Buyers.filter (fun b => M.v_b b < P)

/-- Sellers whose value is above `P`. -/
def MultilateralCohortMarket.ExtraMarginalSellers {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) : Finset V :=
  M.Sellers.filter (fun s => P < M.v_s s)

/-- Each buyer is active or extra-marginal at price `P`. -/
theorem MultilateralCohortMarket.buyer_partition {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) :
    (∀ b ∈ M.ActiveBuyers P, b ∉ M.ExtraMarginalBuyers P) ∧
    (∀ b ∈ M.Buyers, b ∈ M.ActiveBuyers P ∨ b ∈ M.ExtraMarginalBuyers P) := by
  constructor
  · intro b hb hb_ext
    have h_le := (Finset.mem_filter.mp hb).2
    have h_lt := (Finset.mem_filter.mp hb_ext).2
    exact Nat.not_lt_of_le h_le h_lt
  · intro b hb
    by_cases hP : P ≤ M.v_b b
    · exact Or.inl (Finset.mem_filter.mpr ⟨hb, hP⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hb, Nat.lt_of_not_le hP⟩)

/-- Each seller is active or extra-marginal at price `P`. -/
theorem MultilateralCohortMarket.seller_partition {V M : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V M) (P : ℕ) :
    (∀ s ∈ M.ActiveSellers P, s ∉ M.ExtraMarginalSellers P) ∧
    (∀ s ∈ M.Sellers, s ∈ M.ActiveSellers P ∨ s ∈ M.ExtraMarginalSellers P) := by
  constructor
  · intro s hs hs_ext
    have h_le := (Finset.mem_filter.mp hs).2
    have h_lt := (Finset.mem_filter.mp hs_ext).2
    exact Nat.not_lt_of_le h_le h_lt
  · intro s hs
    by_cases hP : M.v_s s ≤ P
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs, hP⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hs, Nat.lt_of_not_le hP⟩)


theorem multilateral_cohort_pairwise_trade_conservation
    {V C : Type*} [DecidableEq V]
    (M : MultilateralCohortMarket V C)
    (b s : V) (hb : b ∈ M.Buyers) (hs : s ∈ M.Sellers)
    (omega_pre omega_post : V → C → ℕ)
    (m : C)
    (h_pair_conserved : omega_post b m + omega_post s m = omega_pre b m + omega_pre s m)
    (h_rest_invariant : ∀ a ∈ M.Buyers ∪ M.Sellers,
      a ≠ b → a ≠ s → omega_post a m = omega_pre a m) :
    (∑ a ∈ M.Buyers ∪ M.Sellers, omega_post a m) =
      ∑ a ∈ M.Buyers ∪ M.Sellers, omega_pre a m := by
  have hbs : b ≠ s := by
    intro h_eq
    exact (Finset.disjoint_left.mp M.h_disjoint) hb (h_eq ▸ hs)
  exact finset_sum_pair_update (M.Buyers ∪ M.Sellers) b s
    (Finset.mem_union_left _ hb) (Finset.mem_union_right _ hs) hbs
    (fun a => omega_pre a m) (fun a => omega_post a m) h_pair_conserved h_rest_invariant

section ActionFrameMultilateralMarket

variable [W : ActionFrame]


theorem multilateral_extra_marginal_deterrence
    (M : MultilateralCohortMarket W.Agent W.Means) (P : ℕ) (t : Moment) (h : History)
    (α_buy α_sell : Action)
    (h_buyer_unease : ∀ b ∈ M.ExtraMarginalBuyers P,
      ¬ Preference b t h (End_of b α_buy t h) (End_of b α₀ t h))
    (h_seller_unease : ∀ s ∈ M.ExtraMarginalSellers P,
      ¬ Preference s t h (End_of s α_sell t h) (End_of s α₀ t h)) :
    (∀ b ∈ M.ExtraMarginalBuyers P, ¬ ActivePurposefulAct b t h α_buy) ∧
    (∀ s ∈ M.ExtraMarginalSellers P, ¬ ActivePurposefulAct s t h α_sell) := by
  constructor
  · intro b hb h_act
    exact (h_buyer_unease b hb) h_act.2
  · intro s hs h_act
    exact (h_seller_unease s hs) h_act.2

/-- The same deterrence result for participant-specific candidate actions. -/
theorem multilateral_extra_marginal_deterrence_of_actions
    (M : MultilateralCohortMarket W.Agent W.Means) (P : ℕ) (t : Moment) (h : History)
    (α_buy α_sell : Agent → Action)
    (h_buyer_unease : ∀ b ∈ M.ExtraMarginalBuyers P,
      ¬ Preference b t h (End_of b (α_buy b) t h) (End_of b α₀ t h))
    (h_seller_unease : ∀ s ∈ M.ExtraMarginalSellers P,
      ¬ Preference s t h (End_of s (α_sell s) t h) (End_of s α₀ t h)) :
    (∀ b ∈ M.ExtraMarginalBuyers P, ¬ ActivePurposefulAct b t h (α_buy b)) ∧
    (∀ s ∈ M.ExtraMarginalSellers P, ¬ ActivePurposefulAct s t h (α_sell s)) := by
  constructor
  · intro b hb hact
    exact h_buyer_unease b hb hact.2
  · intro s hs hact
    exact h_seller_unease s hs hact.2


variable [BilateralExchangeFrame W]

/-- An observed clearing event: the selected seller offers the good for money,
the selected buyer accepts, extra-marginal appraisals are supplied, and all
other cohort members are inert. -/
structure MultilateralClearingScenario
    (M : MultilateralCohortMarket W.Agent W.Means) where
  price : ℕ
  moment : Moment
  next : Moment
  history : History
  buyer : W.Agent
  seller : W.Agent
  buyerMember : buyer ∈ M.Buyers
  sellerMember : seller ∈ M.Sellers
  successor : IsNextMoment Precedence W.mem_hist moment next history
  buyerCandidateAction : W.Agent → Action
  sellerCandidateAction : W.Agent → Action
  buyerUnease : ∀ b ∈ M.ExtraMarginalBuyers price,
    ¬ Preference b moment history
      (End_of b (buyerCandidateAction b) moment history)
      (End_of b α₀ moment history)
  sellerUnease : ∀ s ∈ M.ExtraMarginalSellers price,
    ¬ Preference s moment history
      (End_of s (sellerCandidateAction s) moment history)
      (End_of s α₀ moment history)
  sellerOfferEnacted : enacted seller moment history =
    W.Offer seller buyer 1 M.m_good price M.m_money
  buyerAcceptEnacted : enacted buyer moment history =
    W.Accept buyer seller 1 M.m_good price M.m_money
  selectedBuyerAction : buyerCandidateAction buyer =
    W.Accept buyer seller 1 M.m_good price M.m_money
  selectedSellerAction : sellerCandidateAction seller =
    W.Offer seller buyer 1 M.m_good price M.m_money
  otherParticipantsIdle : ∀ a ∈ M.Buyers ∪ M.Sellers,
    a ≠ buyer → a ≠ seller → enacted a moment history = α₀
  otherParticipantsUninvaded : ∀ a ∈ M.Buyers ∪ M.Sellers,
    a ≠ buyer → a ≠ seller → ∀ j, ¬ W.IsInvasiveOn (enacted j moment history) a

/-- Named outcome of one certified multilateral clearing step. -/
structure MultilateralClearingConclusion
    (M : MultilateralCohortMarket W.Agent W.Means)
    (S : MultilateralClearingScenario M) : Prop where
  activeBuyerValuation : ∀ b ∈ M.ActiveBuyers S.price, S.price ≤ M.v_b b
  activeSellerValuation : ∀ s ∈ M.ActiveSellers S.price, M.v_s s ≤ S.price
  sellerDeliversGood : omega S.seller S.next S.history M.m_good + 1 =
    omega S.seller S.moment S.history M.m_good
  buyerReceivesGood : omega S.buyer S.next S.history M.m_good =
    omega S.buyer S.moment S.history M.m_good + 1
  sellerReceivesMoney : omega S.seller S.next S.history M.m_money =
    omega S.seller S.moment S.history M.m_money + S.price
  buyerPaysMoney : omega S.buyer S.next S.history M.m_money + S.price =
    omega S.buyer S.moment S.history M.m_money
  extraBuyerDeterrence : ∀ b ∈ M.ExtraMarginalBuyers S.price,
    ¬ ActivePurposefulAct b S.moment S.history (S.buyerCandidateAction b)
  extraSellerDeterrence : ∀ s ∈ M.ExtraMarginalSellers S.price,
    ¬ ActivePurposefulAct s S.moment S.history (S.sellerCandidateAction s)
  goodConservation :
    (∑ a ∈ M.Buyers ∪ M.Sellers, omega a S.next S.history M.m_good) =
      ∑ a ∈ M.Buyers ∪ M.Sellers, omega a S.moment S.history M.m_good
  moneyConservation :
    (∑ a ∈ M.Buyers ∪ M.Sellers, omega a S.next S.history M.m_money) =
      ∑ a ∈ M.Buyers ∪ M.Sellers, omega a S.moment S.history M.m_money


theorem action_frame_multilateral_market_clearing
    (M : MultilateralCohortMarket W.Agent W.Means)
    (S : MultilateralClearingScenario M) : MultilateralClearingConclusion M S := by
  have h_buyer_ne_seller : S.buyer ≠ S.seller := by
    intro h_eq
    exact (Finset.disjoint_left.mp M.h_disjoint) S.buyerMember (h_eq ▸ S.sellerMember)
  have h_seller_ne_buyer := h_buyer_ne_seller.symm
  have ⟨h_cons_good, h_cons_money⟩ := bilateral_exchange_conserves_means
    S.seller S.buyer S.moment S.next S.history 1 M.m_good S.price M.m_money
    h_seller_ne_buyer M.h_distinct S.successor S.sellerOfferEnacted
    S.buyerAcceptEnacted
  have h_directional := bilateral_exchange_commodity_transfers
    S.seller S.buyer S.moment S.next S.history 1 M.m_good S.price M.m_money
    h_seller_ne_buyer M.h_distinct S.successor S.sellerOfferEnacted
    S.buyerAcceptEnacted
  have h_rest : ∀ a ∈ M.Buyers ∪ M.Sellers,
      a ≠ S.buyer → a ≠ S.seller → ∀ m,
        omega a S.next S.history m = omega a S.moment S.history m := by
    intro a ha hab has m
    have h_a_inert := S.otherParticipantsIdle a ha hab has
    have h_uninv := S.otherParticipantsUninvaded a ha hab has
    have h_law := W.law_in_re_transition a S.moment S.next S.history α₀ m
      alpha_zero_not_trade h_uninv h_a_inert S.successor
    rw [W.use_means_alpha_zero, W.yield_means_alpha_zero] at h_law
    rw [Nat.add_zero, Nat.add_zero] at h_law
    exact h_law
  have h_good := multilateral_cohort_pairwise_trade_conservation M S.buyer S.seller
    S.buyerMember S.sellerMember
    (fun a m => omega a S.moment S.history m)
    (fun a m => omega a S.next S.history m) M.m_good (by omega)
    (fun a ha hab has => h_rest a ha hab has M.m_good)
  have h_money := multilateral_cohort_pairwise_trade_conservation M S.buyer S.seller
    S.buyerMember S.sellerMember
    (fun a m => omega a S.moment S.history m)
    (fun a m => omega a S.next S.history m) M.m_money (by omega)
    (fun a ha hab has => h_rest a ha hab has M.m_money)
  have h_active_buyers : ∀ b ∈ M.ActiveBuyers S.price, S.price ≤ M.v_b b := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  have h_active_sellers : ∀ s ∈ M.ActiveSellers S.price, M.v_s s ≤ S.price := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2
  exact {
    activeBuyerValuation := h_active_buyers
    activeSellerValuation := h_active_sellers
    sellerDeliversGood := h_directional.1
    buyerReceivesGood := h_directional.2.1
    sellerReceivesMoney := h_directional.2.2.1
    buyerPaysMoney := h_directional.2.2.2
    extraBuyerDeterrence := by
      intro b hb hp
      exact S.buyerUnease b hb hp.2
    extraSellerDeterrence := by
      intro s hs hp
      exact S.sellerUnease s hs hp.2
    goodConservation := h_good
    moneyConservation := h_money }

/-- An ActionFrame clearing certificate requires the selected market transfer
to be a purposeful bilateral exchange.  Finite market algorithms can produce
the event data, while this interface and its consequences apply to any
`ActionFrame`. -/
structure PurposefulMultilateralClearingRound
    (M : MultilateralCohortMarket W.Agent W.Means) where
  clearing : MultilateralClearingScenario M
  purposefulExchange : BilateralExchange clearing.seller clearing.buyer
    clearing.moment clearing.history 1 M.m_good clearing.price M.m_money

/-- The matched seller and buyer both perform active purposeful actions in a
purposeful multilateral clearing round. -/
theorem PurposefulMultilateralClearingRound.matched_parties_active
    {M : MultilateralCohortMarket W.Agent W.Means}
    (S : PurposefulMultilateralClearingRound M) :
    ActivePurposefulAct S.clearing.seller S.clearing.moment S.clearing.history
      (W.Offer S.clearing.seller S.clearing.buyer 1 M.m_good
        S.clearing.price M.m_money) ∧
    ActivePurposefulAct S.clearing.buyer S.clearing.moment S.clearing.history
      (W.Accept S.clearing.buyer S.clearing.seller 1 M.m_good
        S.clearing.price M.m_money) := by
  rcases S.purposefulExchange with ⟨_, _, ⟨_, hSeller, hOfferNe, hBuyer, hAcceptNe⟩⟩
  exact ⟨(active_purposeful_act_iff_ne_alpha_zero _ _ _ _).2 ⟨hSeller, hOfferNe⟩,
    (active_purposeful_act_iff_ne_alpha_zero _ _ _ _).2 ⟨hBuyer, hAcceptNe⟩⟩

/-- Extra-marginal agents are deterred by the ActionFrame's purposeful
choice relation at the realized clearing price. -/
theorem PurposefulMultilateralClearingRound.extra_marginal_deterrence
    {M : MultilateralCohortMarket W.Agent W.Means}
    (S : PurposefulMultilateralClearingRound M) :
    (∀ b ∈ M.ExtraMarginalBuyers S.clearing.price,
      ¬ ActivePurposefulAct b S.clearing.moment S.clearing.history
        (S.clearing.buyerCandidateAction b)) ∧
    (∀ s ∈ M.ExtraMarginalSellers S.clearing.price,
      ¬ ActivePurposefulAct s S.clearing.moment S.clearing.history
        (S.clearing.sellerCandidateAction s)) :=
  multilateral_extra_marginal_deterrence_of_actions M S.clearing.price
    S.clearing.moment S.clearing.history S.clearing.buyerCandidateAction
    S.clearing.sellerCandidateAction S.clearing.buyerUnease S.clearing.sellerUnease

/-- A buyer's reservation amount is grounded in the frame's preference
relation: offers at or below it are preferred to idling, while offers above it
are rejected by that same preference relation. -/
structure PurposefulReservationPair
    (M : MultilateralCohortMarket W.Agent W.Means)
    (buyer seller : W.Agent) (t : W.Moment) (h : W.History) where
  buyerCeiling : ℕ
  sellerFloor : ℕ
  buyerCeiling_eq_value : buyerCeiling = M.v_b buyer
  sellerFloor_eq_value : sellerFloor = M.v_s seller
  buyerPrefersAtOrBelow : ∀ p, p ≤ buyerCeiling →
    Preference buyer t h
      (End_of buyer (W.Accept buyer seller 1 M.m_good p M.m_money) t h)
      (End_of buyer α₀ t h)
  buyerDeterrenceAbove : ∀ p, buyerCeiling < p →
    ¬ Preference buyer t h
      (End_of buyer (W.Accept buyer seller 1 M.m_good p M.m_money) t h)
      (End_of buyer α₀ t h)
  sellerPrefersAtOrAbove : ∀ p, sellerFloor ≤ p →
    Preference seller t h
      (End_of seller (W.Offer seller buyer 1 M.m_good p M.m_money) t h)
      (End_of seller α₀ t h)
  sellerDeterrenceBelow : ∀ p, p < sellerFloor →
    ¬ Preference seller t h
      (End_of seller (W.Offer seller buyer 1 M.m_good p M.m_money) t h)
      (End_of seller α₀ t h)

/-- The buyer's numerically funded bid is capped by both the preference-based
reservation amount and cash observed in the ActionFrame. -/
def PurposefulReservationPair.fundedBid
    {M : MultilateralCohortMarket W.Agent W.Means}
    {buyer seller : W.Agent} {t : W.Moment} {h : W.History}
    (R : PurposefulReservationPair M buyer seller t h) (snapshotCash : ℕ) : ℕ :=
  min R.buyerCeiling snapshotCash

theorem PurposefulReservationPair.fundedBid_le_ceiling
    {M : MultilateralCohortMarket W.Agent W.Means}
    {buyer seller : W.Agent} {t : W.Moment} {h : W.History}
    (R : PurposefulReservationPair M buyer seller t h) (snapshotCash : ℕ) :
    R.fundedBid snapshotCash ≤ R.buyerCeiling :=
  Nat.min_le_left _ _

theorem PurposefulReservationPair.fundedBid_le_cash
    {M : MultilateralCohortMarket W.Agent W.Means}
    {buyer seller : W.Agent} {t : W.Moment} {h : W.History}
    (R : PurposefulReservationPair M buyer seller t h) (snapshotCash : ℕ) :
    R.fundedBid snapshotCash ≤ snapshotCash :=
  Nat.min_le_right _ _

/-- A finite clearing result must fit inside the seller's preference-based
reservation and the buyer's funded bid. The source of both reservation values
is the selected agents' preference brackets; cash is read from the pre-trade
ActionFrame endowment. -/
structure PurposefulFundedClearingRound
    (M : MultilateralCohortMarket W.Agent W.Means) where
  base : PurposefulMultilateralClearingRound M
  reservation : PurposefulReservationPair M base.clearing.buyer
    base.clearing.seller base.clearing.moment base.clearing.history
  snapshotCash : ℕ
  snapshotCash_eq : snapshotCash =
    W.omega base.clearing.buyer base.clearing.moment base.clearing.history M.m_money
  sellerFloor_le_price : reservation.sellerFloor ≤ base.clearing.price
  price_le_fundedBid : base.clearing.price ≤ reservation.fundedBid snapshotCash

/-- The clearing price lies above the seller's ordinal reservation and below
both the buyer's ordinal ceiling and observed spendable cash. -/
theorem PurposefulFundedClearingRound.price_bracket
    {M : MultilateralCohortMarket W.Agent W.Means}
    (S : PurposefulFundedClearingRound M) :
    S.reservation.sellerFloor ≤ S.base.clearing.price ∧
    S.base.clearing.price ≤ S.reservation.buyerCeiling ∧
    S.base.clearing.price ≤ S.snapshotCash := by
  exact ⟨S.sellerFloor_le_price,
    le_trans S.price_le_fundedBid (S.reservation.fundedBid_le_ceiling S.snapshotCash),
    le_trans S.price_le_fundedBid (S.reservation.fundedBid_le_cash S.snapshotCash)⟩

/-- Two purposeful clearing rounds in the same catallactic market have the
same price when they concern the same buyer and seller and that pair has a
single mutually acceptable price. The equality follows from each round's
ActionFrame-grounded reservation bracket. -/
theorem PurposefulFundedClearingRound.same_price_of_singleton_reservation
    {M : MultilateralCohortMarket W.Agent W.Means}
    (saving credit : PurposefulFundedClearingRound M)
    (h_buyer : saving.base.clearing.buyer = credit.base.clearing.buyer)
    (h_seller : saving.base.clearing.seller = credit.base.clearing.seller)
    (h_singleton : saving.reservation.sellerFloor =
      saving.reservation.buyerCeiling) :
    saving.base.clearing.price = credit.base.clearing.price := by
  have h_floor : saving.reservation.sellerFloor = credit.reservation.sellerFloor := by
    rw [saving.reservation.sellerFloor_eq_value,
      credit.reservation.sellerFloor_eq_value, h_seller]
  have h_ceiling : saving.reservation.buyerCeiling = credit.reservation.buyerCeiling := by
    rw [saving.reservation.buyerCeiling_eq_value,
      credit.reservation.buyerCeiling_eq_value, h_buyer]
  have h_credit_singleton : credit.reservation.sellerFloor =
      credit.reservation.buyerCeiling := by
    calc
      credit.reservation.sellerFloor = saving.reservation.sellerFloor := h_floor.symm
      _ = saving.reservation.buyerCeiling := h_singleton
      _ = credit.reservation.buyerCeiling := h_ceiling
  have h_saving_bracket := saving.price_bracket
  have h_credit_bracket := credit.price_bracket
  omega

/-- At the realized price, both participants' reservation comparisons follow
from their preference-based bounds, and their matched exchange remains an
active purposeful act by the underlying ActionFrame certificate. -/
theorem PurposefulFundedClearingRound.realized_price_grounded
    {M : MultilateralCohortMarket W.Agent W.Means}
    (S : PurposefulFundedClearingRound M) :
    Preference S.base.clearing.buyer S.base.clearing.moment S.base.clearing.history
      (End_of S.base.clearing.buyer
        (W.Accept S.base.clearing.buyer S.base.clearing.seller 1 M.m_good
          S.base.clearing.price M.m_money)
        S.base.clearing.moment S.base.clearing.history)
      (End_of S.base.clearing.buyer α₀ S.base.clearing.moment S.base.clearing.history) ∧
    Preference S.base.clearing.seller S.base.clearing.moment S.base.clearing.history
      (End_of S.base.clearing.seller
        (W.Offer S.base.clearing.seller S.base.clearing.buyer 1 M.m_good
          S.base.clearing.price M.m_money)
        S.base.clearing.moment S.base.clearing.history)
      (End_of S.base.clearing.seller α₀ S.base.clearing.moment S.base.clearing.history) ∧
    (ActivePurposefulAct S.base.clearing.buyer S.base.clearing.moment
      S.base.clearing.history
      (W.Accept S.base.clearing.buyer S.base.clearing.seller 1 M.m_good
        S.base.clearing.price M.m_money) ∧
     ActivePurposefulAct S.base.clearing.seller S.base.clearing.moment
      S.base.clearing.history
      (W.Offer S.base.clearing.seller S.base.clearing.buyer 1 M.m_good
        S.base.clearing.price M.m_money)) := by
  have hprice := S.price_bracket
  have hactive := S.base.matched_parties_active
  exact ⟨S.reservation.buyerPrefersAtOrBelow _ hprice.2.1,
    S.reservation.sellerPrefersAtOrAbove _ hprice.1,
    ⟨hactive.2, hactive.1⟩⟩

end ActionFrameMultilateralMarket


-- Section 4b.1: Ordered Pairs and Transfer Conservation


structure OCGroundedCohortMarket {M : Type*} (n : ℕ) where
  m_good : M
  m_money : M
  h_distinct : m_good ≠ m_money
  v_b : Fin n → ℕ
  v_s : Fin n → ℕ
  buyer_perm : Equiv.Perm (Fin n)
  seller_perm : Equiv.Perm (Fin n)
  v_b_sorted_antitone : Antitone (fun r => v_b (buyer_perm r))
  v_s_sorted_monotone : Monotone (fun r => v_s (seller_perm r))


theorem sorted_cohort_marginal_pairs_equilibrium
    {M : Type*} {n : ℕ} (Mkt : OCGroundedCohortMarket (M := M) n) (r_star : Fin n) (P : ℕ)
    (h_clearing : Mkt.v_s (Mkt.seller_perm r_star) ≤ P ∧ P ≤ Mkt.v_b (Mkt.buyer_perm r_star)) :
    (∀ r : Fin n,
      r ≤ r_star → P ≤ Mkt.v_b (Mkt.buyer_perm r) ∧ Mkt.v_s (Mkt.seller_perm r) ≤ P) := by
  intro r hr
  have hb_anti := Mkt.v_b_sorted_antitone hr
  have hs_mono := Mkt.v_s_sorted_monotone hr
  exact ⟨le_trans h_clearing.2 hb_anti, le_trans hs_mono h_clearing.1⟩


abbrev InventoryLedger (V M : Type*) := V → M → ℕ

/-- One solvent transfer carries exact remainders for the seller's good and
the buyer's money. The post-transfer ledger therefore never uses truncated
subtraction. -/
structure SolventPairTransfer {V M : Type*} [DecidableEq V]
    [DecidableEq M] (P : ℕ) (m_good m_money : M)
    (ω : InventoryLedger V M) where
  buyer : V
  seller : V
  buyer_ne_seller : buyer ≠ seller
  goodsDistinct : m_good ≠ m_money
  buyer_money : NatRemainder (ω buyer m_money) P
  seller_good : NatRemainder (ω seller m_good) 1

/-- The ledger after one certified transfer. -/
def SolventPairTransfer.after {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M} (T : SolventPairTransfer P m_good m_money ω) :
    InventoryLedger V M := fun a m =>
      if a = T.buyer then
        if m = m_good then ω a m + 1
        else if m = m_money then T.buyer_money.remaining else ω a m
      else if a = T.seller then
        if m = m_good then T.seller_good.remaining
        else if m = m_money then ω a m + P else ω a m
      else ω a m

/-- A complete list of transfers indexes every step by its exact input and
output ledgers. -/
inductive TransferRun {V M : Type*} [DecidableEq V] [DecidableEq M]
    (P : ℕ) (m_good m_money : M) :
    List (V × V) → InventoryLedger V M → InventoryLedger V M → Prop
  | nil (ω : InventoryLedger V M) : TransferRun P m_good m_money [] ω ω
  | cons {rest : List (V × V)} {ω ω' : InventoryLedger V M}
      (step : SolventPairTransfer P m_good m_money ω)
      (tail : TransferRun P m_good m_money rest step.after ω') :
      TransferRun P m_good m_money ((step.buyer, step.seller) :: rest) ω ω'

namespace SolventPairTransfer

/-- Exact buyer and seller remainders are uniquely determined by their
pre-transfer holdings and the certified quantities. -/
theorem buyer_money_remainder_unique {V M : Type*}
    [DecidableEq V] [DecidableEq M]
    {P : ℕ} {m_good m_money : M} {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω)
    (r : NatRemainder (ω T.buyer m_money) P) :
    T.buyer_money.remaining = r.remaining :=
  NatRemainder.remaining_unique T.buyer_money r

theorem seller_good_remainder_unique {V M : Type*}
    [DecidableEq V] [DecidableEq M]
    {P : ℕ} {m_good m_money : M} {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω)
    (r : NatRemainder (ω T.seller m_good) 1) :
    T.seller_good.remaining = r.remaining :=
  NatRemainder.remaining_unique T.seller_good r

/-- Directional holdings are determined by the exact transfer certificate. -/
theorem buyer_receives_good {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω) :
    T.after T.buyer m_good = ω T.buyer m_good + 1 := by
  simp [SolventPairTransfer.after]

theorem seller_delivers_good {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω) :
    T.after T.seller m_good + 1 = ω T.seller m_good := by
  have hne := T.buyer_ne_seller.symm
  simp [SolventPairTransfer.after, hne]
  have hbalance := T.seller_good.balance
  omega

theorem buyer_pays_money {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω) :
    T.after T.buyer m_money + P = ω T.buyer m_money := by
  have hbalance := T.buyer_money.balance
  simp [SolventPairTransfer.after, T.goodsDistinct.symm]
  omega

theorem seller_receives_money {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M}
    (T : SolventPairTransfer P m_good m_money ω) :
    T.after T.seller m_money = ω T.seller m_money + P := by
  simp [SolventPairTransfer.after, T.buyer_ne_seller.symm, T.goodsDistinct.symm]

/-- A certified pair transfer conserves each good and money total over any
cohort containing both parties. -/
theorem conserves {V M : Type*} [DecidableEq V] [DecidableEq M]
    {P : ℕ} {m_good m_money : M}
    {ω : InventoryLedger V M} (T : SolventPairTransfer P m_good m_money ω)
    (Cohort : Finset V) (hb : T.buyer ∈ Cohort) (hs : T.seller ∈ Cohort)
    (m : M) :
    ∑ a ∈ Cohort, T.after a m = ∑ a ∈ Cohort, ω a m := by
  have h_s_erase : T.seller ∈ Cohort.erase T.buyer := by
    rw [Finset.mem_erase]
    exact ⟨T.buyer_ne_seller.symm, hs⟩
  rw [← Finset.add_sum_erase Cohort (fun a => T.after a m) hb]
  rw [← Finset.add_sum_erase Cohort (fun a => ω a m) hb]
  rw [← Finset.add_sum_erase (Cohort.erase T.buyer) (fun a => T.after a m) h_s_erase]
  rw [← Finset.add_sum_erase (Cohort.erase T.buyer) (fun a => ω a m) h_s_erase]
  have h_other :
      ∑ a ∈ (Cohort.erase T.buyer).erase T.seller, T.after a m =
      ∑ a ∈ (Cohort.erase T.buyer).erase T.seller, ω a m := by
    apply Finset.sum_congr rfl
    intro a ha
    have hneB : a ≠ T.buyer := (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha)).1
    have hneS : a ≠ T.seller := (Finset.mem_erase.mp ha).1
    simp [SolventPairTransfer.after, hneB, hneS]
  have h_pair : T.after T.buyer m + T.after T.seller m =
      ω T.buyer m + ω T.seller m := by
    have hne := T.buyer_ne_seller.symm
    by_cases hg : m = m_good
    · subst m
      simp [SolventPairTransfer.after, hne]
      have hbal := T.seller_good.balance
      omega
    · by_cases hm : m = m_money
      · subst m
        simp [SolventPairTransfer.after, hne, hg]
        have hbal := T.buyer_money.balance
        omega
      · simp [SolventPairTransfer.after, hne, hg, hm]
  omega

end SolventPairTransfer

/-- An indexed run preserves cohort totals when each executed party belongs to
the cohort. -/
theorem transfer_run_conserves {V M : Type*} [DecidableEq V]
    [DecidableEq M] {P : ℕ} {m_good m_money : M}
    {pairs : List (V × V)}
    {ω ω' : InventoryLedger V M}
    (run : TransferRun P m_good m_money pairs ω ω')
    (Cohort : Finset V)
    (h_in_cohort : ∀ p ∈ pairs, p.1 ∈ Cohort ∧ p.2 ∈ Cohort) (m : M) :
    ∑ a ∈ Cohort, ω' a m = ∑ a ∈ Cohort, ω a m := by
  induction run with
  | nil _ => rfl
  | @cons rest before after step tail ih =>
    have hhead := h_in_cohort (step.buyer, step.seller) (by simp)
    have hrest : ∀ p ∈ rest, p.1 ∈ Cohort ∧ p.2 ∈ Cohort := by
      intro p hp
      exact h_in_cohort p (by simp [hp])
    calc
      ∑ a ∈ Cohort, after a m = ∑ a ∈ Cohort, step.after a m := ih hrest
      _ = ∑ a ∈ Cohort, before a m :=
        step.conserves Cohort hhead.1 hhead.2 m

namespace TransferRegression

abbrev Agent := Fin 2
abbrev Means := Fin 2

def good : Means := 0
def money : Means := 1

def exactBudgetLedger : InventoryLedger Agent Means := fun a m =>
  if a = 0 then if m = 1 then 7 else 0
  else if a = 1 then if m = 0 then 1 else 0
  else 0

def exactBudgetTransfer : SolventPairTransfer 7 good money exactBudgetLedger where
  buyer := 0
  seller := 1
  buyer_ne_seller := by decide
  goodsDistinct := by decide
  buyer_money := ⟨0, by decide⟩
  seller_good := ⟨0, by decide⟩

/-- Paying the exact budget leaves zero cash; the certificate records an
additive balance rather than relying on truncated subtraction. -/
theorem exact_budget_is_fully_spent : exactBudgetTransfer.after 0 money = 0 := by
  simp [SolventPairTransfer.after, exactBudgetTransfer, exactBudgetLedger,
    money, good]

def zeroPriceLedger : InventoryLedger Agent Means := fun a m =>
  if a = 1 ∧ m = 0 then 1 else 0

def zeroPriceTransfer : SolventPairTransfer 0 good money zeroPriceLedger where
  buyer := 0
  seller := 1
  buyer_ne_seller := by decide
  goodsDistinct := by decide
  buyer_money := ⟨0, by decide⟩
  seller_good := ⟨0, by decide⟩

/-- A zero-price exchange is valid with a zero cash balance and still uses the
seller's exact one-unit good balance. -/
theorem zero_price_buyer_cash_is_unchanged : zeroPriceTransfer.after 0 money = 0 := by
  simp [SolventPairTransfer.after, zeroPriceTransfer, zeroPriceLedger,
    money, good]

theorem zero_price_seller_delivers_good : zeroPriceTransfer.after 1 good = 0 := by
  simp [SolventPairTransfer.after, zeroPriceTransfer, zeroPriceLedger,
    money, good]

/-- There is no exact natural-number remainder when the requested payment
exceeds available cash. -/
theorem insufficient_funds_have_no_remainder : ¬ Nonempty (NatRemainder 3 4) := by
  rintro ⟨r⟩
  have h := r.balance
  omega

/-- A seller without the required unit of goods cannot carry a solvent
delivery certificate. -/
theorem insufficient_seller_goods_have_no_remainder :
    ¬ Nonempty (NatRemainder 0 1) := by
  rintro ⟨r⟩
  have h := r.balance
  omega

theorem exact_budget_transfer_directional_holdings :
    exactBudgetTransfer.after 0 good = 1 ∧
    exactBudgetTransfer.after 1 good = 0 ∧
    exactBudgetTransfer.after 1 money = 7 ∧
    exactBudgetTransfer.after 0 money = 0 := by
  norm_num [SolventPairTransfer.after, exactBudgetTransfer,
    exactBudgetLedger, good, money]
  exact ⟨rfl, rfl⟩

def repeatedLedger : InventoryLedger Agent Means := fun a m =>
  if a = 0 then if m = 1 then 2 else 0
  else if a = 1 then if m = 0 then 2 else 0
  else 0

def repeatedFirst : SolventPairTransfer 1 good money repeatedLedger where
  buyer := 0
  seller := 1
  buyer_ne_seller := by decide
  goodsDistinct := by decide
  buyer_money := ⟨1, by decide⟩
  seller_good := ⟨1, by decide⟩

def repeatedSecond : SolventPairTransfer 1 good money repeatedFirst.after where
  buyer := 0
  seller := 1
  buyer_ne_seller := by decide
  goodsDistinct := by decide
  buyer_money := ⟨0, by
    change 1 + 0 = 1
    rfl⟩
  seller_good := ⟨0, by
    change 1 + 0 = 1
    rfl⟩

/-- The same buyer-seller pair can occur twice when each successive ledger
certifies the next payment and delivery. -/
theorem repeatedPairRun : TransferRun 1 good money [(0, 1), (0, 1)]
    repeatedLedger repeatedSecond.after :=
  .cons repeatedFirst (.cons repeatedSecond (.nil _))

theorem repeated_pair_run_exists : Nonempty
    (TransferRun 1 good money [(0, 1), (0, 1)] repeatedLedger repeatedSecond.after) :=
  ⟨repeatedPairRun⟩

theorem repeated_pair_exhausts_buyer_cash : repeatedSecond.after 0 money = 0 := by
  simp [SolventPairTransfer.after, repeatedSecond, repeatedFirst, repeatedLedger,
    money, good]

theorem repeated_pair_exhausts_seller_goods : repeatedSecond.after 1 good = 0 := by
  simp [SolventPairTransfer.after, repeatedSecond, repeatedFirst, repeatedLedger,
    money, good]

end TransferRegression

/-- The multilateral conservation interface consumes an indexed run, so every
step carries the exact balance needed to execute it. -/
theorem simultaneous_multilateral_trade_conservation
    {V M : Type*} [DecidableEq V] [DecidableEq M]
    {P : ℕ} {m_good m_money : M} {pairs : List (V × V)}
    {ω ω' : InventoryLedger V M}
    (run : TransferRun P m_good m_money pairs ω ω')
    (Cohort : Finset V)
    (h_in_cohort : ∀ p ∈ pairs, p.1 ∈ Cohort ∧ p.2 ∈ Cohort) (m : M) :
    ∑ a ∈ Cohort, ω' a m = ∑ a ∈ Cohort, ω a m :=
  transfer_run_conserves run Cohort h_in_cohort m

/-- A multilateral market stores the certified execution together with the
exact post-transfer ledger. -/
structure MultilateralMarketBook (V M : Type*) [DecidableEq V]
    [DecidableEq M] where
  Traders : Finset V
  Buyers : Finset V
  Sellers : Finset V
  h_buyers_sub : Buyers ⊆ Traders
  h_sellers_sub : Sellers ⊆ Traders
  h_disjoint : Disjoint Buyers Sellers
  m_good : M
  m_money : M
  h_distinct_means : m_good ≠ m_money
  ω : InventoryLedger V M
  P : ℕ
  pairs : List (V × V)
  after : InventoryLedger V M
  transferRun : TransferRun P m_good m_money pairs ω after
  h_participants : ∀ p ∈ pairs, p.1 ∈ Traders ∧ p.2 ∈ Traders

/-- The market book's recorded output is solvent and conserves total inventory
for every means. Individual post-trade holdings are the exact ledger in the
book, not a truncated arithmetic expression. -/
theorem multilateral_market_book_trade_conserved_and_solvent
    {V M : Type*} [DecidableEq V] [DecidableEq M]
    (B : MultilateralMarketBook V M) (m : M) :
    (∀ a, 0 ≤ B.after a m) ∧
      ∑ a ∈ B.Traders, B.after a m = ∑ a ∈ B.Traders, B.ω a m := by
  constructor
  · intro _
    exact Nat.zero_le _
  · exact transfer_run_conserves B.transferRun B.Traders
      B.h_participants m


-- Section 4c: Cash Balances and Price Changes


section EpistemicCashReservation

variable [W : ActionFrame]


def CashBalanceReservationDemand
    (PlausibleBranches : Finset W.History) (expenditure : W.History → ℕ) (M_held : ℕ) : Prop :=
  ∀ h ∈ PlausibleBranches, expenditure h ≤ M_held


/-- Epistemic Cash Balance Solvency Guarantee:
Holding a cash balance `M_held` sufficient to cover contemplated reservation expenditures
guarantees financial solvency across all plausible branches: every expenditure is within
endowments, and planned actions satisfy `A_feas` via `ActionFrame.A_feas_coupling`. -/
theorem cash_balance_solvency_guarantee
    (i : W.Agent) (t : W.Moment) (m_money : W.Means)
    (PlausibleBranches : Finset W.History) (expenditure : W.History → ℕ) (M_held : ℕ)
    (α : W.History → W.Action)
    (h_res : CashBalanceReservationDemand PlausibleBranches expenditure M_held)
    (h_held : ∀ h ∈ PlausibleBranches, M_held ≤ W.omega i t h m_money)
    (h_exp : ∀ h ∈ PlausibleBranches, W.use_means (α h) m_money ≤ expenditure h)
    (h_cont : ∀ h ∈ PlausibleBranches, α h ∈ W.A_cont i t h)
    (h_other : ∀ h ∈ PlausibleBranches, ∀ m, m ≠ m_money →
      W.use_means (α h) m ≤ W.omega i t h m) :
    (∀ h ∈ PlausibleBranches, expenditure h ≤ W.omega i t h m_money) ∧
    (∀ h ∈ PlausibleBranches, α h ∈ W.A_feas i t h) := by
  have h_cov : ∀ h ∈ PlausibleBranches, expenditure h ≤ W.omega i t h m_money := by
    intro h hh
    exact le_trans (h_res h hh) (h_held h hh)
  refine ⟨h_cov, ?_⟩
  intro h hh
  rw [W.A_feas_coupling]
  refine ⟨h_cont h hh, ?_⟩
  intro m
  by_cases hm : m = m_money
  · subst m
    exact le_trans (h_exp h hh) (h_cov h hh)
  · exact h_other h hh m hm

end EpistemicCashReservation


def CanAffordQuantity (quantity price cash : ℕ) : Prop :=
  quantity * price ≤ cash

structure CantillonNetwork [W : ActionFrame] where
  downstream : W.Agent
  t_pre : W.Moment
  t_post : W.Moment
  h : W.History
  m_money : W.Means
  P_pre : ℕ
  P_post : ℕ
  h_pos_pre : 0 < P_pre
  h_inflation : P_pre < P_post
  h_downstream_cash_unchanged : W.omega downstream t_post h m_money =
    W.omega downstream t_pre h m_money
  h_solvency_pre : P_pre ≤ W.omega downstream t_pre h m_money
  h_exclusion_post : W.omega downstream t_post h m_money < P_post

def CantillonNetwork.M_downstream [W : ActionFrame] (net : CantillonNetwork) : ℕ :=
  W.omega net.downstream net.t_pre net.h net.m_money

structure CantillonPurchasingPowerConclusion [W : ActionFrame] (net : CantillonNetwork) : Prop where
  oneUnitAffordableBefore : CanAffordQuantity 1 net.P_pre net.M_downstream
  noPositiveQuantityAffordableAfter : ∀ quantity, 0 < quantity →
    ¬ CanAffordQuantity quantity net.P_post net.M_downstream
  crossProductDecline : net.M_downstream * net.P_pre <
    net.M_downstream * net.P_post

theorem CantillonNetwork.one_unit_affordable_before [W : ActionFrame] (net : CantillonNetwork) :
    CanAffordQuantity 1 net.P_pre net.M_downstream := by
  simpa [CanAffordQuantity, CantillonNetwork.M_downstream] using net.h_solvency_pre

theorem CantillonNetwork.no_positive_quantity_affordable_after [W : ActionFrame]
    (net : CantillonNetwork) (quantity : ℕ) (hquantity : 0 < quantity) :
    ¬ CanAffordQuantity quantity net.P_post net.M_downstream := by
  intro h_affordable
  have hquantity_one : 1 ≤ quantity := Nat.succ_le_of_lt hquantity
  have hprice_le : net.P_post ≤ quantity * net.P_post := by
    simpa using Nat.mul_le_mul_right net.P_post hquantity_one
  have hprice_le_cash : net.P_post ≤ net.M_downstream :=
    le_trans hprice_le h_affordable
  have h_excl := net.h_exclusion_post
  rw [net.h_downstream_cash_unchanged] at h_excl
  exact (Nat.not_le_of_gt h_excl) hprice_le_cash


theorem cantillon_network_purchasing_power_dilution [W : ActionFrame]
    (net : CantillonNetwork) : CantillonPurchasingPowerConclusion net := by
  have h_money_pos : 0 < net.M_downstream :=
    lt_of_lt_of_le net.h_pos_pre net.h_solvency_pre
  exact ⟨net.one_unit_affordable_before,
    net.no_positive_quantity_affordable_after,
    Nat.mul_lt_mul_of_pos_left net.h_inflation h_money_pos⟩


-- Section 4c.1: Price Uncertainty and Cash Demand


/-- Lower and upper price bounds for each factor. -/
structure FactorPriceBox (d : ℕ) where
  P_inf : Fin d → ℕ
  P_sup : Fin d → ℕ
  h_le : ∀ k, P_inf k ≤ P_sup k

/-- Sum of upper prices times quantities. -/
def PrecautionaryCashDemand {d : ℕ} (B : FactorPriceBox d) (x : Fin d → ℕ) : ℕ :=
  ∑ k : Fin d, B.P_sup k * x k

/-- A factor completion action is infeasible when its upper-box cash demand
exceeds the actor's money endowment. This is the direct bridge from
catallactic price uncertainty to ActionFrame resource feasibility. -/
theorem factor_completion_infeasible_of_price_box_squeeze
    [W : ActionFrame] {d : ℕ}
    (B : FactorPriceBox d) (factorQuantities : Fin d → ℕ)
    (i : Agent) (t : Moment) (h : History)
    (completion : Action) (money : Means)
    (h_cost : W.use_means completion money =
      PrecautionaryCashDemand B factorQuantities)
    (h_cash_shortfall : W.omega i t h money <
      PrecautionaryCashDemand B factorQuantities) :
    completion ∉ W.A_feas i t h := by
  apply infeasible_of_insufficient_endowment i t h completion money
  change W.omega i t h money < W.use_means completion money
  rw [h_cost]
  exact h_cash_shortfall

/-- `B2` has lower lower-bounds and higher upper-bounds than `B1`. -/
def PriceBoxWidening {d : ℕ} (B1 B2 : FactorPriceBox d) : Prop :=
  (∀ k, B2.P_inf k ≤ B1.P_inf k) ∧ (∀ k, B1.P_sup k ≤ B2.P_sup k)

/-- Widening the box weakly increases cash demand. -/
theorem box_widening_increases_precautionary_cash_demand {d : ℕ}
    (B1 B2 : FactorPriceBox d) (x : Fin d → ℕ)
    (h_widen : PriceBoxWidening B1 B2) :
    PrecautionaryCashDemand B1 x ≤ PrecautionaryCashDemand B2 x := by
  dsimp [PrecautionaryCashDemand]
  apply Finset.sum_le_sum
  intro k _
  exact Nat.mul_le_mul_right (x k) (h_widen.2 k)

/-- A higher upper price for a used factor strictly increases cash demand. -/
theorem box_widening_strictly_increases_precautionary_cash_demand {d : ℕ}
    (B1 B2 : FactorPriceBox d) (x : Fin d → ℕ)
    (h_widen : PriceBoxWidening B1 B2)
    (k_star : Fin d) (h_pos : 0 < x k_star) (h_strict : B1.P_sup k_star < B2.P_sup k_star) :
    PrecautionaryCashDemand B1 x < PrecautionaryCashDemand B2 x := by
  dsimp [PrecautionaryCashDemand]
  apply Finset.sum_lt_sum
  · intro k _
    exact Nat.mul_le_mul_right (x k) (h_widen.2 k)
  · exact ⟨k_star, Finset.mem_univ k_star, by nlinarith⟩

/-- Agents whose money endowment covers their cash demand. -/
def CashBackedAcceptanceProfile {V M : Type*} [DecidableEq V] {d : ℕ}
    (ω : V → M → ℕ) (m_money : M)
    (B : FactorPriceBox d) (x : V → Fin d → ℕ) (Cohort : Finset V) : Finset V :=
  Cohort.filter (fun i => PrecautionaryCashDemand B (x i) ≤ ω i m_money)

/-- Widening the box shrinks the set of agents whose demand is covered. -/
theorem box_widening_contracts_solvent_profile {V M : Type*} [DecidableEq V] {d : ℕ}
    (ω : V → M → ℕ) (m_money : M)
    (B1 B2 : FactorPriceBox d) (x : V → Fin d → ℕ) (Cohort : Finset V)
    (h_widen : PriceBoxWidening B1 B2) :
    CashBackedAcceptanceProfile ω m_money B2 x Cohort ⊆
      CashBackedAcceptanceProfile ω m_money B1 x Cohort := by
  intro i hi
  simp only [CashBackedAcceptanceProfile, Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  have h_mono := box_widening_increases_precautionary_cash_demand B1 B2 (x i) h_widen
  exact le_trans h_mono hi.2


structure NetworkPriceBoxSchedule {V M : Type*} (d : ℕ) where
  boxOf : (M → Finset V) → FactorPriceBox d
  box_monotone : ∀ Γ₁ Γ₂, Γ₁ ≤ Γ₂ → PriceBoxWidening (boxOf Γ₂) (boxOf Γ₁)


theorem network_money_emergence_narrows_price_box_and_expands_solvency
    [W : ActionFrame] [Finite W.Means]
    (G : TradingNetwork W.Agent) (Supplies : W.Agent → W.Means) (Demands : W.Agent → W.Means → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (seed : W.Agent) (m_star : W.Means) (Γ₀ : W.Means → Finset W.Agent)
    (h_seed : seed ∈ Γ₀ m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed)
    {d : ℕ} (sched : NetworkPriceBoxSchedule (V := W.Agent) (M := W.Means) d)
    (ω : W.Agent → W.Means → ℕ) (x : W.Agent → Fin d → ℕ) (Cohort : Finset W.Agent) :
    ∃ (Γ_star : W.Means → Finset W.Agent) (n : ℕ),
      Γ_star = (PhiTradingNet G Supplies Demands)^[n] Γ₀ ∧
      IsNetworkUniversalMoney Γ_star m_star ∧
      PriceBoxWidening (sched.boxOf Γ_star) (sched.boxOf Γ₀) ∧
      (∀ i : W.Agent, PrecautionaryCashDemand (sched.boxOf Γ_star) (x i) ≤
                    PrecautionaryCashDemand (sched.boxOf Γ₀) (x i)) ∧
      CashBackedAcceptanceProfile ω m_star (sched.boxOf Γ₀) x Cohort ⊆
      CashBackedAcceptanceProfile ω m_star (sched.boxOf Γ_star) x Cohort := by
  obtain ⟨Γ_star, n, hn_eq, _, h_univ⟩ :=
    network_universal_money_emergence (W := W) G Supplies Demands seed m_star Γ₀ h_seed h_conn
  have h_le : Γ₀ ≤ Γ_star := by
    rw [hn_eq]
    exact le_iterate_phi_trading_net G Supplies Demands Γ₀ n
  have h_widen : PriceBoxWidening (sched.boxOf Γ_star) (sched.boxOf Γ₀) :=
    sched.box_monotone Γ₀ Γ_star h_le
  have h_cash : ∀ i : W.Agent,
      PrecautionaryCashDemand (sched.boxOf Γ_star) (x i) ≤
      PrecautionaryCashDemand (sched.boxOf Γ₀) (x i) :=
    fun i => box_widening_increases_precautionary_cash_demand
      (sched.boxOf Γ_star) (sched.boxOf Γ₀) (x i) h_widen
  have h_solv := box_widening_contracts_solvent_profile
    ω m_star (sched.boxOf Γ_star) (sched.boxOf Γ₀) x Cohort h_widen
  exact ⟨Γ_star, n, hn_eq, h_univ, h_widen, h_cash, h_solv⟩


theorem network_money_emergence_strictly_reduces_cash_demand
    [W : ActionFrame] [Finite W.Means]
    (G : TradingNetwork W.Agent) (Supplies : W.Agent → W.Means) (Demands : W.Agent → W.Means → Prop)
    [∀ Γ i m, Decidable (NetworkFeasIndirect G Supplies Demands Γ i m)]
    (seed : W.Agent) (m_star : W.Means) (Γ₀ : W.Means → Finset W.Agent)
    (h_seed : seed ∈ Γ₀ m_star)
    (h_conn : NetworkWantsConnected G Supplies Demands seed)
    {d : ℕ} (sched : NetworkPriceBoxSchedule (V := W.Agent) (M := W.Means) d)
    (k_star : Fin d) (x : Fin d → ℕ) (h_pos : 0 < x k_star)
    (h_strict_narrow : ∀ Γ, IsNetworkUniversalMoney Γ m_star →
      (sched.boxOf Γ).P_sup k_star < (sched.boxOf Γ₀).P_sup k_star) :
    ∃ (Γ_star : W.Means → Finset W.Agent) (n : ℕ),
      Γ_star = (PhiTradingNet G Supplies Demands)^[n] Γ₀ ∧
      IsNetworkUniversalMoney Γ_star m_star ∧
      PrecautionaryCashDemand (sched.boxOf Γ_star) x <
        PrecautionaryCashDemand (sched.boxOf Γ₀) x := by
  obtain ⟨Γ_star, n, hn_eq, _, h_univ⟩ :=
    network_universal_money_emergence (W := W) G Supplies Demands seed m_star Γ₀ h_seed h_conn
  have h_le : Γ₀ ≤ Γ_star := by
    rw [hn_eq]
    exact le_iterate_phi_trading_net G Supplies Demands Γ₀ n
  have h_widen : PriceBoxWidening (sched.boxOf Γ_star) (sched.boxOf Γ₀) :=
    sched.box_monotone Γ₀ Γ_star h_le
  have h_strict := h_strict_narrow Γ_star h_univ
  have h_cash_strict := box_widening_strictly_increases_precautionary_cash_demand
    (sched.boxOf Γ_star) (sched.boxOf Γ₀) x h_widen k_star h_pos h_strict
  exact ⟨Γ_star, n, hn_eq, h_univ, h_cash_strict⟩


structure CantillonNetworkDiffusion (V : Type) [DecidableEq V] where
  G : TradingNetwork V
  seed : V
  hop_dist : V → ℕ
  hop_seed : hop_dist seed = 0
  hop_step : ∀ i j, G.adjacent i j → hop_dist j ≤ hop_dist i + 1
  delta_M : ℕ
  h_pos_delta : 0 < delta_M


def CantillonNetworkDiffusion.effective_bid {V : Type} [DecidableEq V]
    (diff : CantillonNetworkDiffusion V) (v_b : V → ℕ) (d : ℕ) (i : V) : ℕ :=
  v_b i + if diff.hop_dist i ≤ d then diff.delta_M else 0

/-- Effective cash balance of agent `i` at diffusion stage `d`. -/
def CantillonNetworkDiffusion.effective_cash {V : Type} [DecidableEq V]
    (diff : CantillonNetworkDiffusion V) (omega_money : V → ℕ) (d : ℕ) (i : V) : ℕ :=
  omega_money i + if diff.hop_dist i ≤ d then diff.delta_M else 0


theorem cantillon_hop_shifts_clearing_price_and_crowds_out_downstream
    {V : Type} [DecidableEq V]
    (diff : CantillonNetworkDiffusion V) (v_b : V → ℕ)
    (d : ℕ) (P_pre P_wave : ℕ)
    (j : V) (h_downstream : d < diff.hop_dist j)
    (h_intra_pre : P_pre ≤ v_b j)
    (h_below_wave : v_b j < P_wave) :
    P_pre ≤ diff.effective_bid v_b 0 j ∧
    diff.effective_bid v_b d j < P_wave := by
  have h_not_le_d : ¬ (diff.hop_dist j ≤ d) := by omega
  have h_not_le_0 : ¬ (diff.hop_dist j ≤ 0) := by omega
  dsimp [CantillonNetworkDiffusion.effective_bid]
  split_ifs; omega


-- Section 4: Tendering at a Fixed Exchange Rate


section GreshamsLaw

variable [W : ActionFrame]


theorem mengerian_bundle_gresham_preference
    (i : Agent) (t : Moment) (h : History)
    (e_market e_good e_bad : Ends)
    (h_distinct : e_good ≠ e_bad)
    (h_good_mkt : e_good ≠ e_market)
    (h_bad_mkt : e_bad ≠ e_market)
    (h_comm_pref : Preference i t h e_good e_bad) :
    let b_tender_bad : Finset Ends := {e_market, e_good}
    let b_tender_good : Finset Ends := {e_market, e_bad}
    (b_tender_bad \ b_tender_good = {e_good}) ∧
    (b_tender_good \ b_tender_bad = {e_bad}) ∧
    (∀ e1 ∈ b_tender_bad \ b_tender_good,
     ∀ e2 ∈ b_tender_good \ b_tender_bad, Preference i t h e1 e2) := by
  intro b_tender_bad b_tender_good
  have h_diff_bad : b_tender_bad \ b_tender_good = {e_good} := by
    dsimp [b_tender_bad, b_tender_good]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h_not⟩
      · exfalso; exact h_not (Or.inl rfl)
      · exact rfl
    · rintro rfl
      refine ⟨Or.inr rfl, ?_⟩
      rintro (rfl | rfl)
      · exact h_good_mkt rfl
      · exact h_distinct rfl
  have h_diff_good : b_tender_good \ b_tender_bad = {e_bad} := by
    dsimp [b_tender_bad, b_tender_good]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h_not⟩
      · exfalso; exact h_not (Or.inl rfl)
      · exact rfl
    · rintro rfl
      refine ⟨Or.inr rfl, ?_⟩
      rintro (rfl | rfl)
      · exact h_bad_mkt rfl
      · exact h_distinct.symm rfl
  refine ⟨h_diff_bad, h_diff_good, ?_⟩
  rw [h_diff_bad, h_diff_good]
  intro e1 he1 e2 he2
  simp only [Finset.mem_singleton] at he1 he2
  subst he1 he2
  exact h_comm_pref


/-- The subset of transacting agents actively tendering medium m in spot exchanges. -/
def CirculatingTender
    (Agents : Finset Agent)
    (tender : Agent → Means) (m : Means) : Finset Agent :=
  Agents.filter (fun i => tender i = m)


theorem purposeful_greshams_law_collapse
    (m_good m_bad : Means)
    (e_tender_good e_tender_bad : Ends)
    (Agents : Finset Agent)
    (t : Moment) (h : History)
    (α_tender : Agent → Means → Action)
    (h_tender_pref : ∀ i ∈ Agents, Preference i t h e_tender_bad e_tender_good)
    (h_bad_feas : ∀ i ∈ Agents, α_tender i m_bad ∈ A_feas i t h)
    (h_end_bad : ∀ i ∈ Agents, End_of i (α_tender i m_bad) t h = e_tender_bad)
    (h_end_good : ∀ i ∈ Agents, End_of i (α_tender i m_good) t h = e_tender_good) :
    ∀ i ∈ Agents, ¬ PurposefulAct i t h (α_tender i m_good) := by
  intro i hi h_purp
  have h_feas_bad := h_bad_feas i hi
  have h_pref := h_tender_pref i hi
  rw [← h_end_bad i hi, ← h_end_good i hi] at h_pref
  have h_undom := h_purp.2.2.2 (α_tender i m_bad) h_feas_bad
  exact h_undom h_pref


theorem greshams_law_circulation_collapse
    (m_good m_bad : Means)
    (e_tender_good e_tender_bad : Ends)
    (Agents : Finset Agent)
    (t : Moment) (h : History)
    (tender : Agent → Means)
    (α_tender : Agent → Means → Action)
    (h_tender_pref : ∀ i ∈ Agents, Preference i t h e_tender_bad e_tender_good)
    (h_feasible_tender : ∀ i ∈ Agents, tender i = m_good ∨ tender i = m_bad)
    (h_purp_tender : ∀ i ∈ Agents, PurposefulAct i t h (α_tender i (tender i)))
    (h_bad_feas : ∀ i ∈ Agents, α_tender i m_bad ∈ A_feas i t h)
    (h_end_bad : ∀ i ∈ Agents, End_of i (α_tender i m_bad) t h = e_tender_bad)
    (h_end_good : ∀ i ∈ Agents, End_of i (α_tender i m_good) t h = e_tender_good) :
    CirculatingTender Agents tender m_good = ∅ ∧
    CirculatingTender Agents tender m_bad = Agents := by
  have h_rational_tender : ∀ i ∈ Agents, tender i ≠ m_good := by
    intro i hi h_tender_good
    have h_purp := h_purp_tender i hi
    rw [h_tender_good] at h_purp
    have h_not_purp := purposeful_greshams_law_collapse m_good m_bad e_tender_good e_tender_bad
      Agents t h α_tender h_tender_pref h_bad_feas h_end_bad h_end_good i hi
    exact h_not_purp h_purp
  dsimp [CirculatingTender]
  constructor
  · rw [Finset.filter_eq_empty_iff]
    intro i hi h_tender_good
    exact (h_rational_tender i hi) h_tender_good
  · ext i
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hi, _⟩; exact hi
    · intro hi
      refine ⟨hi, ?_⟩
      rcases h_feasible_tender i hi with h_good | h_bad
      · exact (h_rational_tender i hi h_good).elim
      · exact h_bad

end GreshamsLaw


-- Section 5: Physical Inputs and Prices


/-- Physical input vector across d distinct capital/input categories. -/
def InputVec (d : ℕ) := Fin d → ℕ

/-- `x` is no greater than `y` in every coordinate. -/
def PhysLE {d : ℕ} (x y : InputVec d) : Prop :=
  ∀ r : Fin d, x r ≤ y r

/-- Each vector exceeds the other in at least one coordinate. -/
def PhysicalAntichain {d : ℕ} (x y : InputVec d) : Prop :=
  (∃ a : Fin d, y a < x a) ∧ (∃ b : Fin d, x b < y b)

/-- The two vectors are incomparable under `PhysLE`. -/
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


def Cost (d : ℕ) (P : Fin d → ℕ) (x : InputVec d) : ℕ :=
  ∑ r : Fin d, P r * x r


theorem catallactic_cost_linearly_ordered (d : ℕ) (P : Fin d → ℕ) (x y : InputVec d) :
    Cost d P x ≤ Cost d P y ∨ Cost d P y ≤ Cost d P x :=
  le_total (Cost d P x) (Cost d P y)


def IsRankPreserving (φ : Fin 4 → ℕ) : Prop :=
  φ 0 > φ 1 ∧ φ 1 > φ 2 ∧ φ 2 > φ 3


theorem socialist_calculation_incommensurability :
    ∃ (φ1 φ2 : Fin 4 → ℕ),
      IsRankPreserving φ1 ∧ IsRankPreserving φ2 ∧
      (φ1 0 + φ1 3 > φ1 1 + φ1 2) ∧
      (φ2 0 + φ2 3 < φ2 1 + φ2 2) := by
  let φ1 : Fin 4 → ℕ := fun r =>
    match r with
    | ⟨0, _⟩ => 10
    | ⟨1, _⟩ => 4
    | ⟨2, _⟩ => 3
    | ⟨3, _⟩ => 1
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


theorem semantic_incommensurability_barrier :
    -- Rank-preserving functions can reverse the sum comparison.
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


-- Section 5b: Price Comparisons in ActionFrame


section ActionFrameSocialistCalculation

variable [W : ActionFrame]


structure ActionFrameSocialistEconomy (i : Agent) (t : Moment) (h : History) where
  mA : Means
  mB : Means
  h_diff_means : mA ≠ mB
  eA : Ends
  eB : Ends
  h_diff_ends : eA ≠ eB
  x_A : InputVec 2
  x_B : InputVec 2
  non_market_report : Fin 2 → ℕ
  bundle_A : Means → ℕ
  bundle_B : Means → ℕ
  h_end_A : eA = W.BundleEnd bundle_A
  h_end_B : eB = W.BundleEnd bundle_B
  /-- Which bundle is selected by the local appraisal. -/
  prefers_A : Bool
  /-- The selected bundle dominates the other under valued-end appraisal. -/
  end_dominance :
    if prefers_A then
      W.SubjectiveTeleologicalDominates i t h bundle_A bundle_B
    else
      W.SubjectiveTeleologicalDominates i t h bundle_B bundle_A

/-- Alternative A is preferred when `prefers_A` is true. -/
theorem ActionFrameSocialistEconomy.pref_A_over_B
    (E : ActionFrameSocialistEconomy i t h) (hA : E.prefers_A = true) :
    Preference i t h E.eA E.eB := by
  have hd : W.SubjectiveTeleologicalDominates i t h E.bundle_A E.bundle_B := by
    simpa [hA] using E.end_dominance
  have hp := W.teleological_bundle_dominance_induces_preference
    i t h E.bundle_A E.bundle_B hd
  rw [← E.h_end_A, ← E.h_end_B] at hp
  exact hp

/-- Alternative B is preferred when `prefers_A` is false. -/
theorem ActionFrameSocialistEconomy.pref_B_over_A
    (E : ActionFrameSocialistEconomy i t h) (hB : E.prefers_A = false) :
    Preference i t h E.eB E.eA := by
  have hd : W.SubjectiveTeleologicalDominates i t h E.bundle_B E.bundle_A := by
    simpa [hB] using E.end_dominance
  have hp := W.teleological_bundle_dominance_induces_preference
    i t h E.bundle_B E.bundle_A hd
  rw [← E.h_end_B, ← E.h_end_A] at hp
  exact hp


theorem action_frame_socialist_pref_asymm
    (i : Agent) (t : Moment) (h : History) (E : ActionFrameSocialistEconomy i t h) :
    (E.prefers_A = true → ¬ Preference i t h E.eB E.eA) ∧
    (E.prefers_A = false → ¬ Preference i t h E.eA E.eB) := by
  constructor
  · intro hA hp
    exact W.pref_asymm i t h (E.pref_A_over_B hA) hp
  · intro hB hp
    exact W.pref_asymm i t h (E.pref_B_over_A hB) hp


def ActionFramePreservedEnd (E : ActionFrameSocialistEconomy i t h) (x : InputVec 2) : Ends :=
  if x 0 ≤ x 1 then E.eA else E.eB


def ViolatesActionFrameMengerianEconomizing (E : ActionFrameSocialistEconomy i t h)
    (chosen : InputVec 2) : Prop :=
  ∃ alt, (alt = E.x_A ∨ alt = E.x_B) ∧
    Preference i t h (ActionFramePreservedEnd E alt) (ActionFramePreservedEnd E chosen)

/-- The recorded methods, inventories, and values in an `ActionFrame`. -/
def action_frame_non_market_observable
    (E : ActionFrameSocialistEconomy i t h) : InputVec 2 × InputVec 2 × (Fin 2 → ℕ) :=
  (E.x_A, E.x_B, E.non_market_report)


theorem action_frame_socialist_calculation_impossibility
    (i1 i2 : Agent) (t1 t2 : Moment) (h1 h2 : History)
    (E1 : ActionFrameSocialistEconomy i1 t1 h1)
    (E2 : ActionFrameSocialistEconomy i2 t2 h2)
    (h_same_methods : E1.x_A = E2.x_A ∧ E1.x_B = E2.x_B)
    (h_anti : PhysicalAntichain E1.x_A E1.x_B)
    (h_same_report : E1.non_market_report = E2.non_market_report)
    (h_same_ends : E1.eA = E2.eA ∧ E1.eB = E2.eB)
    (h_opposite_preferences : E1.prefers_A = true ∧ E2.prefers_A = false)
    (h_presA : ActionFramePreservedEnd E1 E1.x_A = E1.eB)
    (h_presB : ActionFramePreservedEnd E1 E1.x_B = E1.eA) :
    PhysicalAntichain E1.x_A E1.x_B ∧
    action_frame_non_market_observable E1 = action_frame_non_market_observable E2 ∧
    ViolatesActionFrameMengerianEconomizing E1 E1.x_A ∧
    ¬ ViolatesActionFrameMengerianEconomizing E1 E1.x_B ∧
    ViolatesActionFrameMengerianEconomizing E2 E2.x_B ∧
    ¬ ViolatesActionFrameMengerianEconomizing E2 E2.x_A ∧
    ∀ (planner_rule : (InputVec 2 × InputVec 2 × (Fin 2 → ℕ)) → Bool),
      (let chosen1 := if planner_rule (action_frame_non_market_observable E1)
        then E1.x_A else E1.x_B
       ViolatesActionFrameMengerianEconomizing E1 chosen1) ∨
      (let chosen2 := if planner_rule (action_frame_non_market_observable E2)
        then E2.x_A else E2.x_B
       ViolatesActionFrameMengerianEconomizing E2 chosen2) := by
  have h_obs : action_frame_non_market_observable E1 = action_frame_non_market_observable E2 := by
    dsimp [action_frame_non_market_observable]
    rw [h_same_methods.1, h_same_methods.2, h_same_report]
  have h_pres2A : ActionFramePreservedEnd E2 E2.x_A = E2.eB := by
    have h_eq : ActionFramePreservedEnd E2 E2.x_A =
      if E1.x_A 0 ≤ E1.x_A 1 then E2.eA else E2.eB := by
      dsimp [ActionFramePreservedEnd]
      rw [← h_same_methods.1]
    rw [h_eq, ← h_same_ends.1, ← h_same_ends.2]
    exact h_presA
  have h_pres2B : ActionFramePreservedEnd E2 E2.x_B = E2.eA := by
    have h_eq : ActionFramePreservedEnd E2 E2.x_B =
      if E1.x_B 0 ≤ E1.x_B 1 then E2.eA else E2.eB := by
      dsimp [ActionFramePreservedEnd]
      rw [← h_same_methods.2]
    rw [h_eq, ← h_same_ends.1, ← h_same_ends.2]
    exact h_presB
  have h_viol1A : ViolatesActionFrameMengerianEconomizing E1 E1.x_A := by
    refine ⟨E1.x_B, Or.inr rfl, ?_⟩
    rw [h_presA, h_presB]
    exact E1.pref_A_over_B h_opposite_preferences.1
  have h_not_viol1B : ¬ ViolatesActionFrameMengerianEconomizing E1 E1.x_B := by
    intro ⟨alt, halt, hpref⟩
    rw [h_presB] at hpref
    rcases halt with rfl | rfl
    · rw [h_presA] at hpref
      exact W.pref_asymm i1 t1 h1 (E1.pref_A_over_B h_opposite_preferences.1) hpref
    · rw [h_presB] at hpref
      exact pref_irrefl i1 t1 h1 E1.eA hpref
  have h_viol2B : ViolatesActionFrameMengerianEconomizing E2 E2.x_B := by
    refine ⟨E2.x_A, Or.inl rfl, ?_⟩
    rw [h_pres2A, h_pres2B]
    exact E2.pref_B_over_A h_opposite_preferences.2
  have h_not_viol2A : ¬ ViolatesActionFrameMengerianEconomizing E2 E2.x_A := by
    intro ⟨alt, halt, hpref⟩
    rw [h_pres2A] at hpref
    rcases halt with rfl | rfl
    · rw [h_pres2A] at hpref
      exact pref_irrefl i2 t2 h2 E2.eB hpref
    · rw [h_pres2B] at hpref
      exact W.pref_asymm i2 t2 h2 (E2.pref_B_over_A h_opposite_preferences.2) hpref
  refine ⟨h_anti, h_obs, h_viol1A, h_not_viol1B, h_viol2B, h_not_viol2A, ?_⟩
  intro planner_rule
  rw [h_obs]
  cases planner_rule (action_frame_non_market_observable E2)
  · exact Or.inr h_viol2B
  · exact Or.inl h_viol1A

end ActionFrameSocialistCalculation

-- Section 9: Monetary Production Outlays, Return Ratios, and Present-Endowment Choice Invariance

/-- Monetary accounting for a discrete production run partitioned into two factor
cost components (`factorCostA` and `factorCostB`) and gross output revenue
`grossRevenue` derived directly from action input and yield vectors. -/
structure MonetaryProductionOutlay (W : ActionFrame) (α : W.Action) (mA mB m_out : W.Means)
    (pA pB p_out : ℕ) where
  factorCostA : ℕ := W.use_means α mA * pA
  factorCostB : ℕ := W.use_means α mB * pB
  grossRevenue : ℕ := W.yield_means α m_out * p_out

/-- Total monetary input cost `factorCostA + factorCostB`. -/
def MonetaryProductionOutlay.totalCost {W : ActionFrame}
    {α : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O : MonetaryProductionOutlay W α mA mB m_out pA pB p_out) : ℕ :=
  O.factorCostA + O.factorCostB

/-- Net monetary return `grossRevenue - totalCost`. -/
def MonetaryProductionOutlay.netReturn {W : ActionFrame}
    {α : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O : MonetaryProductionOutlay W α mA mB m_out pA pB p_out) : ℕ :=
  O.grossRevenue - O.totalCost

/-- Cross-multiplied comparison of the factor-cost ratio `A_new / B_new > A_old / B_old`. -/
def HigherFactorARatio {W : ActionFrame}
    {α_new α_old : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O_new : MonetaryProductionOutlay W α_new mA mB m_out pA pB p_out)
    (O_old : MonetaryProductionOutlay W α_old mA mB m_out pA pB p_out) : Prop :=
  O_old.factorCostA * O_new.factorCostB < O_new.factorCostA * O_old.factorCostB

/-- Cross-multiplied comparison of the net return ratio
`netReturn_new / totalCost_new > netReturn_old / totalCost_old`. -/
def StrictlyHigherReturnRatio {W : ActionFrame}
    {α_new α_old : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O_new : MonetaryProductionOutlay W α_new mA mB m_out pA pB p_out)
    (O_old : MonetaryProductionOutlay W α_old mA mB m_out pA pB p_out) : Prop :=
  O_old.netReturn * O_new.totalCost < O_new.netReturn * O_old.totalCost

/-- When a production technique substitutes factor A for factor B (`A_old < A_new`
and `B_new < B_old`) while reducing input cost (`totalCost_new < totalCost_old`)
for at least the same gross revenue (`grossRevenue_old ≤ grossRevenue_new`), the
factor-A ratio, the net monetary return, and the return-to-cost ratio all strictly increase. -/
theorem cost_reduction_increases_net_return_and_ratio
    {W : ActionFrame} {α_old α_new : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O_old : MonetaryProductionOutlay W α_old mA mB m_out pA pB p_out)
    (O_new : MonetaryProductionOutlay W α_new mA mB m_out pA pB p_out)
    (h_pos_new : 0 < O_new.totalCost)
    (h_viable_old : O_old.totalCost ≤ O_old.grossRevenue)
    (h_a_rise : O_old.factorCostA < O_new.factorCostA)
    (h_b_fall : O_new.factorCostB < O_old.factorCostB)
    (h_b_pos : 0 < O_new.factorCostB)
    (h_cost_fall : O_new.totalCost < O_old.totalCost)
    (h_rev_ge : O_old.grossRevenue ≤ O_new.grossRevenue) :
    HigherFactorARatio O_new O_old ∧
    O_old.netReturn < O_new.netReturn ∧
    StrictlyHigherReturnRatio O_new O_old := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [HigherFactorARatio]
    have h1 : O_old.factorCostA * O_new.factorCostB < O_new.factorCostA * O_new.factorCostB :=
      Nat.mul_lt_mul_of_pos_right h_a_rise h_b_pos
    have h2 : O_new.factorCostA * O_new.factorCostB ≤ O_new.factorCostA * O_old.factorCostB :=
      Nat.mul_le_mul_left O_new.factorCostA (Nat.le_of_lt h_b_fall)
    exact lt_of_lt_of_le h1 h2
  · dsimp [MonetaryProductionOutlay.netReturn]
    omega
  · dsimp [StrictlyHigherReturnRatio, MonetaryProductionOutlay.netReturn]
    have h_ret_lt :
        O_old.grossRevenue - O_old.totalCost < O_new.grossRevenue - O_new.totalCost := by
      omega
    have h_step1 :
        (O_old.grossRevenue - O_old.totalCost) * O_new.totalCost <
        (O_new.grossRevenue - O_new.totalCost) * O_new.totalCost :=
      Nat.mul_lt_mul_of_pos_right h_ret_lt h_pos_new
    have h_step2 :
        (O_new.grossRevenue - O_new.totalCost) * O_new.totalCost ≤
        (O_new.grossRevenue - O_new.totalCost) * O_old.totalCost :=
      Nat.mul_le_mul_left (O_new.grossRevenue - O_new.totalCost) (Nat.le_of_lt h_cost_fall)
    exact lt_of_lt_of_le h_step1 h_step2

/-- If factor outlays adjust downward (`A_adj ≤ A_new` and `B_adj ≤ B_new`)
while preserving gross revenue relative to the initial technique, total input cost
remains strictly below the initial cost and the return-to-cost ratio strictly exceeds
the initial return ratio. -/
theorem input_cost_deflation_preserves_return_ratio
    {W : ActionFrame} {α_old α_new α_adj : W.Action} {mA mB m_out : W.Means} {pA pB p_out : ℕ}
    (O_old : MonetaryProductionOutlay W α_old mA mB m_out pA pB p_out)
    (O_new : MonetaryProductionOutlay W α_new mA mB m_out pA pB p_out)
    (O_adj : MonetaryProductionOutlay W α_adj mA mB m_out pA pB p_out)
    (h_pos_adj : 0 < O_adj.totalCost)
    (_h_viable_old : O_old.totalCost ≤ O_old.grossRevenue)
    (h_cost_fall : O_new.totalCost < O_old.totalCost)
    (h_adj_a : O_adj.factorCostA ≤ O_new.factorCostA)
    (h_adj_b : O_adj.factorCostB ≤ O_new.factorCostB)
    (h_rev_preserved : O_old.grossRevenue ≤ O_adj.grossRevenue) :
    O_adj.totalCost < O_old.totalCost ∧
    StrictlyHigherReturnRatio O_adj O_old := by
  have h_adj_le_new : O_adj.totalCost ≤ O_new.totalCost := by
    dsimp [MonetaryProductionOutlay.totalCost]
    omega
  have h_adj_lt_old : O_adj.totalCost < O_old.totalCost :=
    lt_of_le_of_lt h_adj_le_new h_cost_fall
  refine ⟨h_adj_lt_old, ?_⟩
  dsimp [StrictlyHigherReturnRatio, MonetaryProductionOutlay.netReturn]
  have h_ret_lt : O_old.grossRevenue - O_old.totalCost < O_adj.grossRevenue - O_adj.totalCost := by
    omega
  have h_step1 :
      (O_old.grossRevenue - O_old.totalCost) * O_adj.totalCost <
      (O_adj.grossRevenue - O_adj.totalCost) * O_adj.totalCost :=
    Nat.mul_lt_mul_of_pos_right h_ret_lt h_pos_adj
  have h_step2 :
      (O_adj.grossRevenue - O_adj.totalCost) * O_adj.totalCost ≤
      (O_adj.grossRevenue - O_adj.totalCost) * O_old.totalCost :=
    Nat.mul_le_mul_left (O_adj.grossRevenue - O_adj.totalCost) (Nat.le_of_lt h_adj_lt_old)
  exact lt_of_lt_of_le h_step1 h_step2

/-- Present-Endowment Choice Invariance:
In any `ActionFrame`, if two histories `h1` and `h2` pass through the same moment `t`,
then physical inventories (`ω`), contemplated menus (`A_cont`), intended ends, and preferences
are identical by tree bundle invariance axioms (`mem_hist`). Consequently, resource feasibility
(`A_feas`) and undominated choice are identical across `h1` and `h2`. -/
theorem present_endowment_choice_invariance
    [W : ActionFrame]
    (i : W.Agent) (t : W.Moment) (h1 h2 : W.History)
    (h1_mem : W.mem_hist t h1) (h2_mem : W.mem_hist t h2) :
    (∀ α, α ∈ W.A_feas i t h1 ↔ α ∈ W.A_feas i t h2) ∧
    (∀ α, (α ∈ W.A_feas i t h1 ∧ ∀ β ∈ W.A_feas i t h1,
        ¬ W.Preference i t h1 (W.End_of i β t h1) (W.End_of i α t h1)) ↔
      (α ∈ W.A_feas i t h2 ∧ ∀ β ∈ W.A_feas i t h2,
        ¬ W.Preference i t h2 (W.End_of i β t h2) (W.End_of i α t h2))) := by
  have h_same_ends : ∀ α, W.End_of i α t h1 = W.End_of i α t h2 :=
    fun α => W.End_of_bundle_invariant i α t h1_mem h2_mem
  have h_same_pref : W.Preference i t h1 = W.Preference i t h2 :=
    W.Preference_bundle_invariant i t h1_mem h2_mem
  have h_feas_eq : W.A_feas i t h1 = W.A_feas i t h2 :=
    W.A_feas_bundle_invariant i t h1_mem h2_mem
  have h_feas_iff : ∀ α, α ∈ W.A_feas i t h1 ↔ α ∈ W.A_feas i t h2 := by
    intro α
    rw [h_feas_eq]
  refine ⟨h_feas_iff, ?_⟩
  intro α
  constructor
  · rintro ⟨h_a, h_undom⟩
    refine ⟨(h_feas_iff α).mp h_a, ?_⟩
    intro β h_b
    rw [← h_same_ends β, ← h_same_ends α, ← h_same_pref]
    exact h_undom β ((h_feas_iff β).mpr h_b)
  · rintro ⟨h_a, h_undom⟩
    refine ⟨(h_feas_iff α).mpr h_a, ?_⟩
    intro β h_b
    rw [h_same_ends β, h_same_ends α, h_same_pref]
    exact h_undom β ((h_feas_iff β).mp h_b)

end Praxeology

end
