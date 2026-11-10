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
public import Praxeology.Catallactics
public import Praxeology.Catallactics.Credit

/-!
# Entrepreneurship, Intertemporal Choice, and Capital Structure

This module models entrepreneurial capital formation, credit funding, and cycle
obstructions entirely through the native `ActionFrame` vocabulary. Rate suppression,
teleological appraisal flips, complementary factor starvation, and cash shortfalls
are derived from physical inventory balances and purposeful action, eliminating
all external wrapper hypothesis structures.
-/

@[expose] public section

namespace Praxeology

open ActionFrame

/-- Evidence that a matched credit advance finances an entrepreneur's decision
node. The loan must precede the decision, and its cash is not spent along the
observed inventory run between origination and that node. -/
structure EntrepreneurialCreditFunding
    {W : ActionFrame} [BilateralExchangeFrame W]
    (i : W.Agent) (x : W.DecisionIndex) (grossRate : ℚ) where
  terms : PawnLoanTerms W
  advance : CreditAdvance terms
  borrowerIsEntrepreneur : terms.borrower = i
  advanceHistoryIsDecisionHistory : advance.history = x.history
  advancePrecedesDecision : W.Precedence advance.nextMoment x.moment
  postAdvanceRun : InventoryRun W i advance.history advance.nextMoment x.moment
  loanCashNotSpent : postAdvanceRun.totalUse terms.money = 0
  quotedGrossRateMatches : terms.grossRepaymentFactor = grossRate

namespace EntrepreneurialCreditFunding

/-- The borrower has at least the advanced principal in cash at the decision
node, derived from the matched advance and the intervening inventory balance. -/
theorem principal_available_at_decision {W : ActionFrame} [BilateralExchangeFrame W]
    {i : W.Agent} {x : W.DecisionIndex} {grossRate : ℚ}
    (F : EntrepreneurialCreditFunding i x grossRate) :
    F.terms.principal ≤ W.omega i x.moment x.history F.terms.money := by
  have h_advance := F.advance.physical_transfer.1
  rw [F.borrowerIsEntrepreneur] at h_advance
  have h_post : F.terms.principal ≤
      W.omega i F.advance.nextMoment F.advance.history F.terms.money := by
    rw [h_advance]
    exact Nat.le_add_left _ _
  have h_run := F.postAdvanceRun.inventory_balance F.terms.money
  rw [F.loanCashNotSpent, Nat.add_zero] at h_run
  have h_decision : F.terms.principal ≤
      W.omega i x.moment F.advance.history F.terms.money := by omega
  rw [F.advanceHistoryIsDecisionHistory] at h_decision
  exact h_decision

/-- Cash from the observed advance makes a project feasible when it covers
the project's money input and all other inputs are independently covered. -/
theorem action_feasible_from_advance {W : ActionFrame} [BilateralExchangeFrame W]
    {i : W.Agent} {x : W.DecisionIndex} {grossRate : ℚ}
    (F : EntrepreneurialCreditFunding i x grossRate) (α : W.Action)
    (h_contemplated : α ∈ W.A_cont i x.moment x.history)
    (h_money_input : W.use_means α F.terms.money ≤ F.terms.principal)
    (h_other_inputs : ∀ m, m ≠ F.terms.money →
      W.use_means α m ≤ W.omega i x.moment x.history m) :
    α ∈ W.A_feas i x.moment x.history := by
  apply (feasible_iff_contemplated_and_resource_feasible
    i x.moment x.history α).2
  refine ⟨h_contemplated, ?_⟩
  intro m
  by_cases hm : m = F.terms.money
  · subst m
    exact le_trans h_money_input F.principal_available_at_decision
  · exact h_other_inputs m hm

end EntrepreneurialCreditFunding

/-- Teleological bundle dominance determines investment choice:
when suppressed credit rates make the post-repayment physical endowment bundle
strictly dominate status quo/safe action, the investment becomes purposeful.
Conversely, when unsuppressed natural rates leave status quo dominating the net
repayment bundle, investment is rejected as non-purposeful. -/
theorem teleological_bundle_dominance_flips_investment
    [W : ActionFrame] [BilateralExchangeFrame W]
    (i : W.Agent) (naturalDecision creditDecision : W.DecisionIndex)
    (investment : W.Action) (grossRate : ℚ)
    (funding : EntrepreneurialCreditFunding i creditDecision grossRate)
    (h_investment_active : investment ≠ W.alpha_zero)
    (b_zero b_nat b_cred : W.Means → ℕ)
    (h_nat_dom : W.SubjectiveTeleologicalDominates i naturalDecision.moment
      naturalDecision.history b_zero b_nat)
    (h_cred_dom : W.SubjectiveTeleologicalDominates i creditDecision.moment
      creditDecision.history b_cred b_zero)
    (h_ground_nat_zero :
      W.End_of i W.alpha_zero naturalDecision.moment naturalDecision.history =
        W.BundleEnd b_zero)
    (h_ground_nat_inv :
      W.End_of i investment naturalDecision.moment naturalDecision.history =
        W.BundleEnd b_nat)
    (h_ground_cred_inv :
      W.End_of i investment creditDecision.moment creditDecision.history =
        W.BundleEnd b_cred)
    (h_ground_cred_zero :
      W.End_of i W.alpha_zero creditDecision.moment creditDecision.history =
        W.BundleEnd b_zero)
    (h_credit_maximal : ∀ β ∈ W.A_feas i creditDecision.moment creditDecision.history,
      ¬ W.Preference i creditDecision.moment creditDecision.history
        (W.End_of i β creditDecision.moment creditDecision.history)
        (W.End_of i investment creditDecision.moment creditDecision.history))
    (h_credit_contemplated :
      investment ∈ W.A_cont i creditDecision.moment creditDecision.history)
    (h_credit_money_input :
      W.use_means investment funding.terms.money ≤ funding.terms.principal)
    (h_credit_other_inputs : ∀ m, m ≠ funding.terms.money →
      W.use_means investment m ≤
        W.omega i creditDecision.moment creditDecision.history m)
    (h_credit_executed :
      Exec i creditDecision.moment investment creditDecision.history) :
    ¬ PurposefulAct i naturalDecision.moment naturalDecision.history investment ∧
      PurposefulAct i creditDecision.moment creditDecision.history investment := by
  have h_nat_pref := W.teleological_bundle_dominance_induces_preference
    i naturalDecision.moment naturalDecision.history b_zero b_nat h_nat_dom
  rw [← h_ground_nat_zero, ← h_ground_nat_inv] at h_nat_pref
  have h_credit_feasible := funding.action_feasible_from_advance investment
    h_credit_contemplated h_credit_money_input h_credit_other_inputs
  have h_cred_pref := W.teleological_bundle_dominance_induces_preference
    i creditDecision.moment creditDecision.history b_cred b_zero h_cred_dom
  rw [← h_ground_cred_inv, ← h_ground_cred_zero] at h_cred_pref
  refine ⟨?_, ?_⟩
  · intro h_purp_nat
    rcases h_purp_nat.2.2.1 with h_zero | h_better
    · exact h_investment_active h_zero
    · exact W.pref_asymm i naturalDecision.moment naturalDecision.history
        h_better h_nat_pref
  · exact ⟨h_credit_feasible, h_credit_executed, Or.inr h_cred_pref, h_credit_maximal⟩

/-- Direct derivation of purposeful investment from credit advance funding and
maximal preference over the idle baseline. -/
theorem credit_funding_induces_purposeful_investment
    [W : ActionFrame] [BilateralExchangeFrame W]
    (i : W.Agent) (x : W.DecisionIndex)
    (investment : W.Action) (grossRate : ℚ)
    (funding : EntrepreneurialCreditFunding i x grossRate)
    (_h_investment_active : investment ≠ W.alpha_zero)
    (h_pref : W.Preference i x.moment x.history
      (W.End_of i investment x.moment x.history)
      (W.End_of i W.alpha_zero x.moment x.history))
    (h_maximal : ∀ β ∈ W.A_feas i x.moment x.history,
      ¬ W.Preference i x.moment x.history
        (W.End_of i β x.moment x.history)
        (W.End_of i investment x.moment x.history))
    (h_contemplated : investment ∈ W.A_cont i x.moment x.history)
    (h_money_input : W.use_means investment funding.terms.money ≤ funding.terms.principal)
    (h_other_inputs : ∀ m, m ≠ funding.terms.money →
      W.use_means investment m ≤ W.omega i x.moment x.history m)
    (h_executed : Exec i x.moment investment x.history) :
    PurposefulAct i x.moment x.history investment := by
  have h_feas := funding.action_feasible_from_advance investment
    h_contemplated h_money_input h_other_inputs
  exact ⟨h_feas, h_executed, Or.inr h_pref, h_maximal⟩

/-- A capital-accumulation transition may be production or a matched exchange.
Its physical yield and input are stated in inventory terms, so downstream
results do not assume that a firm or a lone producer creates capital from
nothing. -/
structure EntrepreneurialCapitalFormation
    {W : ActionFrame} [BilateralExchangeFrame W] (i : W.Agent) (h : W.History)
    (decision next : W.Moment) (investment : W.Action) (capital : W.Means) where
  transition : InventoryStep W i h decision next
  representsInvestment : transition.action = investment
  initialCapital : W.omega i decision h capital = 0
  capitalInput : transition.effectiveUse capital = 0
  capitalOutput : transition.effectiveYield capital = 1

namespace EntrepreneurialCapitalFormation

/-- The observed transition creates one unit of capital. -/
theorem capital_stock_after {W : ActionFrame} [BilateralExchangeFrame W]
    {i : W.Agent} {h : W.History}
    {decision next : W.Moment} {investment : W.Action}
    {capital : W.Means}
    (A : EntrepreneurialCapitalFormation i h decision next investment capital) :
    W.omega i next h capital = 1 := by
  have hbalance := A.transition.inventory_balance capital
  rw [A.capitalInput, A.initialCapital, A.capitalOutput] at hbalance
  omega

end EntrepreneurialCapitalFormation

/-- Stage completion is physically infeasible when any required complementary factor
is absent from the actor's endowment. -/
theorem completion_infeasible_of_factor_starvation {W : ActionFrame}
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (completion : W.Action) (complementary : W.Means)
    (h_stock : W.omega i t h complementary = 0)
    (h_req : 0 < W.use_means completion complementary) :
    completion ∉ W.A_feas i t h ∧ ¬ @PurposefulAct W i t h completion := by
  have h_short : W.omega i t h complementary < W.use_means completion complementary := by
    omega
  have h_infeas := infeasible_of_insufficient_endowment i t h completion complementary h_short
  exact ⟨h_infeas, fun h_purp => h_infeas h_purp.1⟩

/-- Stage completion is physically infeasible when the required cash input
exceeds the actor's available money endowment. -/
theorem completion_infeasible_of_cash_shortfall {W : ActionFrame}
    (i : W.Agent) (t : W.Moment) (h : W.History)
    (completion : W.Action) (money : W.Means)
    (h_short : W.omega i t h money < W.use_means completion money) :
    completion ∉ W.A_feas i t h ∧ ¬ @PurposefulAct W i t h completion := by
  have h_infeas := infeasible_of_insufficient_endowment i t h completion money h_short
  exact ⟨h_infeas, fun h_purp => h_infeas h_purp.1⟩

/-- A targeted sabotage structure where an agent holds an integrated capital bundle
requiring a complementary factor `m_comp`, and external non-consensual contraction
of even a single unit of `m_comp` strands the entire capital stock and blocks completion. -/
structure TargetedComplementarySabotage
    {W : ActionFrame} (i : W.Agent) (t : W.Moment) (h : W.History)
    (completion : W.Action) (m_cap m_comp : W.Means) (q_comp : ℕ) where
  m_diff : m_cap ≠ m_comp
  q_pos : 0 < q_comp
  has_cap : 0 < W.omega i t h m_cap
  has_comp : W.omega i t h m_comp = q_comp
  req_comp : W.use_means completion m_comp = q_comp
  req_cap : W.use_means completion m_cap ≤ W.omega i t h m_cap
  contemplated : completion ∈ W.A_cont i t h

namespace TargetedComplementarySabotage

/-- The post-sabotage endowment bundle contracting `m_comp` by 1 unit. -/
def postSabotageStock {W : ActionFrame} (i : W.Agent) (t : W.Moment) (h : W.History)
    (m_comp : W.Means) (q_comp : ℕ) : W.Means → ℕ :=
  fun m => if m = m_comp then q_comp - 1 else W.omega i t h m

/-- Sabotage contracts the complementary factor strictly below the critical threshold. -/
theorem post_sabotage_complementary_lt
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {completion : W.Action} {m_cap m_comp : W.Means} {q_comp : ℕ}
    (S : TargetedComplementarySabotage i t h completion m_cap m_comp q_comp) :
    postSabotageStock i t h m_comp q_comp m_comp < q_comp := by
  simp only [postSabotageStock, ↓reduceIte]
  have hq := S.q_pos
  omega

/-- Stripping one unit of the complementary factor strands the capital factor:
the effective capital stock falls to zero even though physical capital remains. -/
theorem post_sabotage_effective_capital_zero
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {completion : W.Action} {m_cap m_comp : W.Means} {q_comp : ℕ}
    (S : TargetedComplementarySabotage i t h completion m_cap m_comp q_comp) :
    complementaryEffectiveBundle m_cap m_comp q_comp
      (postSabotageStock i t h m_comp q_comp) m_cap = 0 := by
  simp [complementaryEffectiveBundle, S.post_sabotage_complementary_lt]

/-- If the post-sabotage stock is realized at history `h_post`, the completion action
becomes infeasible. -/
theorem post_sabotage_completion_infeasible
    {W : ActionFrame} {i : W.Agent} {t : W.Moment}
    {h_post : W.History} {completion : W.Action} {m_cap m_comp : W.Means} {q_comp : ℕ}
    (S : TargetedComplementarySabotage i t h_post completion m_cap m_comp q_comp)
    (h_contracted : W.omega i t h_post m_comp < q_comp) :
    completion ∉ W.A_feas i t h_post := by
  apply infeasible_of_insufficient_endowment i t h_post completion m_comp
  change W.omega i t h_post m_comp < W.use_means completion m_comp
  rw [S.req_comp]
  exact h_contracted

/-- Pre-sabotage stock strictly teleologically dominates post-sabotage stock
for any end requiring the complementary factor quantum. -/
theorem targeted_sabotage_teleological_dominance
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {completion : W.Action} {m_cap m_comp : W.Means} {q_comp : ℕ}
    (S : TargetedComplementarySabotage i t h completion m_cap m_comp q_comp)
    (req : W.Ends → W.Means → ℕ) (e_target : W.Ends)
    (h_target_comp : req e_target m_comp = q_comp)
    (h_target_other : ∀ m ≠ m_comp, req e_target m ≤ W.omega i t h m) :
    TeleologicalBundleDominates req
      (fun m => W.omega i t h m)
      (postSabotageStock i t h m_comp q_comp) := by
  constructor
  · intro Ends_set h_post_att m
    have h_le : postSabotageStock i t h m_comp q_comp m ≤ W.omega i t h m := by
      dsimp [postSabotageStock]
      split_ifs with hm
      · subst hm
        rw [S.has_comp]
        omega
      · exact le_rfl
    exact le_trans (h_post_att m) h_le
  · refine ⟨{e_target}, ?_, ?_⟩
    · rw [jointly_attains_singleton]
      dsimp [AttainsEnd]
      intro m
      by_cases hm : m = m_comp
      · subst m
        rw [h_target_comp, S.has_comp]
      · exact h_target_other m hm
    · rw [jointly_attains_singleton]
      dsimp [AttainsEnd]
      intro h_att
      have h_bound := h_att m_comp
      simp only [postSabotageStock, ↓reduceIte] at h_bound
      rw [h_target_comp] at h_bound
      have hq := S.q_pos
      omega

end TargetedComplementarySabotage

/-- Explicit evidence that a completion action is unavailable at the
post-investment node. Physical starvation and price-box cash shortfall both
construct this common certificate. -/
structure BlockedCompletion {W : ActionFrame} (i : W.Agent) (next : W.Moment)
    (h : W.History) (completion : W.Action) where
  infeasible : completion ∉ W.A_feas i next h

/-- Core entrepreneurial-cycle synthesis once stage completion is known to be
blocked. The comparison is admitted by one shared context, so regret is derived
from physical bundle dominance rather than supplied as a preference premise. -/
private theorem entrepreneurial_cycle_regret_of_blocked_completion
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex)
    (next actualMaturity safeMaturity : W.Moment)
    (safeHistory : W.History)
    (investment completion safeAction : W.Action)
    (capital : W.Means)
    (transition : InventoryStep W i x.history x.moment next)
    (h_transition_action : transition.action = investment)
    (h_initial_capital : W.omega i x.moment x.history capital = 0)
    (h_capital_input : transition.effectiveUse capital = 0)
    (h_capital_output : transition.effectiveYield capital = 1)
    (blocked : BlockedCompletion i next x.history completion)
    (h_purposeful : PurposefulAct i x.moment x.history investment)
    (h_safe_feasible : safeAction ∈ W.A_feas i x.moment x.history)
    (context : Context)
    (h_context : C.compatible i x.moment x.history context)
    (h_actual_admitted : C.admissible i x context investment x.history actualMaturity)
    (h_safe_admitted : C.admissible i x context safeAction safeHistory safeMaturity)
    (h_physical_outcomes : W.OutcomesGroundedInEndowmentsFor i)
    (h_safe_bundle_dominates : W.SubjectiveTeleologicalDominates i actualMaturity x.history
      (W.omega i safeMaturity safeHistory) (W.omega i actualMaturity x.history)) :
    W.omega i next x.history capital = 1 ∧
      transition.action = investment ∧
      completion ∉ W.A_feas i next x.history ∧
      PurposefulAct i x.moment x.history investment ∧
      ContextMatchedRegret C i x actualMaturity investment safeAction := by
  have hbalance := transition.inventory_balance capital
  rw [h_capital_input, h_initial_capital, h_capital_output] at hbalance
  have hcapital : W.omega i next x.history capital = 1 := by omega
  have h_pref := W.teleological_bundle_dominance_induces_preference i actualMaturity x.history
    (W.omega i safeMaturity safeHistory) (W.omega i actualMaturity x.history)
    h_safe_bundle_dominates
  have h_safe_ground : W.OutcomeOf i safeAction x.moment safeMaturity safeHistory =
      W.BundleEnd (W.omega i safeMaturity safeHistory) :=
    h_physical_outcomes safeAction x.moment safeMaturity safeHistory
  have h_actual_ground : W.OutcomeOf i investment x.moment actualMaturity x.history =
      W.BundleEnd (W.omega i actualMaturity x.history) :=
    h_physical_outcomes investment x.moment actualMaturity x.history
  rw [← h_safe_ground, ← h_actual_ground] at h_pref
  have h_regret : ContextMatchedRegret C i x actualMaturity investment safeAction := by
    exact ⟨h_safe_feasible, context, safeHistory, safeMaturity,
      h_context, h_actual_admitted, h_safe_admitted, h_pref⟩
  exact ⟨hcapital, h_transition_action, blocked.infeasible, h_purposeful, h_regret⟩

/-- General entrepreneurial ABCT synthesis for complementary-factor
starvation. The transition creates capital while leaving the required
complementary factor absent, which supplies the blocked-completion premise. -/
private theorem entrepreneurial_cycle_regret_from_starvation
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (C : W.ContextCorrespondence Context)
    (i : W.Agent) (x : W.DecisionIndex)
    (next actualMaturity safeMaturity : W.Moment)
    (safeHistory : W.History)
    (investment completion safeAction : W.Action)
    (capital complementary : W.Means)
    (formation : EntrepreneurialCapitalFormation i x.history x.moment next investment capital)
    (h_starve : W.omega i next x.history complementary = 0)
    (h_req : 0 < W.use_means completion complementary)
    (h_purposeful : PurposefulAct i x.moment x.history investment)
    (h_safe_feasible : safeAction ∈ W.A_feas i x.moment x.history)
    (context : Context)
    (h_context : C.compatible i x.moment x.history context)
    (h_actual_admitted : C.admissible i x context investment x.history actualMaturity)
    (h_safe_admitted : C.admissible i x context safeAction safeHistory safeMaturity)
    (h_physical_outcomes : W.OutcomesGroundedInEndowmentsFor i)
    (h_safe_bundle_dominates : W.SubjectiveTeleologicalDominates i actualMaturity x.history
      (W.omega i safeMaturity safeHistory) (W.omega i actualMaturity x.history)) :
    W.omega i next x.history capital = 1 ∧
      W.omega i next x.history complementary = 0 ∧
      completion ∉ W.A_feas i next x.history ∧
      PurposefulAct i x.moment x.history investment ∧
      ContextMatchedRegret C i x actualMaturity investment safeAction := by
  have h_infeas := completion_infeasible_of_factor_starvation i next x.history
    completion complementary h_starve h_req
  have hcore := entrepreneurial_cycle_regret_of_blocked_completion C i x
    next actualMaturity safeMaturity safeHistory investment completion safeAction capital
    formation.transition formation.representsInvestment
    formation.initialCapital formation.capitalInput
    formation.capitalOutput ⟨h_infeas.1⟩
    h_purposeful h_safe_feasible context h_context
    h_actual_admitted h_safe_admitted h_physical_outcomes h_safe_bundle_dominates
  rcases hcore with ⟨h_capital, _, h_blocked, h_choice, h_regret⟩
  exact ⟨h_capital, h_starve, h_blocked, h_choice, h_regret⟩

/-- The actors, decision nodes, actions, and capital goods that define a
cycle. Separating this identity data keeps appraisal and context evidence
small and makes it reusable. -/
structure EntrepreneurialInvestment (W : ActionFrame) where
  i : W.Agent
  naturalDecision : W.DecisionIndex
  x : W.DecisionIndex
  next : W.Moment
  actualMaturity : W.Moment
  safeMaturity : W.Moment
  safeHistory : W.History
  investment : W.Action
  completion : W.Action
  safeAction : W.Action
  capital : W.Means
  complementary : W.Means

/-- Bundle the context correspondence, matched history and maturity evidence,
and the physical bundle comparison used to derive regret. -/
structure ContextualCycleEvaluation {W : ActionFrame} (Context : Type)
    (I : EntrepreneurialInvestment W) where
  correspondence : W.ContextCorrespondence Context
  safeFeasible : I.safeAction ∈ W.A_feas I.i I.x.moment I.x.history
  context : Context
  contextCompatible : correspondence.compatible I.i I.x.moment I.x.history context
  actualAdmitted : correspondence.admissible I.i I.x context I.investment
    I.x.history I.actualMaturity
  safeAdmitted : correspondence.admissible I.i I.x context I.safeAction
    I.safeHistory I.safeMaturity
  physicalOutcomes : W.OutcomesGroundedInEndowmentsFor I.i
  safeBundleDominates : W.SubjectiveTeleologicalDominates I.i I.actualMaturity
    I.x.history (W.omega I.i I.safeMaturity I.safeHistory)
    (W.omega I.i I.actualMaturity I.x.history)

namespace ContextualCycleEvaluation

/-- Derive regret from the common context and physical comparison. -/
theorem regret {W : ActionFrame} {Context : Type}
    {I : EntrepreneurialInvestment W} (E : ContextualCycleEvaluation Context I) :
    ContextMatchedRegret E.correspondence I.i I.x I.actualMaturity
      I.investment I.safeAction := by
  have h_pref := W.teleological_bundle_dominance_induces_preference
    I.i I.actualMaturity I.x.history
    (W.omega I.i I.safeMaturity I.safeHistory)
    (W.omega I.i I.actualMaturity I.x.history)
    E.safeBundleDominates
  have h_safe_ground : W.OutcomeOf I.i I.safeAction I.x.moment
      I.safeMaturity I.safeHistory =
      W.BundleEnd (W.omega I.i I.safeMaturity I.safeHistory) :=
    E.physicalOutcomes I.safeAction I.x.moment I.safeMaturity I.safeHistory
  have h_actual_ground : W.OutcomeOf I.i I.investment I.x.moment
      I.actualMaturity I.x.history =
      W.BundleEnd (W.omega I.i I.actualMaturity I.x.history) :=
    E.physicalOutcomes I.investment I.x.moment I.actualMaturity I.x.history
  rw [← h_safe_ground, ← h_actual_ground] at h_pref
  exact ⟨E.safeFeasible, E.context, I.safeHistory, I.safeMaturity,
    E.contextCompatible, E.actualAdmitted, E.safeAdmitted, h_pref⟩

end ContextualCycleEvaluation

/-- Physical-to-teleological grounding for cycle regret: every valued bundle
attainable on the actual branch is attainable on the safe branch, and the safe
branch attains a valued end that the actual branch misses on `money`. -/
structure StrandedCapitalRegretGrounding
    [W : ActionFrame] (I : EntrepreneurialInvestment W) (money : W.Means) where
  targetEnd : W.Ends
  targetValued : W.ValuedEnd I.i I.actualMaturity I.x.history targetEnd
  safePreservesAttainableEnds :
    ∀ S : Finset W.Ends,
      (∀ w ∈ S, W.ValuedEnd I.i I.actualMaturity I.x.history w) →
      (∀ m, S.sum (fun w => W.requirement w m) ≤
        W.omega I.i I.actualMaturity I.x.history m) →
      (∀ m, S.sum (fun w => W.requirement w m) ≤
        W.omega I.i I.safeMaturity I.safeHistory m)
  safeAttainsTarget :
    ∀ m, W.requirement targetEnd m ≤
      W.omega I.i I.safeMaturity I.safeHistory m
  actualLiquidShortfall :
    W.omega I.i I.actualMaturity I.x.history money <
      W.requirement targetEnd money

namespace StrandedCapitalRegretGrounding

/-- The safe branch's physical bundle strictly dominates the actual bundle
over ends valued at actual maturity. -/
theorem safe_bundle_dominates
    [W : ActionFrame] {I : EntrepreneurialInvestment W} {money : W.Means}
    (G : StrandedCapitalRegretGrounding I money) :
    W.SubjectiveTeleologicalDominates I.i I.actualMaturity I.x.history
      (W.omega I.i I.safeMaturity I.safeHistory)
      (W.omega I.i I.actualMaturity I.x.history) := by
  refine ⟨G.safePreservesAttainableEnds, ⟨{G.targetEnd}, ?_, ?_, ?_⟩⟩
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact G.targetValued
  · intro m
    simpa using G.safeAttainsTarget m
  · intro h_att
    have h_money := h_att money
    simp only [Finset.sum_singleton] at h_money
    have h_short := G.actualLiquidShortfall
    omega

end StrandedCapitalRegretGrounding

/-- The capital formation and contextual evaluation for one entrepreneurial cycle. -/
structure EntrepreneurialCycleScenario (W : ActionFrame) [BilateralExchangeFrame W]
    (Context : Type) where
  investment : EntrepreneurialInvestment W
  formation : EntrepreneurialCapitalFormation investment.i
    investment.x.history investment.x.moment investment.next
    investment.investment investment.capital
  evaluation : ContextualCycleEvaluation Context investment

/-- Admitted regret and the physical conclusions of a general cycle. -/
structure EntrepreneurialCycleConclusion {W : ActionFrame} [BilateralExchangeFrame W]
    {Context : Type} (S : EntrepreneurialCycleScenario W Context) : Prop where
  capitalStockAfter : W.omega S.investment.i S.investment.next
    S.investment.x.history S.investment.capital = 1
  completionBlocked : S.investment.completion ∉ W.A_feas S.investment.i
    S.investment.next S.investment.x.history
  purposefulInvestment : PurposefulAct S.investment.i S.investment.x.moment
    S.investment.x.history S.investment.investment
  contextualRegret : ContextMatchedRegret S.evaluation.correspondence
    S.investment.i S.investment.x S.investment.actualMaturity
    S.investment.investment S.investment.safeAction

/-- Complete a cycle once a separate obstruction and purposeful choice are given. -/
theorem EntrepreneurialCycleScenario.regret_of_blocked_completion
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (blocked : BlockedCompletion S.investment.i S.investment.next
      S.investment.x.history S.investment.completion)
    (purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    EntrepreneurialCycleConclusion S := by
  have hcore := entrepreneurial_cycle_regret_of_blocked_completion
    S.evaluation.correspondence S.investment.i S.investment.x
    S.investment.next S.investment.actualMaturity S.investment.safeMaturity
    S.investment.safeHistory S.investment.investment S.investment.completion
    S.investment.safeAction S.investment.capital
    S.formation.transition S.formation.representsInvestment
    S.formation.initialCapital S.formation.capitalInput S.formation.capitalOutput
    blocked purposeful S.evaluation.safeFeasible S.evaluation.context
    S.evaluation.contextCompatible S.evaluation.actualAdmitted
    S.evaluation.safeAdmitted S.evaluation.physicalOutcomes
    S.evaluation.safeBundleDominates
  rcases hcore with ⟨h_capital, _, h_blocked, h_choice, h_regret⟩
  exact {
    capitalStockAfter := h_capital
    completionBlocked := h_blocked
    purposefulInvestment := h_choice
    contextualRegret := h_regret }

/-- Starvation supplies the common blocked-completion certificate. -/
theorem EntrepreneurialCycleScenario.regret_of_starvation
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (h_starve : W.omega S.investment.i S.investment.next S.investment.x.history
      S.investment.complementary = 0)
    (h_req : 0 < W.use_means S.investment.completion S.investment.complementary)
    (purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    EntrepreneurialCycleConclusion S ∧
    W.omega S.investment.i S.investment.next S.investment.x.history
      S.investment.complementary = 0 := by
  have h_infeas := completion_infeasible_of_factor_starvation
    S.investment.i S.investment.next S.investment.x.history
    S.investment.completion S.investment.complementary h_starve h_req
  have h_cycle := S.regret_of_blocked_completion ⟨h_infeas.1⟩ purposeful
  exact ⟨h_cycle, h_starve⟩

/-- Cash shortfall supplies the common blocked-completion certificate. -/
theorem EntrepreneurialCycleScenario.regret_of_cash_shortfall
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (money : W.Means)
    (h_short : W.omega S.investment.i S.investment.next S.investment.x.history money <
      W.use_means S.investment.completion money)
    (purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    EntrepreneurialCycleConclusion S := by
  have h_infeas := completion_infeasible_of_cash_shortfall
    S.investment.i S.investment.next S.investment.x.history
    S.investment.completion money h_short
  exact S.regret_of_blocked_completion ⟨h_infeas.1⟩ purposeful

/-- Named conclusion for a credit-financed cycle with rejected natural-rate project
and purposeful credit-rate project. -/
structure CreditFinancedCycleConclusion {W : ActionFrame} [BilateralExchangeFrame W]
    {Context : Type} (S : EntrepreneurialCycleScenario W Context) : Prop where
  cycle : EntrepreneurialCycleConclusion S
  rejectedAtNaturalRate : ¬ PurposefulAct S.investment.i
    S.investment.naturalDecision.moment S.investment.naturalDecision.history
    S.investment.investment
  purposefulAtCreditRate : PurposefulAct S.investment.i
    S.investment.x.moment S.investment.x.history
    S.investment.investment

/-- Combined credit-financed starvation result. -/
structure CreditFinancedStarvationConclusion {W : ActionFrame} [BilateralExchangeFrame W]
    {Context : Type} (S : EntrepreneurialCycleScenario W Context) : Prop where
  cycle : CreditFinancedCycleConclusion S
  complementaryStockAfter : W.omega S.investment.i S.investment.next
    S.investment.x.history S.investment.complementary = 0

/-- Credit-financed entrepreneurial cycle theorem.
Deduces rejection at the natural rate and purposeful adoption at the credit rate via
`teleological_bundle_dominance_flips_investment`, culminating in capital starvation and regret. -/
theorem credit_financed_entrepreneurial_cycle_regret
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (grossRate : ℚ)
    (funding : EntrepreneurialCreditFunding S.investment.i S.investment.x grossRate)
    (h_inv_active : S.investment.investment ≠ W.alpha_zero)
    (b_zero b_nat b_cred : W.Means → ℕ)
    (h_nat_dom : W.SubjectiveTeleologicalDominates S.investment.i
      S.investment.naturalDecision.moment S.investment.naturalDecision.history
      b_zero b_nat)
    (h_cred_dom : W.SubjectiveTeleologicalDominates S.investment.i
      S.investment.x.moment S.investment.x.history b_cred b_zero)
    (h_ground_nat_zero :
      W.End_of S.investment.i W.alpha_zero S.investment.naturalDecision.moment
        S.investment.naturalDecision.history = W.BundleEnd b_zero)
    (h_ground_nat_inv :
      W.End_of S.investment.i S.investment.investment
        S.investment.naturalDecision.moment S.investment.naturalDecision.history =
        W.BundleEnd b_nat)
    (h_ground_cred_inv :
      W.End_of S.investment.i S.investment.investment S.investment.x.moment
        S.investment.x.history = W.BundleEnd b_cred)
    (h_ground_cred_zero :
      W.End_of S.investment.i W.alpha_zero S.investment.x.moment
        S.investment.x.history = W.BundleEnd b_zero)
    (h_credit_maximal : ∀ β ∈ W.A_feas S.investment.i S.investment.x.moment
        S.investment.x.history,
      ¬ W.Preference S.investment.i S.investment.x.moment S.investment.x.history
        (W.End_of S.investment.i β S.investment.x.moment S.investment.x.history)
        (W.End_of S.investment.i S.investment.investment S.investment.x.moment
          S.investment.x.history))
    (h_credit_contemplated :
      S.investment.investment ∈ W.A_cont S.investment.i S.investment.x.moment
        S.investment.x.history)
    (h_credit_money_input :
      W.use_means S.investment.investment funding.terms.money ≤ funding.terms.principal)
    (h_credit_other_inputs : ∀ m, m ≠ funding.terms.money →
      W.use_means S.investment.investment m ≤
        W.omega S.investment.i S.investment.x.moment S.investment.x.history m)
    (h_credit_executed :
      Exec S.investment.i S.investment.x.moment S.investment.investment
        S.investment.x.history)
    (h_starve : W.omega S.investment.i S.investment.next S.investment.x.history
      S.investment.complementary = 0)
    (h_req : 0 < W.use_means S.investment.completion S.investment.complementary) :
    CreditFinancedStarvationConclusion S := by
  have ⟨h_natural_rejected, h_credit_purposeful⟩ :=
    teleological_bundle_dominance_flips_investment
      S.investment.i S.investment.naturalDecision S.investment.x
      S.investment.investment grossRate funding h_inv_active
      b_zero b_nat b_cred h_nat_dom h_cred_dom
      h_ground_nat_zero h_ground_nat_inv h_ground_cred_inv h_ground_cred_zero
      h_credit_maximal h_credit_contemplated h_credit_money_input
      h_credit_other_inputs h_credit_executed
  have h_regret := S.regret_of_starvation h_starve h_req h_credit_purposeful
  exact {
    cycle := {
      cycle := h_regret.1
      rejectedAtNaturalRate := h_natural_rejected
      purposefulAtCreditRate := h_credit_purposeful
    }
    complementaryStockAfter := h_regret.2
  }

-- Section: Catallactic Bottleneck Pre-Emption

/-- Catallactic Bottleneck Pre-Emption:
Distinguishes direct coercive menu stripping from catallactic pre-emption.
When rival `j` outbids entrepreneur `i` for factor supplier `k`'s inventory, passive bystander `i`'s
autarkic stock and feasible action menu remain completely uninvaded and unstripped
(`ResourceMenuPreserved` and `∀ γ, ¬ FeasibleMenuStripped i t t' h γ`). However, because
`complementary` remains absent from `i`'s endowment (and depleted at supplier `k`), stage-2
completion suffers `BlockedCompletion`, proving that catallactic competition can defeat an
entrepreneurial plan without any physical or normative invasion of the entrepreneur's property. -/
theorem catallactic_bottleneck_preemption_preserves_menu_but_blocks_completion
    [W : ActionFrame] [BilateralExchangeFrame W]
    (i : W.Agent) (t t' : W.Moment) (h : W.History)
    (completion : W.Action) (complementary : W.Means)
    (h_passive_i : W.enacted i t h = W.alpha_zero)
    (h_starve_i : W.omega i t h complementary = 0)
    (h_req : 0 < W.use_means completion complementary)
    (h_next : IsNextMoment W.Precedence W.mem_hist t t' h) :
    StockPreserved i t t' h ∧
    ResourceMenuPreserved i t t' h ∧
    (∀ γ, ¬ FeasibleMenuStripped i t t' h γ) ∧
    W.omega i t' h complementary = 0 ∧
    BlockedCompletion i t' h completion := by
  have h_stock_i := W.inaction_preserves_endowments i t t' h h_passive_i h_next
  have h_pres_i : StockPreserved i t t' h := by
    intro m
    have h_eq := h_stock_i m
    dsimp [StockPreserved, omega] at *
    omega
  have h_menu_i := stockPreserved_implies_resourceMenuPreserved i t t' h h_pres_i
  have h_nostrip_i : ∀ γ, ¬ FeasibleMenuStripped i t t' h γ :=
    fun γ => stockPreserved_implies_no_feasibleMenuStripped i t t' h h_pres_i γ
  have h_starve_post : W.omega i t' h complementary = 0 := by
    rw [h_stock_i complementary, h_starve_i]
  have h_infeas : completion ∉ W.A_feas i t' h := by
    intro h_feas
    have h_le := (W.A_feas_coupling i t' h completion).mp h_feas |>.2 complementary
    omega
  exact ⟨h_pres_i, h_menu_i, h_nostrip_i, h_starve_post, ⟨h_infeas⟩⟩

/-- Catallactic Bottleneck Pre-Emption Cycle Regret:
Derives the complete entrepreneurial cycle conclusion under catallactic pre-emption. -/
theorem catallactic_bottleneck_preemption_cycle_regret
    [W : ActionFrame] [BilateralExchangeFrame W] {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (h_starve : W.omega S.investment.i S.investment.next S.investment.x.history
      S.investment.complementary = 0)
    (h_req : 0 < W.use_means S.investment.completion S.investment.complementary)
    (purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    EntrepreneurialCycleConclusion S ∧
    BlockedCompletion S.investment.i S.investment.next S.investment.x.history
      S.investment.completion := by
  have h_blocked : BlockedCompletion S.investment.i S.investment.next
      S.investment.x.history S.investment.completion := by
    have h_infeas := completion_infeasible_of_factor_starvation
      S.investment.i S.investment.next S.investment.x.history
      S.investment.completion S.investment.complementary h_starve h_req
    exact ⟨h_infeas.1⟩
  have h_cycle := S.regret_of_blocked_completion h_blocked purposeful
  exact ⟨h_cycle, h_blocked⟩

/-- Under network-topological monetary diffusion, a downstream entrepreneur situated at
distance `hop_stage < diff.hop_dist S.investment.i` holds unaugmented cash balance.
When the upstream factor price wave `P_wave` exceeds the entrepreneur's unaugmented cash,
project completion becomes physically infeasible, blocking completion and inducing
entrepreneurial cycle failure with contextual regret. -/
theorem spatial_cantillon_malinvestment_squeeze
    [W : ActionFrame] [BilateralExchangeFrame W] [DecidableEq W.Agent]
    {Context : Type}
    (S : EntrepreneurialCycleScenario W Context)
    (diff : CantillonNetworkDiffusion W.Agent)
    (v_b : W.Agent → ℕ)
    (hop_stage : ℕ) (P_pre P_wave : ℕ) (m_money : W.Means)
    (h_downstream : hop_stage < diff.hop_dist S.investment.i)
    (h_intra_pre : P_pre ≤ v_b S.investment.i)
    (h_below_wave : v_b S.investment.i < P_wave)
    (h_cash_below_wave :
      W.omega S.investment.i S.investment.next S.investment.x.history m_money < P_wave)
    (h_wave_cost : P_wave ≤ W.use_means S.investment.completion m_money)
    (h_purposeful : PurposefulAct S.investment.i S.investment.x.moment
      S.investment.x.history S.investment.investment) :
    P_pre ≤ diff.effective_bid v_b 0 S.investment.i ∧
    diff.effective_bid v_b hop_stage S.investment.i < P_wave ∧
    diff.effective_cash
      (fun a => W.omega a S.investment.next S.investment.x.history m_money)
      hop_stage S.investment.i =
      W.omega S.investment.i S.investment.next S.investment.x.history m_money ∧
    BlockedCompletion S.investment.i S.investment.next S.investment.x.history
      S.investment.completion ∧
    EntrepreneurialCycleConclusion S := by
  have h_bid := cantillon_hop_shifts_clearing_price_and_crowds_out_downstream
    diff v_b hop_stage P_pre P_wave S.investment.i h_downstream h_intra_pre h_below_wave
  have h_not_le : ¬ (diff.hop_dist S.investment.i ≤ hop_stage) := by omega
  have h_cash : diff.effective_cash
      (fun a => W.omega a S.investment.next S.investment.x.history m_money)
      hop_stage S.investment.i =
      W.omega S.investment.i S.investment.next S.investment.x.history m_money := by
    dsimp [CantillonNetworkDiffusion.effective_cash]
    split_ifs; omega
  have h_short : W.omega S.investment.i S.investment.next S.investment.x.history m_money <
      W.use_means S.investment.completion m_money :=
    lt_of_lt_of_le h_cash_below_wave h_wave_cost
  have h_infeas := completion_infeasible_of_cash_shortfall
    S.investment.i S.investment.next S.investment.x.history
    S.investment.completion m_money h_short
  have h_blocked : BlockedCompletion S.investment.i S.investment.next
      S.investment.x.history S.investment.completion := ⟨h_infeas.1⟩
  have h_cycle := S.regret_of_blocked_completion h_blocked h_purposeful
  exact ⟨h_bid.1, h_bid.2, h_cash, h_blocked, h_cycle⟩

end Praxeology
