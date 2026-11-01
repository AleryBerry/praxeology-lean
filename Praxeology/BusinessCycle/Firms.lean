/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Entrepreneurship
public import Praxeology.Organization
public import Praxeology.FirmBoundary
public import Praxeology.FirmWitness

/-!
# Organized-Firm Specialization of the Entrepreneurial Cycle

The general theorem remains about any acting entrepreneur. This module shows
how an organized firm supplies the capital-accumulation step: an operator
produces an intermediate good, then a matched internal exchange puts it in the
principal's inventory. Firm-boundary evidence supplies the organization
network and its connection to an external market.
-/

@[expose] public section

namespace Praxeology

open ActionFrame

/-- In the existing workshop frame, a purposeful bilateral exchange can only
occur at the transfer or sale moment. This limits which credit lifecycles the
frame can witness without extending its ActionFrame. -/
theorem workshop_bilateral_exchange_moment
    (i j : WorkshopAgent) (t : WMoment) (h : WorkshopHist)
    (qA : ℕ) (mA : WorkshopMeans) (qB : ℕ) (mB : WorkshopMeans)
    (exchange : @BilateralExchange WorkshopActionFrame i j t h qA mA qB mB) :
    t = .transfer ∨ t = .sale := by
  have ⟨h_offer, h_accept⟩ := bilateral_exchange_enacted_actions
    (W := WorkshopActionFrame) i j t h qA mA qB mB exchange
  cases t <;> cases i <;> cases j
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | change w_enacted _ _ _ = _ at h_offer
      simp only [w_enacted] at h_offer
      first
      | split_ifs at h_offer
      | cases h_offer

/-- The workshop's only enacted exchange roles are operator-to-entrepreneur
at transfer and entrepreneur-to-customer at sale. -/
theorem workshop_bilateral_exchange_roles
    (i j : WorkshopAgent) (t : WMoment) (h : WorkshopHist)
    (qA : ℕ) (mA : WorkshopMeans) (qB : ℕ) (mB : WorkshopMeans)
    (exchange : @BilateralExchange WorkshopActionFrame i j t h qA mA qB mB) :
    (t = .transfer ∧ i = .operator ∧ j = .entrepreneur) ∨
      (t = .sale ∧ i = .entrepreneur ∧ j = .customer) := by
  have ⟨h_offer, _⟩ := bilateral_exchange_enacted_actions
    (W := WorkshopActionFrame) i j t h qA mA qB mB exchange
  cases t <;> cases i <;> cases j
  all_goals
    first
    | exact Or.inl ⟨rfl, rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl, rfl⟩
    | change w_enacted _ _ _ = _ at h_offer
      simp only [w_enacted] at h_offer
      first
      | split_ifs at h_offer; all_goals try cases h_offer
      | cases h_offer

/-- In the existing workshop frame, one lender cannot make purposeful
collateralized advances to two distinct borrowers. -/
theorem workshop_no_common_lender_distinct_borrowers
    {T₁ T₂ : PawnLoanTerms WorkshopActionFrame}
    (A₁ : CreditAdvance T₁) (A₂ : CreditAdvance T₂)
    (sameLender : T₁.lender = T₂.lender) :
    T₁.borrower = T₂.borrower := by
  have h₁ := workshop_bilateral_exchange_roles T₁.lender T₁.borrower
    A₁.moment A₁.history T₁.principal T₁.money
    T₁.collateralQuantity T₁.collateral A₁.purposefulExchange
  have h₂ := workshop_bilateral_exchange_roles T₂.lender T₂.borrower
    A₂.moment A₂.history T₂.principal T₂.money
    T₂.collateralQuantity T₂.collateral A₂.purposefulExchange
  rcases h₁ with ⟨_, h₁l, h₁b⟩ | ⟨_, h₁l, h₁b⟩
  · rcases h₂ with ⟨_, h₂l, h₂b⟩ | ⟨_, h₂l, h₂b⟩
    · exact h₁b.trans h₂b.symm
    · have h_impossible : WorkshopAgent.operator = WorkshopAgent.entrepreneur :=
        h₁l.symm.trans (sameLender.trans h₂l)
      cases h_impossible
  · rcases h₂ with ⟨_, h₂l, h₂b⟩ | ⟨_, h₂l, h₂b⟩
    · have h_impossible : WorkshopAgent.entrepreneur = WorkshopAgent.operator :=
        h₁l.symm.trans (sameLender.trans h₂l)
      cases h_impossible
    · exact h₁b.trans h₂b.symm

/-- In the workshop frame, an advance at the transfer moment must be followed
immediately by the sale moment. The terminal histories at transfer have no
matched offer and acceptance. -/
theorem workshop_credit_advance_next_at_transfer
    (T : PawnLoanTerms WorkshopActionFrame) (A : CreditAdvance T)
    (h_moment : A.moment = .transfer) :
    A.nextMoment = .sale := by
  have ⟨h_offer, h_accept⟩ := bilateral_exchange_enacted_actions
    (W := WorkshopActionFrame) T.lender T.borrower A.moment A.history
    T.principal T.money T.collateralQuantity T.collateral A.purposefulExchange
  have h_cases := workshop_next_moment_cases A.successor
  simp only [h_moment, reduceCtorEq, false_and, false_or, or_false, true_and] at h_cases
  rcases h_cases with h_sale | h11 | h12 | h13
  · exact h_sale.1
  · have h_offer' := h_offer
    rw [h_moment, h11.2] at h_offer'
    change w_enacted T.lender WMoment.transfer (11 : WorkshopHist) = _ at h_offer'
    have : False := by
      cases hl : T.lender <;> cases hb : T.borrower
      all_goals simp [w_enacted, hl, hb] at h_offer'
    exact this.elim
  · have h_accept' := h_accept
    rw [h_moment, h12.2] at h_accept'
    change w_enacted T.borrower WMoment.transfer (12 : WorkshopHist) = _ at h_accept'
    have : False := by
      cases hl : T.lender <;> cases hb : T.borrower
      all_goals simp [w_enacted, hl, hb] at h_accept'
    exact this.elim
  · have h_offer' := h_offer
    rw [h_moment, h13.2] at h_offer'
    change w_enacted T.lender WMoment.transfer (13 : WorkshopHist) = _ at h_offer'
    have : False := by
      cases hl : T.lender <;> cases hb : T.borrower
      all_goals simp [w_enacted, hl, hb] at h_offer'
    exact this.elim

/-- The existing workshop ActionFrame has no completed matched loan lifecycle:
every purposeful exchange is at transfer or sale, and either event leaves no
later purposeful exchange between the same parties on that history. -/
theorem workshop_no_credit_repayment
    (T : PawnLoanTerms WorkshopActionFrame) (A : CreditAdvance T) :
    ¬ Nonempty (CreditRepayment A) := by
  rintro ⟨R⟩
  have h_advance_moment := workshop_bilateral_exchange_moment
    T.lender T.borrower A.moment A.history T.principal T.money
    T.collateralQuantity T.collateral A.purposefulExchange
  have h_repayment_moment := workshop_bilateral_exchange_moment
    T.borrower T.lender R.moment A.history T.repayment T.money
    T.collateralQuantity T.collateral R.purposefulExchange
  have h_order : wprec A.moment R.moment :=
    wprec_trans A.successor.2.2.1 R.afterAdvance
  rcases h_advance_moment with h_transfer | h_sale
  · have h_after := R.afterAdvance
    rw [workshop_credit_advance_next_at_transfer T A h_transfer] at h_after
    rcases h_repayment_moment with h_repay_transfer | h_repay_sale
    · rw [h_repay_transfer] at h_after
      exact (wprec_irrefl .sale) h_after
    · rw [h_repay_sale] at h_after
      exact (wprec_irrefl .sale) h_after
  · rw [h_sale] at h_order
    rcases h_repayment_moment with h_repay_transfer | h_repay_sale
    · rw [h_repay_transfer] at h_order
      exact (by decide : ¬ wprec WMoment.sale WMoment.transfer) h_order
    · rw [h_repay_sale] at h_order
      exact (wprec_irrefl .sale) h_order

/-- Physical evidence for interpreting an accepted delegation transfer as a
capital-accumulation step and a later blocked completion. -/
structure DelegatedTransferCapitalEvidence {W : ActionFrame}
    {V : DelegationVocabulary W} {D : AcceptedDelegation V}
    (T : DelegatedInternalTransfer D) where
  postTransfer : W.Moment
  successor : IsNextMoment W.Precedence W.mem_hist T.transferMoment
    postTransfer D.history
  completion : W.Action
  complementary : W.Means
  unitDelivery : T.qA = 1
  initialCapital : W.omega D.principal T.transferMoment D.history T.mA = 0
  initialComplementary :
    W.omega D.principal T.transferMoment D.history complementary = 0
  capitalDistinctFromComplementary : T.mA ≠ complementary
  compensationDistinctFromComplementary : T.mB ≠ complementary
  completionRequiresComplementary : W.use_means completion complementary = 1

/-- Interpret an accepted internal transfer as the entrepreneur's observed
capital-formation transition using the bundled physical evidence. -/
def DelegatedInternalTransfer.toEntrepreneurialCapitalFormation
    {W : ActionFrame} {V : DelegationVocabulary W}
    {D : AcceptedDelegation V} (T : DelegatedInternalTransfer D)
    (E : DelegatedTransferCapitalEvidence T) :
    EntrepreneurialCapitalFormation D.principal D.history T.transferMoment
      E.postTransfer (W.Accept D.principal D.operator T.qA T.mA T.qB T.mB)
      T.mA := by
  rcases bilateral_exchange_enacted_actions D.operator D.principal T.transferMoment
      D.history T.qA T.mA T.qB T.mB T.trade with ⟨h_offer, h_accept⟩
  let step : InventoryStep W D.principal D.history T.transferMoment E.postTransfer :=
    .matchedAccept D.operator T.qA T.mA T.qB T.mB
      T.trade.1 h_accept h_offer E.successor
  have h_capital_use : step.effectiveUse T.mA = 0 := by
    simp [step, InventoryStep.effectiveUse, InventoryStep.action,
      W.use_means_accept, T.trade.2.1]
  have h_capital_yield : step.effectiveYield T.mA = 1 := by
    simp [step, InventoryStep.effectiveYield, InventoryStep.action,
      W.yield_means_accept, E.unitDelivery]
  exact ⟨step, rfl, E.initialCapital, h_capital_use, h_capital_yield⟩

/-- The complementary factor remains absent after the internal transfer. -/
theorem DelegatedTransferCapitalEvidence.postTransferComplementary
    {W : ActionFrame} {V : DelegationVocabulary W}
    {D : AcceptedDelegation V} (T : DelegatedInternalTransfer D)
    (E : DelegatedTransferCapitalEvidence T) :
    W.omega D.principal E.postTransfer D.history E.complementary = 0 := by
  rcases bilateral_exchange_enacted_actions D.operator D.principal T.transferMoment
      D.history T.qA T.mA T.qB T.mB T.trade with ⟨h_offer, h_accept⟩
  let step : InventoryStep W D.principal D.history T.transferMoment E.postTransfer :=
    .matchedAccept D.operator T.qA T.mA T.qB T.mB
      T.trade.1 h_accept h_offer E.successor
  have hbal := step.inventory_balance E.complementary
  have h_complementary_use : step.effectiveUse E.complementary = 0 := by
    simp [step, InventoryStep.effectiveUse, InventoryStep.action,
      W.use_means_accept, E.compensationDistinctFromComplementary.symm]
  have h_complementary_yield : step.effectiveYield E.complementary = 0 := by
    simp [step, InventoryStep.effectiveYield, InventoryStep.action,
      W.yield_means_accept, E.capitalDistinctFromComplementary.symm]
  rw [h_complementary_use, E.initialComplementary, h_complementary_yield] at hbal
  omega

/-- All evidence for an organized-firm cycle, with the internal transfer,
downstream market, physical transition, and contextual appraisal tied together
in one scenario. -/
structure DelegatedFirmCycleScenario [W : ActionFrame]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (Context : Type) where
  delegation : AcceptedDelegation V
  transfer : DelegatedInternalTransfer delegation
  market : IndependentMarketInterface V M
  principalIsMarketSeller : delegation.principal = market.sellerPrincipal
  historyAligned : delegation.history = market.history
  marketAfterWork : W.Precedence delegation.workMoment market.moment
  capital : DelegatedTransferCapitalEvidence transfer
  actualMaturity : W.Moment
  safeMaturity : W.Moment
  safeHistory : W.History
  safeAction : W.Action
  correspondence : W.ContextCorrespondence Context
  context : Context
  contextCompatible : correspondence.compatible delegation.principal
    transfer.transferMoment delegation.history context
  actualAdmitted : correspondence.admissible delegation.principal
    (W.decisionIndex transfer.transferMoment delegation.history
      transfer.transfer_incident) context
    (W.Accept delegation.principal delegation.operator transfer.qA transfer.mA
      transfer.qB transfer.mB) delegation.history actualMaturity
  safeFeasible : safeAction ∈ W.A_feas delegation.principal
    transfer.transferMoment delegation.history
  safeAdmitted : correspondence.admissible delegation.principal
    (W.decisionIndex transfer.transferMoment delegation.history
      transfer.transfer_incident) context safeAction safeHistory safeMaturity
  physicalOutcomes : W.OutcomesGroundedInEndowmentsFor delegation.principal
  safeBundleDominates : W.SubjectiveTeleologicalDominates delegation.principal
    actualMaturity delegation.history
    (W.omega delegation.principal safeMaturity safeHistory)
    (W.omega delegation.principal actualMaturity delegation.history)

/-- Named outputs of an organized-firm entrepreneurial cycle. -/
structure DelegatedFirmCycleConclusion [W : ActionFrame]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {Context : Type}
    (S : DelegatedFirmCycleScenario (W := W) (V := V) (M := M) Context) : Prop where
  firmStructure : (threeStageFirmNetwork S.delegation S.market
    S.principalIsMarketSeller S.historyAligned S.marketAfterWork).HasFirmStructure
  capitalAfterTransfer : W.omega S.delegation.principal S.capital.postTransfer
    S.delegation.history S.transfer.mA = 1
  complementaryStockAfter : W.omega S.delegation.principal S.capital.postTransfer
    S.delegation.history S.capital.complementary = 0
  completionBlocked : S.capital.completion ∉ W.A_feas S.delegation.principal
    S.capital.postTransfer S.delegation.history
  investmentPurposeful : PurposefulAct S.delegation.principal
    S.transfer.transferMoment S.delegation.history
    (W.Accept S.delegation.principal S.delegation.operator S.transfer.qA
      S.transfer.mA S.transfer.qB S.transfer.mB)
  contextualRegret : ContextMatchedRegret S.correspondence S.delegation.principal
    (W.decisionIndex S.transfer.transferMoment S.delegation.history
      S.transfer.transfer_incident) S.actualMaturity
    (W.Accept S.delegation.principal S.delegation.operator S.transfer.qA
      S.transfer.mA S.transfer.qB S.transfer.mB) S.safeAction

/-- Compose accepted delegation, its observed internal transfer, and an
independent downstream market into the organized-firm specialization of the
general entrepreneur cycle theorem. The three-stage organization network is
constructed from the same delegation and market witnesses, so the firm's
internal and external edges remain tied to the cycle evidence. -/
theorem delegated_firm_cycle_regret
    [W : ActionFrame] {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {Context : Type}
    (S : DelegatedFirmCycleScenario (W := W) (V := V) (M := M) Context) :
    DelegatedFirmCycleConclusion S := by
  let D := S.delegation
  let T := S.transfer
  let E := S.market
  let h_firm_seller := S.principalIsMarketSeller
  let h_same_history := S.historyAligned
  let h_market_after_task := S.marketAfterWork
  let postTransfer := S.capital.postTransfer
  let actualMaturity := S.actualMaturity
  let safeMaturity := S.safeMaturity
  let safeHistory := S.safeHistory
  let completion := S.capital.completion
  let safeAction := S.safeAction
  let complementary := S.capital.complementary
  let h_transfer_successor := S.capital.successor
  let h_unit_delivery := S.capital.unitDelivery
  let h_initial_capital := S.capital.initialCapital
  let h_initial_complementary := S.capital.initialComplementary
  let h_capital_ne_complementary := S.capital.capitalDistinctFromComplementary
  let h_compensation_ne_complementary := S.capital.compensationDistinctFromComplementary
  let h_completion_requires_complementary := S.capital.completionRequiresComplementary
  let C := S.correspondence
  let context := S.context
  let h_context := S.contextCompatible
  let h_actual_admitted := S.actualAdmitted
  let h_safe_feasible := S.safeFeasible
  let h_safe_admitted := S.safeAdmitted
  let h_physical_outcomes := S.physicalOutcomes
  let h_safe_bundle_dominates := S.safeBundleDominates
  have h_structure := threeStageFirmNetwork_has_firm_structure D E
    h_firm_seller h_same_history h_market_after_task
  have h_exchange_purposeful := bilateral_exchange_purposeful_actions
    D.operator D.principal T.transferMoment D.history
    T.qA T.mA T.qB T.mB T.trade
  let capitalEvidence : DelegatedTransferCapitalEvidence T := {
    postTransfer := postTransfer
    successor := h_transfer_successor
    completion := completion
    complementary := complementary
    unitDelivery := h_unit_delivery
    initialCapital := h_initial_capital
    initialComplementary := h_initial_complementary
    capitalDistinctFromComplementary := h_capital_ne_complementary
    compensationDistinctFromComplementary := h_compensation_ne_complementary
    completionRequiresComplementary := h_completion_requires_complementary }
  have h_formation := T.toEntrepreneurialCapitalFormation capitalEvidence
  have h_starve := capitalEvidence.postTransferComplementary T
  have h_req : 0 < W.use_means completion complementary := by
    rw [h_completion_requires_complementary]; decide
  let I : EntrepreneurialInvestment W := {
    i := D.principal
    naturalDecision := W.decisionIndex T.transferMoment D.history T.transfer_incident
    x := W.decisionIndex T.transferMoment D.history T.transfer_incident
    next := postTransfer
    actualMaturity := actualMaturity
    safeMaturity := safeMaturity
    safeHistory := safeHistory
    investment := W.Accept D.principal D.operator T.qA T.mA T.qB T.mB
    completion := completion
    safeAction := safeAction
    capital := T.mA
    complementary := complementary }
  let cycleScenario : EntrepreneurialCycleScenario W Context := {
    investment := I
    formation := by simpa [I, ActionFrame.decisionIndex,
      ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
      using h_formation
    evaluation := {
      correspondence := C
      safeFeasible := h_safe_feasible
      context := context
      contextCompatible := h_context
      actualAdmitted := by simpa [I, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
        using h_actual_admitted
      safeAdmitted := by simpa [I, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
        using h_safe_admitted
      physicalOutcomes := by simpa [I, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
        using h_physical_outcomes
      safeBundleDominates := by simpa [I, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
        using h_safe_bundle_dominates } }
  have h_cycle := cycleScenario.regret_of_starvation h_starve h_req h_exchange_purposeful.2
  have h_tuple :
      (threeStageFirmNetwork S.delegation S.market S.principalIsMarketSeller
        S.historyAligned S.marketAfterWork).HasFirmStructure ∧
      W.omega S.delegation.principal S.capital.postTransfer
        S.delegation.history S.transfer.mA = 1 ∧
      W.omega S.delegation.principal S.capital.postTransfer
        S.delegation.history S.capital.complementary = 0 ∧
      S.capital.completion ∉ W.A_feas S.delegation.principal
        S.capital.postTransfer S.delegation.history ∧
      PurposefulAct S.delegation.principal S.transfer.transferMoment
        S.delegation.history
        (W.Accept S.delegation.principal S.delegation.operator S.transfer.qA
          S.transfer.mA S.transfer.qB S.transfer.mB) ∧
      ContextMatchedRegret S.correspondence S.delegation.principal
        (W.decisionIndex S.transfer.transferMoment S.delegation.history
          S.transfer.transfer_incident) S.actualMaturity
        (W.Accept S.delegation.principal S.delegation.operator S.transfer.qA
          S.transfer.mA S.transfer.qB S.transfer.mB) S.safeAction := by
    simpa [cycleScenario, I, D, T, E, capitalEvidence,
      ActionFrame.decisionIndex, ActionFrame.DecisionIndex.history,
      ActionFrame.DecisionIndex.moment] using
      ⟨h_structure, h_cycle.1.capitalStockAfter, h_cycle.2,
      h_cycle.1.completionBlocked, h_cycle.1.purposefulInvestment,
      h_cycle.1.contextualRegret⟩
  rcases h_tuple with ⟨h_firm, h_capital, h_complementary,
    h_blocked, h_purposeful, h_regret⟩
  exact {
    firmStructure := h_firm
    capitalAfterTransfer := h_capital
    complementaryStockAfter := h_complementary
    completionBlocked := h_blocked
    investmentPurposeful := h_purposeful
    contextualRegret := h_regret }

theorem workshop_work_transfer_is_next :
    IsNextMoment wprec wmem WMoment.work WMoment.transfer (0 : WorkshopHist) := by
  refine ⟨by decide, by decide, trivial, ?_⟩
  intro τ _ h_between
  cases τ <;> simp [wprec] at h_between

theorem workshop_transfer_sale_is_next :
    IsNextMoment wprec wmem WMoment.transfer WMoment.sale (0 : WorkshopHist) := by
  refine ⟨by decide, by decide, trivial, ?_⟩
  intro τ _ h_between
  cases τ <;> simp [wprec] at h_between

/-- The workshop's accepted internal exchange is the concrete transfer
evidence used by the firm-cycle theorem. The operator produces the good at
`work`; the matched offer and acceptance transfer it to the entrepreneur at
`transfer`. -/
def workshopDelegatedInternalTransfer :
    DelegatedInternalTransfer workshopAcceptedDelegation where
  transferMoment := WMoment.transfer
  qA := 1
  mA := finalGood0Means
  qB := 2
  mB := tokenMeans
  rawMaterial := rawMeans
  operatorCapacity := capacityMeans
  transfer_incident := by
    change wmem WMoment.transfer (0 : WorkshopHist)
    decide
  work_precedes_transfer := trivial
  work_to_transfer_is_next := workshop_work_transfer_is_next
  task_enacted := by decide
  task_is_physical_production := by
    intro htrade
    change WorkshopActionFrame.IsTradeAction WorkshopAction.produceIntermediate0 at htrade
    rcases htrade with ⟨_, _, _, _, _, _, h_eq⟩ | ⟨_, _, _, _, _, _, h_eq⟩ <;>
      cases h_eq
  recipe_goods_distinct := by decide
  task_uses_raw_material := by decide
  task_uses_operator_capacity := by decide
  delivery_and_compensation_positive := by decide
  raw_material_available_at_work := by decide
  capacity_available_at_work := by decide
  no_opening_delivery_stock := by decide
  task_does_not_consume_delivered_good := by decide
  produced_delivery := by decide
  delivered_stock_at_transfer := by decide
  trade := by
    refine ⟨by decide, by decide, by decide,
      operator_purposeful_internal_offer, by decide,
      entrepreneur_purposeful_internal_acceptance, by decide⟩
  compensation_settled := by decide
  terms_authorized := by
    change workshopVocabulary.authorizesTerms WorkshopAction.proposeScope
      (WorkshopAction.offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans)
      (WorkshopAction.accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans)
    simp [workshopVocabulary, finalGood0Means, tokenMeans]

/-- A branch-aware correspondence for the workshop transfer node. It holds
the other agents' actions fixed while admitting any realized continuation of
the entrepreneur's chosen action. This admits the matched transfer branch
and the principal's safe idle branch under one context. -/
def workshopCycleCorrespondence :
    WorkshopActionFrame.ContextCorrespondence Unit where
  compatible := fun _ _ _ _ => True
  context_nonempty := by intro _ _; exact ⟨(), trivial⟩
  admissible := fun i x _ α hOut τ =>
    α ∈ WorkshopActionFrame.A_feas i x.moment x.history ∧
    WorkshopActionFrame.mem_hist x.moment hOut ∧
    WorkshopActionFrame.enacted i x.moment hOut = α ∧
    (∀ j, j ≠ i →
      WorkshopActionFrame.enacted j x.moment hOut =
        WorkshopActionFrame.enacted j x.moment x.history) ∧
    WorkshopActionFrame.mem_hist τ hOut ∧
    (x.moment = τ ∨ WorkshopActionFrame.Precedence x.moment τ)
  admissible_sound := by
    intro i x c α hOut τ hadm
    rcases hadm with ⟨hα, hOut_mem, h_enacted, h_coagent, hτ_mem, h_future⟩
    exact ⟨trivial, trivial, hOut_mem, h_enacted, h_coagent, hτ_mem, h_future⟩
  admissible_nonempty := by
    intro i x c α _hc hα
    let hOut := WorkshopActionFrame.sigma i x.moment α x.history
    let τ := WorkshopActionFrame.ExpectedMaturation i α x.moment hOut
    have h_real := WorkshopActionFrame.sigma_realization i x.moment
      x.history x.history x.2 hα x.2
    have h_maturation := WorkshopActionFrame.expected_maturation_mem_future
      i α x.moment hOut h_real.1 h_real.2
    refine ⟨hOut, τ, ⟨hα, h_real.1, h_real.2, ?_, h_maturation.1, h_maturation.2⟩⟩
    intro j hne
    exact WorkshopActionFrame.sigma_co_agency i j x.moment x.history x.history
      hne.symm x.2 hα x.2
  admissible_centering := by
    intro i x c _hc
    refine ⟨WorkshopActionFrame.ExpectedMaturation i
      (WorkshopActionFrame.enacted i x.moment x.history) x.moment x.history, ?_⟩
    refine ⟨WorkshopActionFrame.enacted_in_A_feas i x.moment x.history x.2,
      x.2, rfl, ?_, ?_, ?_⟩
    · intro j _hj
      rfl
    · exact (WorkshopActionFrame.expected_maturation_mem_future i
        (WorkshopActionFrame.enacted i x.moment x.history) x.moment x.history
        x.2 rfl).1
    · exact (WorkshopActionFrame.expected_maturation_mem_future i
        (WorkshopActionFrame.enacted i x.moment x.history) x.moment x.history
        x.2 rfl).2

def workshopCycleDecision : WorkshopActionFrame.DecisionIndex :=
  ActionFrame.decisionIndex WorkshopActionFrame WMoment.transfer (0 : WorkshopHist)
    (by change wmem WMoment.transfer (0 : WorkshopHist); decide)

def workshopCycleInvestment : WorkshopActionFrame.Action :=
  WorkshopAction.accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans

def workshopCycleCompletion : WorkshopActionFrame.Action :=
  WorkshopAction.produceIntermediate0

theorem workshop_safe_liquidity_dominates_bust :
    SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .entrepreneur WMoment.sale 0)
      (w_omega .entrepreneur .leaf12 12)
      (w_omega .entrepreneur .sale 0) := by
  classical
  have h_valued_ends_require_tokens : ∀ w,
      workshopValuedEnd .entrepreneur WMoment.sale 0 w →
        0 < workshop_requirement w tokenMeans := by
    intro w hw
    cases w <;>
      simp [workshopValuedEnd, workshop_requirement, tokenMeans] at hw ⊢
  refine ⟨?_, ⟨{WorkshopEnd.entrepreneurLiquidity}, ?_, ?_, ?_⟩⟩
  · intro S hS hAtt m
    have h_empty : S = ∅ := by
      ext w
      constructor
      · intro hw
        have hpositive := h_valued_ends_require_tokens w (hS w hw)
        have h_single := Finset.single_le_sum
          (f := fun w => workshop_requirement w tokenMeans)
          (fun _ _ => Nat.zero_le _) hw
        have h_bound := hAtt tokenMeans
        have h_bound_zero : S.sum
            (fun w => workshop_requirement w tokenMeans) ≤ 0 := by
          change S.sum (fun w => workshop_requirement w tokenMeans) ≤
            w_omega .entrepreneur .sale 0 tokenMeans at h_bound
          have hactual : w_omega .entrepreneur .sale 0 tokenMeans = 0 := by
            decide
          rw [hactual] at h_bound
          exact h_bound
        omega
      · intro hw
        simp at hw
    subst S
    simp
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    subst w
    simp [workshopValuedEnd]
  · intro m
    fin_cases m <;> decide
  · intro hAtt
    have htoken := hAtt tokenMeans
    change 2 ≤ w_omega .entrepreneur .sale 0 tokenMeans at htoken
    have hactual : w_omega .entrepreneur .sale 0 tokenMeans = 0 := by decide
    rw [hactual] at htoken
    omega

/-- Concrete three-agent workshop instantiation. The organization network
uses the accepted delegation for its internal edge and the existing
independent customer interface for its market edge. The cycle itself uses the
operator's produced good, the principal's matched acceptance, a cash-funded
idle branch, and the workshop's derived bust-liquidity preference. -/
theorem workshop_delegated_firm_cycle_regret :
    workshopFirmNetwork.HasFirmStructure ∧
    WorkshopActionFrame.omega .entrepreneur WMoment.sale (0 : WorkshopHist)
      finalGood0Means = 1 ∧
    WorkshopActionFrame.omega .entrepreneur WMoment.sale (0 : WorkshopHist)
      rawMeans = 0 ∧
    workshopCycleCompletion ∉ WorkshopActionFrame.A_feas
      (WorkshopAgent.entrepreneur)
      WMoment.sale (0 : WorkshopHist) ∧
    @PurposefulAct WorkshopActionFrame .entrepreneur WMoment.transfer
      (0 : WorkshopHist)
      workshopCycleInvestment ∧
    ContextMatchedRegret (F := WorkshopActionFrame) workshopCycleCorrespondence
      WorkshopAgent.entrepreneur workshopCycleDecision WMoment.sale workshopCycleInvestment
      WorkshopAction.idle := by
  let C : WorkshopActionFrame.ContextCorrespondence Unit := workshopCycleCorrespondence
  have h_actual : C.admissible .entrepreneur workshopCycleDecision ()
      workshopCycleInvestment (0 : WorkshopHist) WMoment.sale := by
    change workshopCycleInvestment ∈ w_A_feas .entrepreneur WMoment.transfer 0 ∧
      wmem WMoment.transfer 0 ∧
      w_enacted .entrepreneur WMoment.transfer 0 = workshopCycleInvestment ∧
      (∀ j, j ≠ .entrepreneur →
        w_enacted j WMoment.transfer 0 = w_enacted j WMoment.transfer 0) ∧
      wmem WMoment.sale 0 ∧ (WMoment.transfer = WMoment.sale ∨
        wprec WMoment.transfer WMoment.sale)
    refine ⟨by decide, by decide, by decide, ?_, by decide, Or.inr (by decide)⟩
    intro j hj
    cases j with
    | entrepreneur => exact (hj rfl).elim
    | operator => rfl
    | customer => rfl
  have h_safe : C.admissible .entrepreneur workshopCycleDecision ()
      WorkshopAction.idle (12 : WorkshopHist) WMoment.leaf12 := by
    change WorkshopAction.idle ∈ w_A_feas .entrepreneur WMoment.transfer 0 ∧
      wmem WMoment.transfer 12 ∧
      w_enacted .entrepreneur WMoment.transfer 12 = WorkshopAction.idle ∧
      (∀ j, j ≠ .entrepreneur →
        w_enacted j WMoment.transfer 12 = w_enacted j WMoment.transfer 0) ∧
      wmem WMoment.leaf12 12 ∧ (WMoment.transfer = WMoment.leaf12 ∨
        wprec WMoment.transfer WMoment.leaf12)
    refine ⟨by decide, by decide, by decide, ?_, by decide, Or.inr (by decide)⟩
    intro j hj
    cases j with
    | entrepreneur => exact (hj rfl).elim
    | operator => rfl
    | customer => rfl
  let S : DelegatedFirmCycleScenario (W := WorkshopActionFrame) Unit := {
    delegation := workshopAcceptedDelegation
    transfer := workshopDelegatedInternalTransfer
    market := workshopMarketInterface
    principalIsMarketSeller := rfl
    historyAligned := rfl
    marketAfterWork := trivial
    capital := {
      postTransfer := WMoment.sale
      successor := by
        change IsNextMoment wprec wmem WMoment.transfer WMoment.sale
          (0 : WorkshopHist)
        exact workshop_transfer_sale_is_next
      completion := workshopCycleCompletion
      complementary := rawMeans
      unitDelivery := rfl
      initialCapital := by decide
      initialComplementary := by decide
      capitalDistinctFromComplementary := by decide
      compensationDistinctFromComplementary := by decide
      completionRequiresComplementary := by decide }
    actualMaturity := WMoment.sale
    safeMaturity := WMoment.leaf12
    safeHistory := (12 : WorkshopHist)
    safeAction := WorkshopAction.idle
    correspondence := C
    context := ()
    contextCompatible := trivial
    actualAdmitted := by
      simpa [workshopCycleDecision, workshopCycleInvestment,
        workshopDelegatedInternalTransfer, AcceptedDelegation.principal,
        AcceptedDelegation.operator, AcceptedDelegation.history, workshopAcceptedDelegation,
        workshopProposal, workshopExecution, workshopEntrepreneur,
        workshopOperator, ActionFrame.Accept] using h_actual
    safeFeasible := by decide
    safeAdmitted := by
      simpa [workshopCycleDecision, workshopDelegatedInternalTransfer,
        AcceptedDelegation.principal, AcceptedDelegation.operator,
        AcceptedDelegation.history, workshopAcceptedDelegation, workshopProposal, workshopExecution,
        workshopEntrepreneur, workshopOperator] using h_safe
    physicalOutcomes := by intro _ _ _ _; rfl
    safeBundleDominates := by
      change SubjectiveTeleologicalDominates workshop_requirement
        (workshopValuedEnd .entrepreneur WMoment.sale (0 : WorkshopHist))
        (w_omega .entrepreneur .leaf12 (12 : WorkshopHist))
        (w_omega .entrepreneur .sale (0 : WorkshopHist))
      exact workshop_safe_liquidity_dominates_bust }
  have h_cycle := delegated_firm_cycle_regret S
  exact ⟨by simpa [workshopFirmNetwork, S] using h_cycle.firmStructure,
    h_cycle.capitalAfterTransfer, h_cycle.complementaryStockAfter,
    h_cycle.completionBlocked, h_cycle.investmentPurposeful,
    h_cycle.contextualRegret⟩

/-- A firm-boundary decision supplies an organized-firm ABCT case when its
accepted internal transfer is the entrepreneurial capital step. This result
explicitly retains the organization-network and market-boundary witnesses,
then applies the general entrepreneurial theorem to the principal. -/
structure OperationalFirmCycleScenario [W : ActionFrame] (Context : Type) where
  actor : W.Agent
  moment : W.Moment
  history : W.History
  stages : ℕ
  internalized : ℕ
  minimumInternalized : ℕ
  gridStep : ℕ
  upstreamFactor : ℕ
  jointFactor : ℕ
  internalDeadband : ℕ
  externalDeadband : ℕ
  projectedSpread : ℕ
  decision : OperationalFirmBoundaryDecision actor moment history stages
    internalized minimumInternalized gridStep projectedSpread
    upstreamFactor jointFactor internalDeadband externalDeadband
  postTransfer : W.Moment
  actualMaturity : W.Moment
  safeMaturity : W.Moment
  safeHistory : W.History
  completion : W.Action
  safeAction : W.Action
  complementary : W.Means
  transferSuccessor : IsNextMoment W.Precedence W.mem_hist
    decision.compensation.transferMoment postTransfer decision.proposal.history
  unitDelivery : decision.compensation.deliveredQuantity = 1
  initialCapital : W.omega decision.proposal.principal
    decision.compensation.transferMoment decision.proposal.history
    decision.compensation.deliveredGood = 0
  initialComplementary : W.omega decision.proposal.principal
    decision.compensation.transferMoment decision.proposal.history complementary = 0
  capitalDistinctFromComplementary : decision.compensation.deliveredGood ≠ complementary
  compensationDistinctFromComplementary :
    decision.compensation.compensationGood ≠ complementary
  completionRequiresComplementary : W.use_means completion complementary = 1
  correspondence : W.ContextCorrespondence Context
  context : Context
  contextCompatible : correspondence.compatible decision.proposal.principal
    decision.compensation.transferMoment decision.proposal.history context
  actualAdmitted : correspondence.admissible decision.proposal.principal
    (W.decisionIndex decision.compensation.transferMoment decision.proposal.history
      decision.compensation.transfer_incident)
    context
    (W.Accept decision.proposal.principal decision.proposal.operator
      decision.compensation.deliveredQuantity decision.compensation.deliveredGood
      decision.compensation.compensationQuantity decision.compensation.compensationGood)
    decision.proposal.history actualMaturity
  safeFeasible : safeAction ∈ W.A_feas decision.proposal.principal
    decision.compensation.transferMoment decision.proposal.history
  safeAdmitted : correspondence.admissible decision.proposal.principal
    (W.decisionIndex decision.compensation.transferMoment decision.proposal.history
      decision.compensation.transfer_incident)
    context safeAction safeHistory safeMaturity
  physicalOutcomes : W.OutcomesGroundedInEndowmentsFor decision.proposal.principal
  safeBundleDominates : W.SubjectiveTeleologicalDominates
    decision.proposal.principal actualMaturity decision.proposal.history
    (W.omega decision.proposal.principal safeMaturity safeHistory)
    (W.omega decision.proposal.principal actualMaturity decision.proposal.history)

/-- Network, choice, transfer, and contextual-regret witnesses supplied by a
completed operational-firm cycle scenario. -/
def OperationalFirmCycleWitness [W : ActionFrame] {Context : Type}
    (S : OperationalFirmCycleScenario (W := W) Context) : Prop :=
  ∃ h_principal : @PurposefulAct W S.decision.proposal.principal
      S.decision.proposal.decisionMoment S.decision.proposal.history
      S.decision.proposal.assignment,
    (∃ h_internal : (S.decision.organizationNetwork h_principal).internallyDirected
        (0 : Fin 3) (1 : Fin 3),
      (S.decision.organizationNetwork h_principal).accepted_direction h_internal =
        AcceptedDelegation.ofEvidence S.decision.proposal S.decision.execution h_principal
          S.decision.principal_instructs_task S.decision.operator_accepts
          S.decision.operator_executes) ∧
    (∃ h_external : (S.decision.organizationNetwork h_principal).marketInterface
        (1 : Fin 3) (2 : Fin 3),
      (S.decision.organizationNetwork h_principal).market_evidence h_external =
        S.decision.market) ∧
    (S.decision.organizationNetwork h_principal).HasFirmStructure ∧
    S.decision.proposal.history = S.decision.market.history ∧
    W.Precedence S.decision.execution.workMoment S.decision.market.moment ∧
    (W.omega S.decision.proposal.principal S.postTransfer
        S.decision.proposal.history S.decision.compensation.deliveredGood = 1 ∧
      W.omega S.decision.proposal.principal S.postTransfer
        S.decision.proposal.history S.complementary = 0 ∧
      S.completion ∉ W.A_feas S.decision.proposal.principal
        S.postTransfer S.decision.proposal.history ∧
      PurposefulAct S.decision.proposal.principal
        S.decision.compensation.transferMoment S.decision.proposal.history
        (W.Accept S.decision.proposal.principal S.decision.proposal.operator
          S.decision.compensation.deliveredQuantity S.decision.compensation.deliveredGood
          S.decision.compensation.compensationQuantity
          S.decision.compensation.compensationGood) ∧
      ContextMatchedRegret S.correspondence S.decision.proposal.principal
        (W.decisionIndex S.decision.compensation.transferMoment
          S.decision.proposal.history S.decision.compensation.transfer_incident)
        S.actualMaturity
        (W.Accept S.decision.proposal.principal S.decision.proposal.operator
          S.decision.compensation.deliveredQuantity S.decision.compensation.deliveredGood
          S.decision.compensation.compensationQuantity
          S.decision.compensation.compensationGood) S.safeAction)

structure OperationalFirmCycleConclusion [W : ActionFrame] {Context : Type}
    (S : OperationalFirmCycleScenario (W := W) Context) : Prop where
  boundary : OperationalFirmBoundaryConclusion S.decision
  firmCycle : OperationalFirmCycleWitness S

theorem operational_firm_cycle_regret
    [W : ActionFrame] {Context : Type}
    (S : OperationalFirmCycleScenario (W := W) Context) :
    OperationalFirmCycleConclusion S := by
  let dec := S.decision
  let postTransfer := S.postTransfer
  let actualMaturity := S.actualMaturity
  let safeMaturity := S.safeMaturity
  let safeHistory := S.safeHistory
  let completion := S.completion
  let safeAction := S.safeAction
  let complementary := S.complementary
  let h_transfer_successor := S.transferSuccessor
  let h_unit_delivery := S.unitDelivery
  let h_initial_capital := S.initialCapital
  let h_initial_complementary := S.initialComplementary
  let h_capital_ne_complementary := S.capitalDistinctFromComplementary
  let h_compensation_ne_complementary := S.compensationDistinctFromComplementary
  let h_completion_requires_complementary := S.completionRequiresComplementary
  let C := S.correspondence
  let context := S.context
  let h_context := S.contextCompatible
  let h_actual_admitted := S.actualAdmitted
  let h_safe_feasible := S.safeFeasible
  let h_safe_admitted := S.safeAdmitted
  let h_physical_outcomes := S.physicalOutcomes
  let h_safe_bundle_dominates := S.safeBundleDominates
  have h_boundary : OperationalFirmBoundaryConclusion dec :=
    purposeful_operational_firm_boundary dec
  have h_boundary_result := h_boundary
  rcases h_boundary_result with ⟨_, ⟨h_principal_purposeful, _, _⟩⟩
  let D := AcceptedDelegation.ofEvidence dec.proposal dec.execution
    h_principal_purposeful dec.principal_instructs_task dec.operator_accepts dec.operator_executes
  let T := DelegatedInternalTransfer.ofEvidence dec.proposal dec.execution
    h_principal_purposeful dec.principal_instructs_task dec.operator_accepts
    dec.operator_executes dec.compensation
  let O := dec.organizationNetwork h_principal_purposeful
  have h_network := dec.organizationNetwork_retains_evidence h_principal_purposeful
  rcases h_network with ⟨⟨h_internal, h_internal_edge⟩,
    ⟨h_external, h_external_edge⟩, h_same_history, h_work_precedes_sale⟩
  have h_firm : O.HasFirmStructure :=
    ⟨(0 : Fin 3), (1 : Fin 3), (2 : Fin 3), h_internal, h_external⟩
  have h_purposeful_pair := bilateral_exchange_purposeful_actions
    D.operator D.principal T.transferMoment D.history T.qA T.mA T.qB T.mB T.trade
  let capitalEvidence : DelegatedTransferCapitalEvidence T := {
    postTransfer := postTransfer
    successor := h_transfer_successor
    completion := completion
    complementary := complementary
    unitDelivery := h_unit_delivery
    initialCapital := h_initial_capital
    initialComplementary := h_initial_complementary
    capitalDistinctFromComplementary := h_capital_ne_complementary
    compensationDistinctFromComplementary := h_compensation_ne_complementary
    completionRequiresComplementary := h_completion_requires_complementary }
  have h_formation := T.toEntrepreneurialCapitalFormation capitalEvidence
  have h_starve := capitalEvidence.postTransferComplementary T
  have h_req : 0 < W.use_means completion complementary := by
    rw [h_completion_requires_complementary]; decide
  let I : EntrepreneurialInvestment W := {
    i := D.principal
    naturalDecision := W.decisionIndex T.transferMoment D.history T.transfer_incident
    x := W.decisionIndex T.transferMoment D.history T.transfer_incident
    next := postTransfer
    actualMaturity := actualMaturity
    safeMaturity := safeMaturity
    safeHistory := safeHistory
    investment := W.Accept D.principal D.operator T.qA T.mA T.qB T.mB
    completion := completion
    safeAction := safeAction
    capital := T.mA
    complementary := complementary }
  let cycleScenario : EntrepreneurialCycleScenario W Context := {
    investment := I
    formation := h_formation
    evaluation := {
      correspondence := C
      safeFeasible := h_safe_feasible
      context := context
      contextCompatible := h_context
      actualAdmitted := h_actual_admitted
      safeAdmitted := h_safe_admitted
      physicalOutcomes := h_physical_outcomes
      safeBundleDominates := h_safe_bundle_dominates } }
  have h_cycle := cycleScenario.regret_of_starvation h_starve h_req h_purposeful_pair.2
  have h_result : OperationalFirmBoundaryConclusion S.decision ∧
      OperationalFirmCycleWitness S := by
    simpa [cycleScenario, I, O] using
    ⟨h_boundary, h_principal_purposeful,
    ⟨h_internal, h_internal_edge⟩,
    ⟨h_external, h_external_edge⟩,
    by simpa [O] using h_firm,
    h_same_history, h_work_precedes_sale,
    ⟨h_cycle.1.capitalStockAfter, h_cycle.2,
      h_cycle.1.completionBlocked, h_cycle.1.purposefulInvestment,
      h_cycle.1.contextualRegret⟩⟩
  exact ⟨h_result.1, h_result.2⟩

end Praxeology
