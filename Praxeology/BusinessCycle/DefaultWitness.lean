/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.CreditLifecycleFrame

/-!
# Unpaid maturity in the finite credit lifecycle

This witness reuses a branch of the existing credit lifecycle tree. The first
advance is purposeful; the later repayment decision contains the borrower's
inaction and an unmatched lender acceptance. The branch reaches stated
maturity immediately after that decision. Inventory accounting includes an
intervening collateralized advance to another borrower. The witness does not
represent legal title or a foreclosure judgment.
-/

@[expose] public section

namespace Praxeology
namespace CreditLifecycleTree

local instance : ActionFrame := creditLifecycleActionFrame

abbrev LifecyclePurposefulAct (i : WorkshopAgent) (t : Node) (h : History)
    (α : WorkshopAction) : Prop :=
  @PurposefulAct creditLifecycleActionFrame i t h α

/-- A history on which the first advance is matched, a second advance is
matched, the borrower idles at the first repayment decision, and maturity is
the resulting branch endpoint at node fourteen. -/
def unpaidMaturityHistory : History := historyByIndex 8

/-- The endpoint of the unpaid-maturity history. -/
def unpaidMaturityMoment : Node := lifecycleLeaf unpaidMaturityHistory

/-- At the later advance event, the operator's offer and the customer's
acceptance match on this branch. -/
theorem unpaid_history_second_advance_is_matched :
    creditLifecycleActionFrame.enacted .operator secondAdvanceMoment
        unpaidMaturityHistory = secondAdvanceOffer ∧
    creditLifecycleActionFrame.enacted .customer secondAdvanceMoment
        unpaidMaturityHistory = secondAdvanceAccept := by
  decide

/-- At the repayment decision on this branch, the borrower idles while the
lender accepts. The acceptance is unmatched, so no repayment transfer occurs.
-/
theorem unpaid_history_repayment_decision_is_unmatched :
    creditLifecycleActionFrame.enacted .entrepreneur firstRepaymentMoment
        unpaidMaturityHistory = .idle ∧
    creditLifecycleActionFrame.enacted .operator firstRepaymentMoment
        unpaidMaturityHistory = firstRepaymentAccept := by
  decide

/-- The same promised loan terms with maturity set to this branch's endpoint.
The repayment promise remains distinct from the observed lifecycle result. -/
def entrepreneurUnpaidLoanTerms : PawnLoanTerms creditLifecycleActionFrame :=
  { entrepreneurLoanTerms with maturity := unpaidMaturityMoment }

/-- The operator's actual first advance remains purposeful on the unpaid
branch because purposefulness is invariant across histories through a shared
decision with the same enacted action. -/
theorem operator_advance_purposeful_on_unpaid_history :
    LifecyclePurposefulAct .operator firstAdvanceMoment unpaidMaturityHistory
      firstAdvanceOffer := by
  have hmain : creditLifecycleActionFrame.mem_hist firstAdvanceMoment mainHistory := by
    change lifecycleMemHist firstAdvanceMoment mainHistory
    decide
  have hunpaid : creditLifecycleActionFrame.mem_hist firstAdvanceMoment
      unpaidMaturityHistory := by
    change lifecycleMemHist firstAdvanceMoment unpaidMaturityHistory
    decide
  have hsame : creditLifecycleActionFrame.enacted .operator firstAdvanceMoment
      mainHistory = creditLifecycleActionFrame.enacted .operator firstAdvanceMoment
        unpaidMaturityHistory := by decide
  exact (@PurposefulAct.bundle_invariant creditLifecycleActionFrame .operator
    firstAdvanceMoment mainHistory unpaidMaturityHistory firstAdvanceOffer
    hmain hunpaid hsame).mp
      operator_advance_purposeful

/-- The entrepreneur's acceptance remains purposeful on the same history by
the shared-menu, shared-preference, and shared-end laws. -/
theorem entrepreneur_accept_purposeful_on_unpaid_history :
    LifecyclePurposefulAct .entrepreneur firstAdvanceMoment unpaidMaturityHistory
      firstAdvanceAccept := by
  have hmain : creditLifecycleActionFrame.mem_hist firstAdvanceMoment mainHistory := by
    change lifecycleMemHist firstAdvanceMoment mainHistory
    decide
  have hunpaid : creditLifecycleActionFrame.mem_hist firstAdvanceMoment
      unpaidMaturityHistory := by
    change lifecycleMemHist firstAdvanceMoment unpaidMaturityHistory
    decide
  have hsame : creditLifecycleActionFrame.enacted .entrepreneur firstAdvanceMoment
      mainHistory = creditLifecycleActionFrame.enacted .entrepreneur firstAdvanceMoment
        unpaidMaturityHistory := by decide
  exact (@PurposefulAct.bundle_invariant creditLifecycleActionFrame .entrepreneur
    firstAdvanceMoment mainHistory unpaidMaturityHistory firstAdvanceAccept
    hmain hunpaid hsame).mp
      entrepreneur_accept_purposeful

/-- The advance on this branch is the same purposeful bilateral exchange used
by the general credit contract. -/
theorem entrepreneur_unpaid_advance_is_bilateral_exchange :
    @BilateralExchange creditLifecycleActionFrame .operator .entrepreneur
      firstAdvanceMoment unpaidMaturityHistory 1 creditLifecycleMoney 1
      creditLifecycleCollateral := by
  exact ricardian_bilateral_exchange_purposeful WorkshopAgent.operator
    WorkshopAgent.entrepreneur firstAdvanceMoment unpaidMaturityHistory
    creditLifecycleMoney creditLifecycleCollateral 1 1 (by decide) (by decide)
    operator_advance_purposeful_on_unpaid_history (by decide)
    entrepreneur_accept_purposeful_on_unpaid_history (by decide)

/-- A matched purposeful advance on the no-repayment branch. -/
def entrepreneurUnpaidAdvance : CreditAdvance entrepreneurUnpaidLoanTerms where
  history := unpaidMaturityHistory
  moment := firstAdvanceMoment
  nextMoment := secondAdvanceMoment
  successor := by
    change IsNextMoment lifecyclePrecedence lifecycleMemHist
      firstAdvanceMoment secondAdvanceMoment unpaidMaturityHistory
    exact lifecycleNextMoment_is_next firstAdvanceMoment unpaidMaturityHistory
      (by decide) (by decide)
  advanceBeforeMaturity := by
    change lifecyclePrecedence secondAdvanceMoment unpaidMaturityMoment
    decide
  maturityOnHistory := by
    change lifecycleMemHist unpaidMaturityMoment unpaidMaturityHistory
    decide
  purposefulExchange := entrepreneur_unpaid_advance_is_bilateral_exchange

/-- The lender's inventory run from settlement to maturity records a matched
second advance, idle production, and the unmatched repayment acceptance. No
collateral is spent; the second advance supplies one additional collateral
unit to the lender. -/
def entrepreneurUnpaidCollateralCustody :
    CollateralCustodyTrace entrepreneurUnpaidAdvance where
  run := by
    have hadvance : IsNextMoment creditLifecycleActionFrame.Precedence
        creditLifecycleActionFrame.mem_hist secondAdvanceMoment
        (lifecycleNextMoment secondAdvanceMoment unpaidMaturityHistory)
        unpaidMaturityHistory := by
      change IsNextMoment lifecyclePrecedence lifecycleMemHist
        secondAdvanceMoment (lifecycleNextMoment secondAdvanceMoment
          unpaidMaturityHistory) unpaidMaturityHistory
      exact lifecycleNextMoment_is_next secondAdvanceMoment
        unpaidMaturityHistory (by decide) (by decide)
    have hproduction : IsNextMoment creditLifecycleActionFrame.Precedence
        creditLifecycleActionFrame.mem_hist projectCompletionMoment
        (lifecycleNextMoment projectCompletionMoment unpaidMaturityHistory)
        unpaidMaturityHistory := by
      change IsNextMoment lifecyclePrecedence lifecycleMemHist
        projectCompletionMoment (lifecycleNextMoment projectCompletionMoment
          unpaidMaturityHistory) unpaidMaturityHistory
      exact lifecycleNextMoment_is_next projectCompletionMoment
        unpaidMaturityHistory (by decide) (by decide)
    have hrepayment : IsNextMoment creditLifecycleActionFrame.Precedence
        creditLifecycleActionFrame.mem_hist firstRepaymentMoment
        unpaidMaturityMoment unpaidMaturityHistory := by
      change IsNextMoment lifecyclePrecedence lifecycleMemHist
        firstRepaymentMoment (lifecycleNextMoment firstRepaymentMoment
          unpaidMaturityHistory) unpaidMaturityHistory
      have hnext := lifecycleNextMoment_is_next firstRepaymentMoment
        unpaidMaturityHistory (by decide) (by decide)
      simpa [unpaidMaturityMoment, unpaidMaturityHistory,
        historyByIndex, lifecycleLeaf, lifecycleNextMoment,
        firstRepaymentMoment, mainMoment] using hnext
    exact .step
      (.matchedOffer .customer 1 creditLifecycleMoney 1 creditLifecycleCollateral
        (by decide) (by decide) (by decide) hadvance)
      (.step
        (.production creditLifecycleActionFrame.alpha_zero (by decide)
          (@alpha_zero_not_trade creditLifecycleActionFrame) hproduction)
        (.step
          (.unmatchedAccept .entrepreneur 2 creditLifecycleMoney 1
            creditLifecycleCollateral (by decide) (by decide) hrepayment)
          (.done unpaidMaturityMoment)))
  noCollateralUse := by
    decide

/-- This branch reaches unpaid maturity after the repayment decision. Any
purported matched repayment after settlement and before the maturity endpoint
would have to occur at project completion or at the first repayment decision;
the borrower idles at both moments. -/
def entrepreneurUnpaidMaturity : UnpaidMaturity entrepreneurUnpaidAdvance where
  custody := entrepreneurUnpaidCollateralCustody
  noPhysicalRepaymentByMaturity := by
    rintro ⟨R⟩
    have h_on_history :
        creditLifecycleActionFrame.mem_hist R.decisionMoment unpaidMaturityHistory :=
      R.successor.1
    have h_path_cases_raw : R.decisionMoment = (0 : Node) ∨ R.decisionMoment.val = 1 ∨
        R.decisionMoment.val = 2 ∨ R.decisionMoment.val = 3 ∨
        R.decisionMoment.val = 4 ∨ R.decisionMoment = (14 : Node) := by
      change lifecycleMemHist R.decisionMoment unpaidMaturityHistory at h_on_history
      simpa [unpaidMaturityHistory, historyByIndex, lifecycleLeaf,
        lifecycleMemHist, lifecycleAncestor] using h_on_history
    have h_after_advance : MomentAtOrBefore creditLifecycleActionFrame
        secondAdvanceMoment R.decisionMoment := by
      have hAfter := R.afterAdvance
      change MomentAtOrBefore creditLifecycleActionFrame
        entrepreneurUnpaidAdvance.nextMoment R.decisionMoment at hAfter
      simpa [entrepreneurUnpaidAdvance] using hAfter
    have h_after_advance_depth :
        lifecycleDepth secondAdvanceMoment ≤ lifecycleDepth R.decisionMoment := by
      rcases h_after_advance with heq | hprec
      · have hdecision : R.decisionMoment = secondAdvanceMoment := heq.symm
        rw [hdecision]
      · exact (lifecycle_precedence_depth secondAdvanceMoment R.decisionMoment hprec).le
    rcases h_path_cases_raw with h_zero | h_one | h_two | h_completion |
        h_repayment | h_maturity
    · have h_same_moment : R.decisionMoment = (0 : Node) := h_zero
      rw [h_same_moment] at h_after_advance_depth
      norm_num [lifecycleDepth, secondAdvanceMoment, mainMoment] at h_after_advance_depth
    · have h_same_moment : R.decisionMoment = (1 : Node) := Fin.ext h_one
      rw [h_same_moment] at h_after_advance_depth
      norm_num [lifecycleDepth, secondAdvanceMoment, mainMoment] at h_after_advance_depth
    · have h_same_moment : R.decisionMoment = secondAdvanceMoment := by
        apply Fin.ext
        exact h_two
      have hOffer := R.borrowerOfferMatched
      rw [h_same_moment] at hOffer
      change creditLifecycleActionFrame.enacted .entrepreneur secondAdvanceMoment
        unpaidMaturityHistory = creditLifecycleActionFrame.Offer .entrepreneur
          .operator entrepreneurUnpaidLoanTerms.repayment entrepreneurUnpaidLoanTerms.money
          entrepreneurUnpaidLoanTerms.collateralQuantity entrepreneurUnpaidLoanTerms.collateral
        at hOffer
      have h_idle : creditLifecycleActionFrame.enacted .entrepreneur secondAdvanceMoment
          unpaidMaturityHistory = .idle := by decide
      rw [h_idle] at hOffer
      cases hOffer
    · have h_same_moment : R.decisionMoment = (3 : Node) := Fin.ext h_completion
      have hOffer := R.borrowerOfferMatched
      rw [h_same_moment] at hOffer
      change creditLifecycleActionFrame.enacted .entrepreneur (3 : Node)
        unpaidMaturityHistory = creditLifecycleActionFrame.Offer .entrepreneur
          .operator entrepreneurUnpaidLoanTerms.repayment entrepreneurUnpaidLoanTerms.money
          entrepreneurUnpaidLoanTerms.collateralQuantity entrepreneurUnpaidLoanTerms.collateral
        at hOffer
      have h_idle : creditLifecycleActionFrame.enacted .entrepreneur (3 : Node)
          unpaidMaturityHistory = .idle := by decide
      rw [h_idle] at hOffer
      cases hOffer
    · have h_same_moment : R.decisionMoment = (4 : Node) := Fin.ext h_repayment
      have hOffer := R.borrowerOfferMatched
      rw [h_same_moment] at hOffer
      change creditLifecycleActionFrame.enacted .entrepreneur (4 : Node)
        unpaidMaturityHistory = creditLifecycleActionFrame.Offer .entrepreneur
          .operator entrepreneurUnpaidLoanTerms.repayment entrepreneurUnpaidLoanTerms.money
          entrepreneurUnpaidLoanTerms.collateralQuantity entrepreneurUnpaidLoanTerms.collateral
        at hOffer
      change creditLifecycleActionFrame.enacted .entrepreneur firstRepaymentMoment
        unpaidMaturityHistory = creditLifecycleActionFrame.Offer .entrepreneur
          .operator entrepreneurUnpaidLoanTerms.repayment entrepreneurUnpaidLoanTerms.money
          entrepreneurUnpaidLoanTerms.collateralQuantity entrepreneurUnpaidLoanTerms.collateral
        at hOffer
      rw [unpaid_history_repayment_decision_is_unmatched.1] at hOffer
      cases hOffer
    · have h_same_moment : R.decisionMoment = unpaidMaturityMoment := by
        simpa [unpaidMaturityMoment, unpaidMaturityHistory,
          historyByIndex, lifecycleLeaf] using h_maturity
      have hSuccessor := R.successor
      rw [h_same_moment] at hSuccessor
      rcases R.settlesByMaturity with hsettles | hsettles
      · rw [hsettles] at hSuccessor
        exact creditLifecycleActionFrame.moment_lt_irrefl
          unpaidMaturityMoment hSuccessor.2.2.1
      · exact creditLifecycleActionFrame.moment_lt_irrefl unpaidMaturityMoment
          (creditLifecycleActionFrame.moment_lt_trans hSuccessor.2.2.1 hsettles)

/-- The branch's actual result is an outstanding contract reaching unpaid
maturity after the borrower's repayment inaction. The lender's maturity stock
contains at least the collateral quantity received at origination. -/
theorem entrepreneur_unpaid_default_result :
    CreditTransition .outstanding .unpaidMaturity .defaulted ∧
    creditLifecycleActionFrame.omega .operator firstAdvanceMoment
      unpaidMaturityHistory creditLifecycleCollateral + 1 ≤
    creditLifecycleActionFrame.omega .operator unpaidMaturityMoment
      unpaidMaturityHistory creditLifecycleCollateral := by
  refine ⟨entrepreneurUnpaidMaturity.status_transition, ?_⟩
  exact entrepreneurUnpaidMaturity.lender_retains_pledged_collateral

/-- The later matched advance increases the lender's collateral stock by one;
the unmatched repayment acceptance leaves that quantity unchanged through
maturity. This is an aggregate inventory result, not a claim of legal title to
specific fungible units. -/
theorem entrepreneur_unpaid_default_collateral_balance :
    creditLifecycleActionFrame.omega .operator unpaidMaturityMoment
      unpaidMaturityHistory creditLifecycleCollateral =
      creditLifecycleActionFrame.omega .operator secondAdvanceMoment
        unpaidMaturityHistory creditLifecycleCollateral + 1 := by
  calc
    creditLifecycleActionFrame.omega .operator unpaidMaturityMoment
        unpaidMaturityHistory creditLifecycleCollateral =
        creditLifecycleActionFrame.omega .operator secondAdvanceMoment
          unpaidMaturityHistory creditLifecycleCollateral +
            entrepreneurUnpaidCollateralCustody.run.totalYield
              creditLifecycleCollateral :=
      entrepreneurUnpaidCollateralCustody.collateral_retained
    _ = creditLifecycleActionFrame.omega .operator secondAdvanceMoment
        unpaidMaturityHistory creditLifecycleCollateral + 1 := by
      rw [show entrepreneurUnpaidCollateralCustody.run.totalYield
          creditLifecycleCollateral = 1 from by
        decide]

/-- The unpaid branch still supplies an enacted loan quote: origination is
recorded independently of the later unpaid-maturity outcome. -/
def entrepreneurUnpaidEnactedLoanQuote :
    EnactedLoanQuote creditLifecycleActionFrame where
  terms := entrepreneurUnpaidLoanTerms
  advance := entrepreneurUnpaidAdvance

/-- The enacted quote's advance has the existing unpaid-maturity evidence and
therefore no successful repayment certificate. -/
theorem entrepreneur_unpaid_quote_has_no_repayment :
    ¬ Nonempty (CreditRepayment entrepreneurUnpaidEnactedLoanQuote.advance) := by
  exact entrepreneurUnpaidMaturity.noRepaymentByMaturity

end CreditLifecycleTree
end Praxeology

end
