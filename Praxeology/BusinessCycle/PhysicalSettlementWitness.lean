/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.CreditLifecycleFrame

/-!
# Physical repayment without behavioral evidence

The lifecycle's enacted offers and acceptances construct a physical repayment
record directly. Its contractual effect and transfer accounting do not use the
parties' purposeful-action proofs.
-/

@[expose] public section

namespace Praxeology
namespace CreditLifecycleTree

local instance physicalSettlementActionFrame : ActionFrame := creditLifecycleActionFrame

/-- Matched advance actions on the main lifecycle history, without a
purposefulness certificate. -/
def entrepreneurPhysicalAdvance : AdvanceExecution
    (T := entrepreneurLoanTerms) where
  history := mainHistory
  decisionMoment := firstAdvanceMoment
  settlementMoment := secondAdvanceMoment
  successor := by
    change IsNextMoment lifecyclePrecedence lifecycleMemHist
      firstAdvanceMoment secondAdvanceMoment mainHistory
    exact lifecycleNextMoment_is_next firstAdvanceMoment mainHistory (by decide) (by decide)
  settlesByMaturity := by
    right
    change lifecyclePrecedence secondAdvanceMoment maturityMoment
    decide
  maturityOnHistory := by
    change lifecycleMemHist maturityMoment mainHistory
    decide
  lenderOfferMatched := by
    change lifecycleEnacted .operator firstAdvanceMoment mainHistory = firstAdvanceOffer
    decide
  borrowerAcceptanceMatched := by
    change lifecycleEnacted .entrepreneur firstAdvanceMoment mainHistory = firstAdvanceAccept
    decide

/-- Matched repayment actions on the main lifecycle history, without a
purposefulness certificate. -/
def entrepreneurPhysicalRepayment : RepaymentExecution
    (T := entrepreneurLoanTerms) (A := entrepreneurPhysicalAdvance) where
  decisionMoment := firstRepaymentMoment
  settlementMoment := secondRepaymentMoment
  successor := by
    change IsNextMoment lifecyclePrecedence lifecycleMemHist
      firstRepaymentMoment secondRepaymentMoment mainHistory
    exact lifecycleNextMoment_is_next firstRepaymentMoment mainHistory (by decide) (by decide)
  afterAdvance := by
    right
    change lifecyclePrecedence secondAdvanceMoment firstRepaymentMoment
    decide
  settlesByMaturity := by
    right
    change lifecyclePrecedence secondRepaymentMoment maturityMoment
    decide
  borrowerOfferMatched := by
    change lifecycleEnacted .entrepreneur firstRepaymentMoment mainHistory = firstRepaymentOffer
    decide
  lenderAcceptanceMatched := by
    change lifecycleEnacted .operator firstRepaymentMoment mainHistory = firstRepaymentAccept
    decide

/-- A physically matched repayment clears the obligation without requiring a
`CreditRepayment` behavioral certificate. -/
theorem entrepreneur_physical_repayment_clears_obligation :
    CreditTransition .outstanding .repayment .repaid :=
  RepaymentExecution.clears_obligation entrepreneurPhysicalRepayment

/-- The actual matched payment transfers the promised money to the lender and
returns the collateral to the borrower. -/
theorem entrepreneur_physical_repayment_transfer :
    creditLifecycleActionFrame.omega .entrepreneur secondRepaymentMoment mainHistory
        creditLifecycleMoney + entrepreneurLoanTerms.repayment =
      creditLifecycleActionFrame.omega .entrepreneur firstRepaymentMoment mainHistory
        creditLifecycleMoney ∧
    creditLifecycleActionFrame.omega .operator secondRepaymentMoment mainHistory
        creditLifecycleMoney =
      creditLifecycleActionFrame.omega .operator firstRepaymentMoment mainHistory
        creditLifecycleMoney + entrepreneurLoanTerms.repayment ∧
    creditLifecycleActionFrame.omega .entrepreneur secondRepaymentMoment mainHistory
        creditLifecycleCollateral =
      creditLifecycleActionFrame.omega .entrepreneur firstRepaymentMoment mainHistory
        creditLifecycleCollateral + entrepreneurLoanTerms.collateralQuantity ∧
    creditLifecycleActionFrame.omega .operator secondRepaymentMoment mainHistory
        creditLifecycleCollateral + entrepreneurLoanTerms.collateralQuantity =
      creditLifecycleActionFrame.omega .operator firstRepaymentMoment mainHistory
        creditLifecycleCollateral :=
  RepaymentExecution.physical_transfer entrepreneurPhysicalRepayment

end CreditLifecycleTree

/-- Settlement at the maturity node is within the reflexive deadline closure.
-/
theorem settlement_at_maturity_is_on_time {W : ActionFrame} (t : W.Moment) :
    MomentAtOrBefore W t t := Or.inl rfl

/-- Settlement strictly after maturity is outside the deadline, including when
the repayment decision itself begins at maturity. -/
theorem settlement_after_maturity_is_late {W : ActionFrame}
    {maturity settlement : W.Moment} (h : W.Precedence maturity settlement) :
    ¬ MomentAtOrBefore W settlement maturity := by
  intro hdeadline
  rcases hdeadline with heq | hbefore
  · subst settlement
    exact W.moment_lt_irrefl maturity h
  · exact W.moment_lt_irrefl maturity (W.moment_lt_trans h hbefore)

end Praxeology

end
