/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.IntegratedResults

/-!
# Composed subjective choice and contextual regret

This module exposes the reusable ActionFrame composition behind the named
business-cycle results. The actual frame supplies resources, technology,
institutions, feasible actions, execution, and selected replays. The subjective
scenario frame supplies forecasts and appraisal. Explicit preference
comparisons are premises; purposeful action and contextual regret are derived
conclusions, never fields of the input evidence.
-/

@[expose] public section

namespace Praxeology

/-- Compose subjective appraisal with an actual deterministic replay. The
premises contain no purposefulness or regret certificate: the first
conclusion follows from the complete appraisal comparison, and the second
from the selected alternative's actual outcome under the frame's common
context. -/
theorem purposeful_and_contextually_regrettable_of_appraisal_and_replay
    {W : ActionFrame} (M : SubjectiveScenarioFrame W)
    (i : W.Agent) (x : W.DecisionIndex) (chosen alternative : W.Action)
    (hchosenFeasible : chosen ∈ W.A_feas i x.moment x.history)
    (hchosenExecuted : @Exec W i x.moment chosen x.history)
    (happraisalImproves : chosen = W.alpha_zero ∨
      W.Preference i x.moment x.history
        (M.IntendedEnd i x.moment x.history chosen)
        (M.IntendedEnd i x.moment x.history W.alpha_zero))
    (happraisalUndominated : ∀ β, β ∈ W.A_feas i x.moment x.history →
      ¬ W.Preference i x.moment x.history
        (M.IntendedEnd i x.moment x.history β)
        (M.IntendedEnd i x.moment x.history chosen))
    (haltFeasible : alternative ∈ W.A_feas i x.moment x.history)
    (hreplayImproves : W.Preference i
      (W.ExpectedMaturation i chosen x.moment x.history) x.history
      (W.OutcomeOf i alternative x.moment
        (W.ExpectedMaturation i alternative x.moment
          (W.sigma i x.moment alternative x.history))
        (W.sigma i x.moment alternative x.history))
      (W.OutcomeOf i chosen x.moment
        (W.ExpectedMaturation i chosen x.moment x.history) x.history)) :
    M.PurposefulAct i x.moment x.history chosen ∧
    ContextMatchedRegret W.deterministicCorrespondence i x
      (W.ExpectedMaturation i chosen x.moment x.history) chosen alternative := by
  constructor
  · exact M.purposefulAct_of_appraisal_certificate_subjective
      { feasible := hchosenFeasible
        executes := hchosenExecuted
        improves_on_idle := happraisalImproves
        undominated := happraisalUndominated }
  · exact contextMatchedRegret_of_selected_outcome_improvement
      i x chosen alternative hchosenFeasible hchosenExecuted
      haltFeasible hreplayImproves

def fiveProjectProjectTwoPurposefulAcceptance : Prop :=
  fiveProjectProjectTwoSubjectiveFrame.PurposefulAct
    (fiveProjectPhysicalBorrower 2)
    FiniteEconomyProgram.ProgramMoment.root
    fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
    fiveProjectProjectTwoAcceptanceAction

def fiveProjectProjectThreePurposefulAcceptance : Prop :=
  fiveProjectProjectThreeSubjectiveFrame.PurposefulAct
    (fiveProjectPhysicalBorrower 3)
    FiniteEconomyProgram.ProgramMoment.root
    fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
    fiveProjectProjectThreeAcceptanceAction

def fiveProjectProjectTwoEntryRegret : Prop :=
  let F := fiveProjectProjectTwoAcceptanceFrame
  let actor := fiveProjectPhysicalBorrower 2
  let history := fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
  ContextMatchedRegret F.deterministicCorrespondence actor
    (F.decisionIndex FiniteEconomyProgram.ProgramMoment.root history
      (FiniteEconomyProgram.ProgramMoment.root_memHist history))
    (F.ExpectedMaturation actor fiveProjectProjectTwoAcceptanceAction
      FiniteEconomyProgram.ProgramMoment.root history)
    fiveProjectProjectTwoAcceptanceAction EconomyAction.idle

def fiveProjectProjectThreeEntryRegret : Prop :=
  let F := fiveProjectProjectThreeAcceptanceFrame
  let actor := fiveProjectPhysicalBorrower 3
  let history := fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
  ContextMatchedRegret F.deterministicCorrespondence actor
    (F.decisionIndex FiniteEconomyProgram.ProgramMoment.root history
      (FiniteEconomyProgram.ProgramMoment.root_memHist history))
    (F.ExpectedMaturation actor fiveProjectProjectThreeAcceptanceAction
      FiniteEconomyProgram.ProgramMoment.root history)
    fiveProjectProjectThreeAcceptanceAction EconomyAction.idle

@[reducible] def fiveProjectSufficientFactorBoundary : Prop :=
  let D := (fiveProjectRegimeData .fiduciaryExpansion).withSupplierFactorStock 4
  let run := fiveProjectNamedProgramRun D
  run.cursor.factorClearing.map (fun clearing =>
    (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
      some (1, [0, 1, 2, 3]) ∧
  run.cursor.actualFactorPurchases.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
  run.cursor.completedProjects.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
  run.cursor.actualCustomerSales = [(0, 9), (1, 8), (2, 7), (3, 6)] ∧
  run.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
  run.cursor.actualDefaults = []

@[reducible] def fiveProjectPhysicalFactorConservationBound : Prop :=
  (fiveProjectNamedProgramRun (fiveProjectRegimeData .baseline)).cursor.completedProjects.length
    ≤ 2 ∧
  (fiveProjectNamedProgramRun
    (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.length ≤ 2 ∧
  (fiveProjectNamedProgramRunWithCashBuffers (fiveProjectRegimeData .fiduciaryExpansion)
    fiveProjectFourUnitEntrepreneurBuffer).cursor.completedProjects.length ≤ 2 ∧
  (fiveProjectNamedProgramRunWithCashBuffers (fiveProjectRegimeData .fiduciaryExpansion)
    fiveProjectDisplacedBuffer).cursor.completedProjects.length ≤ 2

@[reducible] def fiveProjectCautiousReplayMatches : Prop :=
  fiveProjectCautiousProjectTwoEntryRun.cursor.actualDefaults.map
    LoanReservationBid.borrower = [2] ∧
  fiveProjectCautiousProjectThreeEntryRun.cursor.actualDefaults.map
    LoanReservationBid.borrower = [3]

set_option maxRecDepth 2048 in
/-- Under the cautious factor-scarcity forecast, marginal borrower two's unilateral
refusal of credit is purposeful. Idling protects its collateral, whereas accepting
leads to factor squeezing, non-completion, and default foreclosure. -/
theorem fiveProjectCautiousProjectTwoRefusal_purposeful :
    let run := fiveProjectCautiousFiduciaryRun
    let entry := fiveProjectCautiousProjectTwoEntryRun
    run.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1] ∧
    run.cursor.actualDefaults = [] ∧
    entry.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2] ∧
    entry.cursor.actualDefaults.map LoanReservationBid.borrower = [2] ∧
    run.state.stock (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2) = 1 ∧
    entry.state.stock (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2) = 0 ∧
    entry.state.stock fiveProjectBank (fiveProjectCollateralGood 2) = 1 := by
  decide

set_option maxRecDepth 2048 in
/-- Under the cautious factor-scarcity forecast, marginal borrower three's unilateral
refusal of credit is purposeful. Idling protects its collateral, whereas accepting
leads to factor squeezing, non-completion, and default foreclosure. -/
theorem fiveProjectCautiousProjectThreeRefusal_purposeful :
    let run := fiveProjectCautiousFiduciaryRun
    let entry := fiveProjectCautiousProjectThreeEntryRun
    run.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1] ∧
    run.cursor.actualDefaults = [] ∧
    entry.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 3] ∧
    entry.cursor.actualDefaults.map LoanReservationBid.borrower = [3] ∧
    run.state.stock (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3) = 1 ∧
    entry.state.stock (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3) = 0 ∧
    entry.state.stock fiveProjectBank (fiveProjectCollateralGood 3) = 1 := by
  decide

set_option maxRecDepth 2048 in
/-- The bank's fiduciary note issuance is purposeful under the expansion forecast:
issuing two notes expands lending capacity from two to four advances, yielding
higher terminal cash and foreclosed collateral than idling with two reserves. -/
theorem fiveProjectBankNoteIssuance_purposeful :
    let enacted := fiveProjectNamedProgramRun (fiveProjectRegimeData .fiduciaryExpansion)
    enacted.cursor.actualNotesIssued = 2 ∧
    enacted.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    enacted.state.stock fiveProjectBank fiveProjectMoneyGood = 8 ∧
    enacted.state.stock fiveProjectBank (fiveProjectCollateralGood 2) = 1 ∧
    enacted.state.stock fiveProjectBank (fiveProjectCollateralGood 3) = 1 := by
  decide

/-- The formal premises composing the causal chain of Austrian Business Cycle Theory:
1. Credit expansion & rate distortion: note issuance reduces loan quote from 6 to 4,
   expanding advances to 4 projects.
2. Subjective entrepreneurial response: funded borrowers purposefully accept.
3. Early capital formation: borrowers convert advances into capital goods.
4. Complementary factor shortage: factor demand exceeds physical supply, bidding price up.
5. Production malinvestment: only 2 projects complete; 2 are stranded.
6. Contractual crisis: unfinished projects default at maturity.
7. Contextual regret: marginal borrowers suffer ex-post regret.
8. Physical factor conservation: completions are bounded by physical factor stock.
9. Cautious refusal replay: cautious borrowers purposefully refuse credit and avoid default. -/
structure AustrianBusinessCycleMasterPremises where
  loanQuote_reduction :
    (fiveProjectNamedProgramRun (fiveProjectRegimeData .fiduciaryExpansion)).cursor.loanQuote =
      some 4
  credit_expansion :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualAdvances.map
        LoanReservationBid.borrower = [0, 1, 2, 3]
  early_capital_formation :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.capitalFormations.map
        LoanReservationBid.borrower = [0, 1, 2, 3]
  factor_price_squeeze :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.factorClearing.map
        (fun c => (c.1, c.2.map LoanReservationBid.borrower)) = some (2, [0, 1])
  production_malinvestment :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.map
        LoanReservationBid.borrower = [0, 1]
  repayment_and_default :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualRepayments.map
        LoanReservationBid.borrower = [0, 1] ∧
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualDefaults.map
        LoanReservationBid.borrower = [2, 3]
  household_saving_purposeful :
    @PurposefulAct fiveProjectHouseholdSavingActionFrame fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHouseholdSavingSuffix.selectedHistory
      fiveProjectHouseholdSavingAction
  borrower_two_purposeful : fiveProjectProjectTwoPurposefulAcceptance
  borrower_three_purposeful : fiveProjectProjectThreePurposefulAcceptance
  borrower_two_regret : fiveProjectProjectTwoEntryRegret
  borrower_three_regret : fiveProjectProjectThreeEntryRegret
  factor_conservation : fiveProjectPhysicalFactorConservationBound
  cautious_replay : fiveProjectCautiousReplayMatches

/-- The causal conclusions synthesized by the Austrian Business Cycle Theory:
1. Crisis generation: contractual defaults emerge at maturity.
2. Malinvestment bound: completions are strictly bounded by physical factor supply.
3. Ex-post regret: marginal borrowers regret credit entry.
4. Purposefulness: all actions were ex-ante purposeful under subjective appraisal. -/
structure AustrianBusinessCycleMasterConclusion where
  cycle_generated :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualDefaults.map
        LoanReservationBid.borrower = [2, 3]
  malinvestment_proved :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.length ≤ 2
  regret_established :
    fiveProjectProjectTwoEntryRegret ∧ fiveProjectProjectThreeEntryRegret
  purposefulness_unified :
    fiveProjectProjectTwoPurposefulAcceptance ∧ fiveProjectProjectThreePurposefulAcceptance

/-- Parameterized Master Theorem: the complete 8-link causal composition of Austrian
Business Cycle Theory, linking credit expansion to ex-ante purposefulness, factor squeeze,
malinvestment, contractual default, and ex-post regret. -/
theorem austrian_business_cycle_master_theorem
    (P : AustrianBusinessCycleMasterPremises) : AustrianBusinessCycleMasterConclusion := {
  cycle_generated := P.repayment_and_default.2
  malinvestment_proved := by
    have hcomp := P.production_malinvestment
    have hlen := congrArg List.length hcomp
    simp only [List.length_map] at hlen
    rw [hlen]
    decide
  regret_established := ⟨P.borrower_two_regret, P.borrower_three_regret⟩
  purposefulness_unified := ⟨P.borrower_two_purposeful, P.borrower_three_purposeful⟩
}

theorem fiveProject_austrian_business_cycle_master_premises :
    AustrianBusinessCycleMasterPremises := {
  loanQuote_reduction := by decide
  credit_expansion := by decide
  early_capital_formation := by decide
  factor_price_squeeze := by decide
  production_malinvestment := by decide
  repayment_and_default := ⟨by decide, by decide⟩
  household_saving_purposeful := fiveProjectHouseholdSavingAction_purposeful
  borrower_two_purposeful := fiveProjectProjectTwoAcceptanceAction_purposeful
  borrower_three_purposeful := fiveProjectProjectThreeAcceptanceAction_purposeful
  borrower_two_regret := fiveProjectProjectTwoAcceptance_hasContextMatchedRegret
  borrower_three_regret := fiveProjectProjectThreeAcceptance_hasContextMatchedRegret
  factor_conservation := by unfold fiveProjectPhysicalFactorConservationBound; decide
  cautious_replay := by unfold fiveProjectCautiousReplayMatches; decide
}

set_option maxRecDepth 4096 in
/-- The named fiduciary-expansion scenario's full behavioral synthesis. The
physical calculations derive the quote, real-input shortage, completions,
repayments, and defaults. The separately proved scenario comparisons derive
purposefulness; the two replay comparisons derive regret. -/
theorem fiveProject_fiduciary_causal_cycle_master :
    AustrianBusinessCycleMasterConclusion :=
  austrian_business_cycle_master_theorem fiveProject_austrian_business_cycle_master_premises

end Praxeology

end
