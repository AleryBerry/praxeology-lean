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
refusal of credit avoids default. Idling protects its collateral, whereas accepting
leads to factor squeezing, non-completion, and default foreclosure. -/
theorem fiveProjectCautiousProjectTwoRefusal_avoids_default :
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
refusal of credit avoids default. Idling protects its collateral, whereas accepting
leads to factor squeezing, non-completion, and default foreclosure. -/
theorem fiveProjectCautiousProjectThreeRefusal_avoids_default :
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
/-- The bank's fiduciary note issuance expands advances under the expansion forecast:
issuing two notes expands lending capacity from two to four advances, yielding
higher terminal cash and foreclosed collateral than idling with two reserves. -/
theorem fiveProjectBankNoteIssuance_expands_advances :
    let enacted := fiveProjectNamedProgramRun (fiveProjectRegimeData .fiduciaryExpansion)
    enacted.cursor.actualNotesIssued = 2 ∧
    enacted.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    enacted.state.stock fiveProjectBank fiveProjectMoneyGood = 8 ∧
    enacted.state.stock fiveProjectBank (fiveProjectCollateralGood 2) = 1 ∧
    enacted.state.stock fiveProjectBank (fiveProjectCollateralGood 3) = 1 := by
  decide

/-- The causal conclusions synthesized by the Austrian Business Cycle Theory:
1. Crisis generation: contractual defaults emerge at maturity.
2. Malinvestment bound: completions are strictly bounded by physical factor supply.
3. Advance-completion shortfall: expanded advance count strictly exceeds factor-conserved
   completion count (2 < 4).
4. Stranded capital difference: stranded projects [2, 3] are the exact difference between
   funded advances [0, 1, 2, 3] and completed projects [0, 1].
5. Cautious refusal default avoidance: cautious refusal avoids defaults ([]) while optimistic
   entry suffers defaults ([2], [3]).
6. Ex-post regret: marginal borrowers regret credit entry.
7. Purposefulness: all actions (saving, borrowing) were ex-ante purposeful under subjective
   appraisal. -/
structure FiveProjectConclusion where
  cycle_generated :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualDefaults.map
        LoanReservationBid.borrower = [2, 3]
  malinvestment_proved :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.length ≤ 2
  expansion_exceeds_conservation :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.length <
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualAdvances.length
  stranded_projects_exact_difference :
    (fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualDefaults.map
        LoanReservationBid.borrower =
      ((fiveProjectNamedProgramRun
        (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualAdvances.map
          LoanReservationBid.borrower).diff
      ((fiveProjectNamedProgramRun
        (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.map
          LoanReservationBid.borrower)
  cautious_avoids_default :
    fiveProjectCautiousFiduciaryRun.cursor.actualDefaults = [] ∧
    fiveProjectCautiousProjectTwoEntryRun.cursor.actualDefaults.map
      LoanReservationBid.borrower = [2] ∧
    fiveProjectCautiousProjectThreeEntryRun.cursor.actualDefaults.map
      LoanReservationBid.borrower = [3]
  regret_established :
    fiveProjectProjectTwoEntryRegret ∧ fiveProjectProjectThreeEntryRegret
  purposefulness_unified :
    (@PurposefulAct fiveProjectHouseholdSavingActionFrame fiveProjectHousehold
      FiniteEconomyProgram.ProgramMoment.root fiveProjectHouseholdSavingSuffix.selectedHistory
      fiveProjectHouseholdSavingAction) ∧
    fiveProjectProjectTwoPurposefulAcceptance ∧
    fiveProjectProjectThreePurposefulAcceptance

set_option maxRecDepth 4096 in
/-- The named fiduciary-expansion scenario's full behavioral synthesis. The
physical calculations derive the quote, real-input shortage, completions,
repayments, and defaults. The separately proved scenario comparisons derive
purposefulness; the two replay comparisons derive regret. It composes the
executable run and behavioral results directly, without an intermediate
evidence record. -/
theorem fiveProject_fiduciary_causal_cycle_master :
    FiveProjectConclusion := by
  have h_credit_expansion :
      (fiveProjectNamedProgramRun
        (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualAdvances.map
          LoanReservationBid.borrower = [0, 1, 2, 3] := by
    decide
  have h_production_malinvestment :
      (fiveProjectNamedProgramRun
        (fiveProjectRegimeData .fiduciaryExpansion)).cursor.completedProjects.map
          LoanReservationBid.borrower = [0, 1] := by
    decide
  have h_defaults :
      (fiveProjectNamedProgramRun
        (fiveProjectRegimeData .fiduciaryExpansion)).cursor.actualDefaults.map
          LoanReservationBid.borrower = [2, 3] := by
    decide
  have h_cautious_replay : fiveProjectCautiousReplayMatches := by
    unfold fiveProjectCautiousReplayMatches
    decide
  exact {
    cycle_generated := h_defaults
    malinvestment_proved := by
      have hlen := congrArg List.length h_production_malinvestment
      simp only [List.length_map] at hlen
      rw [hlen]
      decide
    expansion_exceeds_conservation := by
      have hlen_comp := congrArg List.length h_production_malinvestment
      have hlen_adv := congrArg List.length h_credit_expansion
      simp only [List.length_map] at hlen_comp hlen_adv
      rw [hlen_comp, hlen_adv]
      decide
    stranded_projects_exact_difference := by
      rw [h_credit_expansion, h_production_malinvestment, h_defaults]
      decide
    cautious_avoids_default := ⟨rfl, h_cautious_replay.1, h_cautious_replay.2⟩
    regret_established := ⟨fiveProjectProjectTwoAcceptance_hasContextMatchedRegret,
      fiveProjectProjectThreeAcceptance_hasContextMatchedRegret⟩
    purposefulness_unified :=
      ⟨fiveProjectHouseholdSavingAction_purposeful,
        fiveProjectProjectTwoAcceptanceAction_purposeful,
        fiveProjectProjectThreeAcceptanceAction_purposeful⟩ }

end Praxeology

end
