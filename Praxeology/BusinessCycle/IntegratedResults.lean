/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.BehavioralChoices

/-!
# Integrated behavioral and regret results

This module connects the five-project physical replays to the existing
ActionFrame choice and context-matched regret interfaces.
-/

@[expose] public section

namespace Praxeology

def fiveProjectProjectThreeAcceptanceSuffix :=
  fiveProjectFiduciaryAcceptanceSuffix 3

def fiveProjectProjectThreeAcceptanceAction :
    EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  .accept (fiveProjectPhysicalBorrower 3) fiveProjectBank
    fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
    (fiveProjectCollateralGood 3)

@[instance_reducible] noncomputable def fiveProjectProjectThreeAcceptanceFrame :
    ActionFrame :=
  fiveProjectPhysicalSuffixActionFrame fiveProjectProjectThreeAcceptanceSuffix 3

structure FiveProjectProjectThreeLoanObservation where
  borrowerMoney : ℕ
  borrowerCollateral : ℕ
  publishedRepayment : Option ℕ
  deriving DecidableEq, Repr

def fiveProjectProjectThreeLoanObservationAt
    (moment : fiveProjectProjectThreeAcceptanceSuffix.program.Moment) :
    FiveProjectProjectThreeLoanObservation :=
  { borrowerMoney := moment.currentState.stock
      (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood
    borrowerCollateral := moment.currentState.stock
      (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3)
    publishedRepayment := some 4 }

/-- The project-three forecast preserves the borrower's observed local cash,
collateral, and actual published loan quote at the acceptance node. The
four-factor scenario changes the unobserved aggregate household resources. -/
theorem fiveProjectProjectThreeForecast_preserves_observed_local_data :
    (fiveProjectFiduciaryAcceptancePrefix 3).state.stock
        (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood =
      (fiveProjectFourFactorForecastAcceptancePrefix 3).state.stock
        (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood ∧
    (fiveProjectFiduciaryAcceptancePrefix 3).state.stock
        (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3) =
      (fiveProjectFourFactorForecastAcceptancePrefix 3).state.stock
        (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3) ∧
    (fiveProjectFiduciaryAcceptancePrefix 3).cursor.loanQuote =
      (fiveProjectFourFactorForecastAcceptancePrefix 3).cursor.loanQuote ∧
    (fiveProjectFiduciaryAcceptancePrefix 3).cursor.loanQuote = some 4 ∧
    (fiveProjectFourFactorForecastAcceptancePrefix 3).cursor.loanQuote = some 4 := by
  decide

structure FiveProjectProjectThreeForecastScenario where
  moment : fiveProjectProjectThreeAcceptanceSuffix.program.Moment
  history : fiveProjectProjectThreeAcceptanceSuffix.program.History
  incident : fiveProjectProjectThreeAcceptanceFrame.mem_hist moment history
  observation : FiveProjectProjectThreeLoanObservation
  fourFactorForecast : Bool

noncomputable def fiveProjectProjectThreeScenarioMenu
    (actor : FiveProjectPhysicalAgent)
    (scenario : FiveProjectProjectThreeForecastScenario) :
    Finset (EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) :=
  fiveProjectProjectThreeAcceptanceFrame.A_feas actor scenario.moment scenario.history

noncomputable def fiveProjectProjectThreeScenarioEnd (actor : FiveProjectPhysicalAgent)
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation)
    (scenario : FiveProjectProjectThreeForecastScenario) :
    fiveProjectProjectThreeAcceptanceFrame.Ends := by
  if hforecast : scenario.fourFactorForecast ∧
      actor = fiveProjectPhysicalBorrower 3 then
    if haccept : action = fiveProjectProjectThreeAcceptanceAction then
      exact .bundle (fiveProjectFourFactorForecastRun.state.stock actor)
    else if hidle : action = EconomyAction.idle then
      exact .bundle ((fiveProjectFourFactorForecastDeclineRun 3).state.stock actor)
    else
      exact fiveProjectProjectThreeAcceptanceFrame.End_of actor action
        scenario.moment scenario.history
  else
    exact fiveProjectProjectThreeAcceptanceFrame.End_of actor action
      scenario.moment scenario.history

noncomputable def fiveProjectProjectThreeForecastScenarioAt
    (actor : FiveProjectPhysicalAgent)
    (moment : fiveProjectProjectThreeAcceptanceSuffix.program.Moment)
    (observation : FiveProjectProjectThreeLoanObservation) :
    FiveProjectProjectThreeForecastScenario :=
  { moment := moment
    history := fiveProjectPhysicalSuffixReferenceHistory
      fiveProjectProjectThreeAcceptanceSuffix actor moment
    incident := fiveProjectPhysicalSuffixReferenceHistory_mem
      fiveProjectProjectThreeAcceptanceSuffix actor moment
    observation := observation
    fourFactorForecast := decide
      (actor = fiveProjectPhysicalBorrower 3 ∧
        moment = FiniteEconomyProgram.ProgramMoment.root) }

noncomputable def fiveProjectProjectThreeActualScenario
    (actor : FiveProjectPhysicalAgent)
    (moment : fiveProjectProjectThreeAcceptanceSuffix.program.Moment)
    (history : fiveProjectProjectThreeAcceptanceSuffix.program.History) :
    FiveProjectProjectThreeForecastScenario := by
  classical
  exact if hmem : fiveProjectProjectThreeAcceptanceFrame.mem_hist moment history then
    { moment := moment
      history := history
      incident := hmem
      observation := fiveProjectProjectThreeLoanObservationAt moment
      fourFactorForecast := false }
  else
    { moment := moment
      history := fiveProjectPhysicalSuffixReferenceHistory
        fiveProjectProjectThreeAcceptanceSuffix actor moment
      incident := fiveProjectPhysicalSuffixReferenceHistory_mem
        fiveProjectProjectThreeAcceptanceSuffix actor moment
      observation := fiveProjectProjectThreeLoanObservationAt moment
      fourFactorForecast := false }

noncomputable def fiveProjectProjectThreeForecastEconomy :
    SingletonForecastEconomy fiveProjectProjectThreeAcceptanceFrame where
  Scenario := FiveProjectProjectThreeForecastScenario
  Observation := FiveProjectProjectThreeLoanObservation
  scenarioAnchor := FiveProjectProjectThreeForecastScenario.moment
  scenarioMenu := fiveProjectProjectThreeScenarioMenu
  scenarioEnd := fiveProjectProjectThreeScenarioEnd
  observeActual _ moment _ := fiveProjectProjectThreeLoanObservationAt moment
  observeScenario _ scenario := scenario.observation
  forecastScenario := fiveProjectProjectThreeForecastScenarioAt
  forecast_anchored _ _ _ := rfl
  forecast_matches_observation _ _ _ := rfl
  forecast_menu_covers actor moment history hmem := by
    let forecast := fiveProjectProjectThreeForecastScenarioAt actor moment
      (fiveProjectProjectThreeLoanObservationAt moment)
    have hmenu := fiveProjectProjectThreeAcceptanceFrame.A_feas_bundle_invariant
      actor moment hmem forecast.incident
    change fiveProjectProjectThreeAcceptanceFrame.A_feas actor moment history ⊆
      fiveProjectProjectThreeAcceptanceFrame.A_feas actor forecast.moment forecast.history
    rw [hmenu]
    exact Finset.Subset.rfl
  observation_shared_at_decision _ _ _ _ _ _ := rfl
  actualScenario := fiveProjectProjectThreeActualScenario
  actual_scenario_anchored _ moment history hmem := by
    simp [fiveProjectProjectThreeActualScenario, hmem]
  actual_scenario_observation _ moment history hmem := by
    simp [fiveProjectProjectThreeActualScenario, hmem]
  actual_scenario_end _ moment history action hmem := by
    simp [fiveProjectProjectThreeScenarioEnd,
      fiveProjectProjectThreeActualScenario, hmem]

noncomputable def fiveProjectProjectThreeSubjectiveFrame :
    SubjectiveScenarioFrame fiveProjectProjectThreeAcceptanceFrame :=
  singletonForecastScenarioFrame fiveProjectProjectThreeForecastEconomy

theorem fiveProjectProjectThreeForecast_accept_end :
    fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
      (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      fiveProjectProjectThreeAcceptanceAction =
    .bundle (fiveProjectFourFactorForecastRun.state.stock
      (fiveProjectPhysicalBorrower 3)) := by
  simp [SubjectiveScenarioFrame.IntendedEnd,
    fiveProjectProjectThreeSubjectiveFrame,
    singletonForecastScenarioFrame,
    fiveProjectProjectThreeForecastEconomy,
    fiveProjectProjectThreeForecastScenarioAt,
    fiveProjectProjectThreeScenarioEnd,
    fiveProjectProjectThreeLoanObservationAt,
    fiveProjectProjectThreeAcceptanceAction]

theorem fiveProjectProjectThreeForecast_idle_end :
    fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
      (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory EconomyAction.idle =
    .bundle ((fiveProjectFourFactorForecastDeclineRun 3).state.stock
      (fiveProjectPhysicalBorrower 3)) := by
  simp [SubjectiveScenarioFrame.IntendedEnd,
    fiveProjectProjectThreeSubjectiveFrame,
    singletonForecastScenarioFrame,
    fiveProjectProjectThreeForecastEconomy,
    fiveProjectProjectThreeForecastScenarioAt,
    fiveProjectProjectThreeScenarioEnd,
    fiveProjectProjectThreeLoanObservationAt,
    fiveProjectProjectThreeAcceptanceAction]

set_option maxRecDepth 16384 in
theorem fiveProjectProjectThreeForecast_accept_improves_on_idle :
    fiveProjectProjectThreeAcceptanceFrame.Preference
      (fiveProjectPhysicalBorrower 3)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      (fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
        fiveProjectProjectThreeAcceptanceAction)
      (fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory EconomyAction.idle) := by
  rw [fiveProjectProjectThreeForecast_accept_end,
    fiveProjectProjectThreeForecast_idle_end]
  let acceptEnd : fiveProjectProjectThreeAcceptanceSuffix.program.End :=
    .bundle (fiveProjectFourFactorForecastRun.state.stock
      (fiveProjectPhysicalBorrower 3))
  let idleEnd : fiveProjectProjectThreeAcceptanceSuffix.program.End :=
    .bundle ((fiveProjectFourFactorForecastDeclineRun 3).state.stock
      (fiveProjectPhysicalBorrower 3))
  change fiveProjectEntrepreneurPrefers
    (fiveProjectProgramEndEntrepreneurOutcome 3 acceptEnd)
    (fiveProjectProgramEndEntrepreneurOutcome 3 idleEnd)
  have haccept :
      fiveProjectProgramEndEntrepreneurOutcome 3 acceptEnd =
        fiveProjectFourFactorForecastRun.entrepreneurOutcome 3 := by
    dsimp [acceptEnd]
    decide
  have hidle :
      fiveProjectProgramEndEntrepreneurOutcome 3 idleEnd =
        (fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3 := by
    dsimp [idleEnd]
    decide
  rw [haccept, hidle]
  rcases fiveProject_four_factor_forecast_marginal_entry_improves_on_declining with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpreferThree⟩
  exact hpreferThree

noncomputable def fiveProjectProjectThreeDeclineChoiceHistory :=
  fiveProjectProjectThreeAcceptanceFrame.sigma
    (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
    EconomyAction.idle fiveProjectProjectThreeAcceptanceSuffix.selectedHistory

set_option maxRecDepth 16384 in
theorem fiveProjectProjectThreeDeclineChoice_preserves_collateral_stock :
    fiveProjectProjectThreeDeclineChoiceHistory.terminalState.stock
      (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3) = 1 := by
  let suffix := fiveProjectProjectThreeAcceptanceSuffix
  let actor := fiveProjectPhysicalBorrower 3
  let h := suffix.selectedHistory
  have hmenu : EconomyAction.idle ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu actor := by
    exact (FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).idle_mem actor
  change (suffix.program.selectByBehavior
      (fiveProjectPhysicalSuffixBehavior suffix 3) actor
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle h).terminalState.stock
      actor (fiveProjectCollateralGood 3) = 1
  rw [suffix.program.selectByBehavior_eq_selectedHistory
    (fiveProjectPhysicalSuffixBehavior suffix 3) actor
    FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle h
    (FiniteEconomyProgram.ProgramMoment.root_memHist h) hmenu]
  rw [fiveProjectPhysicalSuffixBehavior_selectedHistory_root
    suffix 3 actor EconomyAction.idle h hmenu]
  decide +revert

def fiveProjectProjectTwoActualChoiceHistory :=
  fiveProjectProjectTwoAcceptanceSuffix.selectedHistory

noncomputable def fiveProjectProjectTwoDeclineChoiceHistory :=
  fiveProjectProjectTwoAcceptanceFrame.sigma
    (fiveProjectPhysicalBorrower 2) FiniteEconomyProgram.ProgramMoment.root
    EconomyAction.idle fiveProjectProjectTwoActualChoiceHistory

set_option maxRecDepth 16384 in
theorem fiveProjectProjectTwoDeclineChoice_preserves_collateral_stock :
    fiveProjectProjectTwoDeclineChoiceHistory.terminalState.stock
      (fiveProjectPhysicalBorrower 2) (fiveProjectCollateralGood 2) = 1 := by
  let suffix := fiveProjectProjectTwoAcceptanceSuffix
  let actor := fiveProjectPhysicalBorrower 2
  let h := fiveProjectProjectTwoActualChoiceHistory
  have hmenu : EconomyAction.idle ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu actor := by
    exact (FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).idle_mem actor
  change (suffix.program.selectByBehavior
      (fiveProjectPhysicalSuffixBehavior suffix 2) actor
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle h).terminalState.stock
      actor (fiveProjectCollateralGood 2) = 1
  rw [suffix.program.selectByBehavior_eq_selectedHistory
    (fiveProjectPhysicalSuffixBehavior suffix 2) actor
    FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle h
    (FiniteEconomyProgram.ProgramMoment.root_memHist h) hmenu]
  rw [fiveProjectPhysicalSuffixBehavior_selectedHistory_root
    suffix 2 actor EconomyAction.idle h hmenu]
  decide +revert

set_option maxRecDepth 16384 in
theorem fiveProjectProjectTwoLoanEntryDeclinePreferredInFrame :
    let W := fiveProjectProjectTwoAcceptanceFrame
    let i := fiveProjectPhysicalBorrower 2
    let h := fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
    let α := fiveProjectProjectTwoAcceptanceAction
    let β : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .idle
    let hAlt := W.sigma i FiniteEconomyProgram.ProgramMoment.root β h
    let τActual := W.ExpectedMaturation i α
      FiniteEconomyProgram.ProgramMoment.root h
    let τAlt := W.ExpectedMaturation i β
      FiniteEconomyProgram.ProgramMoment.root hAlt
    W.Preference i τActual h
      (W.OutcomeOf i β FiniteEconomyProgram.ProgramMoment.root τAlt hAlt)
      (W.OutcomeOf i α FiniteEconomyProgram.ProgramMoment.root τActual h) := by
  classical
  dsimp only
  let suffix := fiveProjectProjectTwoAcceptanceSuffix
  let actor := fiveProjectPhysicalBorrower 2
  let behavior := fiveProjectPhysicalSuffixBehavior suffix 2
  let hActual := suffix.selectedHistory
  let hDecline := fiveProjectProjectTwoDeclineChoiceHistory
  have hDeclineTerminal : hDecline.terminalState.stock actor
      (fiveProjectCollateralGood 2) = 1 := by
    exact fiveProjectProjectTwoDeclineChoice_preserves_collateral_stock
  have hActualTerminal : hActual.terminalState.stock actor
      (fiveProjectCollateralGood 2) = 0 := by
    decide
  have hHorizon : behavior.evaluationHorizon actor
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectTwoAcceptanceAction = .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  have hAltHorizon : behavior.evaluationHorizon actor
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle =
        .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  let τActual := suffix.program.expectedMaturation behavior actor
    FiniteEconomyProgram.ProgramMoment.root
    fiveProjectProjectTwoAcceptanceAction hActual
  let τAlt := suffix.program.expectedMaturation behavior actor
    FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle hDecline
  have hActualMaturation : τActual = hActual.terminalMoment := by
    dsimp [τActual, FinitePhysicalEconomyProgram.expectedMaturation]
    rw [hHorizon]
    rfl
  have hAltMaturation : τAlt = hDecline.terminalMoment := by
    dsimp [τAlt, FinitePhysicalEconomyProgram.expectedMaturation]
    rw [hAltHorizon]
    rfl
  change fiveProjectPhysicalSuffixPreference suffix.program 2 actor τActual
    hActual (.timed (suffix.program.outcomeAt actor τAlt) τAlt)
    (.timed (suffix.program.outcomeAt actor τActual) τActual)
  simp only [fiveProjectPhysicalSuffixPreference, actor, ↓reduceIte]
  rw [hAltMaturation, hActualMaturation]
  simp only [FinitePhysicalEconomyProgram.outcomeAt,
    FinitePhysicalEconomyProgram.stateAt_terminalMoment,
    fiveProjectProgramEndEntrepreneurOutcome, finiteProgramEndRequirement]
  rw [hDeclineTerminal, hActualTerminal]
  simp [fiveProjectEntrepreneurPrefers]

/-- The actual project-two acceptance has contextual regret under the frame's
own deterministic alternative selector: the declined branch retains the
collateral that the actual default branch transfers to the bank. -/
theorem fiveProjectProjectTwoAcceptance_hasContextMatchedRegret :
    let F := fiveProjectProjectTwoAcceptanceFrame
    letI : ActionFrame := F
    ContextMatchedRegret F.deterministicCorrespondence
      (fiveProjectPhysicalBorrower 2)
      (F.decisionIndex FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
        (FiniteEconomyProgram.ProgramMoment.root_memHist _))
      (F.ExpectedMaturation (fiveProjectPhysicalBorrower 2)
        fiveProjectProjectTwoAcceptanceAction FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectTwoAcceptanceSuffix.selectedHistory)
      fiveProjectProjectTwoAcceptanceAction EconomyAction.idle := by
  let actor := fiveProjectPhysicalBorrower 2
  let history := fiveProjectProjectTwoAcceptanceSuffix.selectedHistory
  exact @contextMatchedRegret_of_selected_outcome_improvement
    fiveProjectProjectTwoAcceptanceFrame actor
    (fiveProjectProjectTwoAcceptanceFrame.decisionIndex
      FiniteEconomyProgram.ProgramMoment.root history
      (FiniteEconomyProgram.ProgramMoment.root_memHist history))
    fiveProjectProjectTwoAcceptanceAction EconomyAction.idle
    fiveProjectProjectTwoAcceptanceAction_feasible
    fiveProjectProjectTwoAcceptanceAction_executes
    (ActionFrame.alpha_zero_feasible fiveProjectProjectTwoAcceptanceFrame actor
      FiniteEconomyProgram.ProgramMoment.root history)
    fiveProjectProjectTwoLoanEntryDeclinePreferredInFrame

set_option maxRecDepth 16384 in
theorem fiveProjectProjectThreeLoanEntryDeclinePreferredInFrame :
    let W := fiveProjectProjectThreeAcceptanceFrame
    let i := fiveProjectPhysicalBorrower 3
    let h := fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
    let α := fiveProjectProjectThreeAcceptanceAction
    let β : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .idle
    let hAlt := W.sigma i FiniteEconomyProgram.ProgramMoment.root β h
    let τActual := W.ExpectedMaturation i α
      FiniteEconomyProgram.ProgramMoment.root h
    let τAlt := W.ExpectedMaturation i β
      FiniteEconomyProgram.ProgramMoment.root hAlt
    W.Preference i τActual h
      (W.OutcomeOf i β FiniteEconomyProgram.ProgramMoment.root τAlt hAlt)
      (W.OutcomeOf i α FiniteEconomyProgram.ProgramMoment.root τActual h) := by
  classical
  dsimp only
  let suffix := fiveProjectProjectThreeAcceptanceSuffix
  let actor := fiveProjectPhysicalBorrower 3
  let behavior := fiveProjectPhysicalSuffixBehavior suffix 3
  let hActual := suffix.selectedHistory
  let hDecline := fiveProjectProjectThreeDeclineChoiceHistory
  have hDeclineTerminal : hDecline.terminalState.stock actor
      (fiveProjectCollateralGood 3) = 1 := by
    exact fiveProjectProjectThreeDeclineChoice_preserves_collateral_stock
  have hActualTerminal : hActual.terminalState.stock actor
      (fiveProjectCollateralGood 3) = 0 := by
    decide
  have hHorizon : behavior.evaluationHorizon actor
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceAction = .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  have hAltHorizon : behavior.evaluationHorizon actor
      FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle =
        .terminalSettlement := by
    simp [behavior, fiveProjectPhysicalSuffixBehavior,
      fiveProjectPhysicalSuffixBaseBehavior,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.withRootContinuation,
      FinitePhysicalEconomyProgram.ActionFrameBehavior.fromReferenceHistory]
  let τActual := suffix.program.expectedMaturation behavior actor
    FiniteEconomyProgram.ProgramMoment.root
    fiveProjectProjectThreeAcceptanceAction hActual
  let τAlt := suffix.program.expectedMaturation behavior actor
    FiniteEconomyProgram.ProgramMoment.root EconomyAction.idle hDecline
  have hActualMaturation : τActual = hActual.terminalMoment := by
    dsimp [τActual, FinitePhysicalEconomyProgram.expectedMaturation]
    rw [hHorizon]
    rfl
  have hAltMaturation : τAlt = hDecline.terminalMoment := by
    dsimp [τAlt, FinitePhysicalEconomyProgram.expectedMaturation]
    rw [hAltHorizon]
    rfl
  change fiveProjectPhysicalSuffixPreference suffix.program 3 actor τActual
    hActual (.timed (suffix.program.outcomeAt actor τAlt) τAlt)
    (.timed (suffix.program.outcomeAt actor τActual) τActual)
  simp only [fiveProjectPhysicalSuffixPreference, actor, ↓reduceIte]
  rw [hAltMaturation, hActualMaturation]
  simp only [FinitePhysicalEconomyProgram.outcomeAt,
    FinitePhysicalEconomyProgram.stateAt_terminalMoment,
    fiveProjectProgramEndEntrepreneurOutcome, finiteProgramEndRequirement]
  rw [hDeclineTerminal, hActualTerminal]
  simp [fiveProjectEntrepreneurPrefers]

theorem fiveProjectProjectThreeAcceptanceAction_selected :
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root (fiveProjectPhysicalBorrower 3) =
        fiveProjectProjectThreeAcceptanceAction := by
  decide

theorem fiveProjectProjectThreeAcceptanceAction_feasible :
    fiveProjectProjectThreeAcceptanceAction ∈
      fiveProjectProjectThreeAcceptanceFrame.A_feas
        (fiveProjectPhysicalBorrower 3)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory := by
  let suffix := fiveProjectProjectThreeAcceptanceSuffix
  change fiveProjectProjectThreeAcceptanceAction ∈ feasibleMenu
    fiveProjectPhysicalOperations (suffix.program.stateAt
      FiniteEconomyProgram.ProgramMoment.root) (fiveProjectPhysicalBorrower 3)
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
        (fiveProjectPhysicalBorrower 3))
  have hmenu := FiniteEconomyProgram.ProgramHistory.enactedAt_root_mem_menu
    suffix.selectedHistory (fiveProjectPhysicalBorrower 3)
  rw [fiveProjectProjectThreeAcceptanceAction_selected] at hmenu
  apply (mem_feasibleMenu_iff fiveProjectPhysicalOperations
    (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
    (fiveProjectPhysicalBorrower 3)
    ((FiniteEconomyProgram.ProgramMoment.root.currentStage
      (program := suffix.program.toFiniteEconomyProgram)).menu
      (fiveProjectPhysicalBorrower 3))
    fiveProjectProjectThreeAcceptanceAction).2
  refine ⟨hmenu, ?_⟩
  intro good
  by_cases hgood : good = fiveProjectCollateralGood 3
  · subst good
    change 1 ≤ (fiveProjectFiduciaryAcceptancePrefix 3).state.stock
      (fiveProjectPhysicalBorrower 3) (fiveProjectCollateralGood 3)
    decide
  · simp only [rawActionUse, fiveProjectProjectThreeAcceptanceAction,
      fiveProjectLoanMarket, ite_eq_right hgood]
    exact Nat.zero_le _

theorem fiveProjectProjectThreeAcceptanceAction_executes :
    @Exec fiveProjectProjectThreeAcceptanceFrame
      (fiveProjectPhysicalBorrower 3)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceAction
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory := by
  change FiniteEconomyProgram.ProgramMoment.memHist
      fiveProjectProjectThreeAcceptanceSuffix.program.toFiniteEconomyProgram
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory ∧
    FiniteEconomyProgram.ProgramHistory.enactedAt
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      FiniteEconomyProgram.ProgramMoment.root (fiveProjectPhysicalBorrower 3) =
        fiveProjectProjectThreeAcceptanceAction
  exact ⟨FiniteEconomyProgram.ProgramMoment.root_memHist _,
    fiveProjectProjectThreeAcceptanceAction_selected⟩

/-- The project-three acceptance node has only the enacted quote and idle in
its feasible menu. This is obtained from the affordable alternatives in the
existing loan instruction. -/
theorem fiveProjectProjectThreeAcceptanceAction_complete_menu
    (action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation)
    (haction : action ∈ fiveProjectProjectThreeAcceptanceFrame.A_feas
      (fiveProjectPhysicalBorrower 3)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory) :
    action = EconomyAction.idle ∨ action = fiveProjectProjectThreeAcceptanceAction := by
  let acceptancePrefix := fiveProjectFiduciaryAcceptancePrefix 3
  let suffix := fiveProjectProjectThreeAcceptanceSuffix
  have hrootMenu : action ∈
      (FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
          (fiveProjectPhysicalBorrower 3) :=
    (mem_feasibleMenu_iff fiveProjectPhysicalOperations
      (suffix.program.stateAt FiniteEconomyProgram.ProgramMoment.root)
      (fiveProjectPhysicalBorrower 3)
      ((FiniteEconomyProgram.ProgramMoment.root.currentStage
        (program := suffix.program.toFiniteEconomyProgram)).menu
          (fiveProjectPhysicalBorrower 3)) action).1 haction |>.1
  have hplanned : acceptancePrefix.cursor.plannedAdvances[3]? = some ⟨3, 5⟩ := by
    decide
  have hinstruction : fiveProjectPhysicalInstruction
      (fiveProjectRegimeData .fiduciaryExpansion) acceptancePrefix.cursor
        acceptancePrefix.state =
        fiveProjectAdvanceInstruction ⟨3, 5⟩ := by
    have hphase := fiveProjectFiduciaryAcceptancePrefix_at_phase 3
    change acceptancePrefix.cursor.remainingPhases.head? =
      some (.loanAcceptance 3) at hphase
    cases hremaining : acceptancePrefix.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        have hphase' : phase = .loanAcceptance 3 := by
          simpa [hremaining] using hphase
        subst phase
        simp [fiveProjectPhysicalInstruction, hremaining, hplanned]
  change action ∈ (fiveProjectPhysicalInstruction
    (fiveProjectRegimeData .fiduciaryExpansion) acceptancePrefix.cursor
      acceptancePrefix.state).stageMenu
      fiveProjectPhysicalOperations acceptancePrefix.state
      (fiveProjectPhysicalBorrower 3) at hrootMenu
  rw [hinstruction, PhysicalProfileInstruction.stageMenu,
    Finset.mem_insert, Finset.mem_insert] at hrootMenu
  rcases hrootMenu with hidle | hscheduled | halt
  · exact Or.inl hidle
  · have hscheduled' : (fiveProjectAdvanceInstruction ⟨3, 5⟩).affordableProfile
        fiveProjectPhysicalOperations acceptancePrefix.state
        (fiveProjectPhysicalBorrower 3) =
          fiveProjectProjectThreeAcceptanceAction := by
      change (if actionAffordable fiveProjectPhysicalOperations acceptancePrefix.state
        (fiveProjectPhysicalBorrower 3)
        (fiveProjectScheduledTransferProfile fiveProjectBank
          (fiveProjectPhysicalBorrower 3) 1 fiveProjectMoneyGood 1
          (fiveProjectCollateralGood 3) (fiveProjectPhysicalBorrower 3))
        then fiveProjectScheduledTransferProfile fiveProjectBank
          (fiveProjectPhysicalBorrower 3) 1 fiveProjectMoneyGood 1
          (fiveProjectCollateralGood 3) (fiveProjectPhysicalBorrower 3)
        else EconomyAction.idle) = fiveProjectProjectThreeAcceptanceAction
      decide
    exact Or.inr (hscheduled'.symm ▸ hscheduled)
  · have hempty :
        (fiveProjectAdvanceInstruction ⟨3, 5⟩).affordableAlternatives
          fiveProjectPhysicalOperations acceptancePrefix.state
          (fiveProjectPhysicalBorrower 3) = ∅ := by
      simp [PhysicalProfileInstruction.affordableAlternatives,
        fiveProjectAdvanceInstruction, fiveProjectTransferInstruction]
    rw [hempty] at halt
    simp at halt

set_option maxRecDepth 16384 in
theorem fiveProjectProjectThreeAcceptanceAction_purposeful :
    fiveProjectProjectThreeSubjectiveFrame.PurposefulAct
      (fiveProjectPhysicalBorrower 3)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      fiveProjectProjectThreeAcceptanceAction := by
  apply SubjectiveScenarioFrame.purposefulAct_of_appraisal_certificate_subjective
    fiveProjectProjectThreeSubjectiveFrame
  refine ⟨fiveProjectProjectThreeAcceptanceAction_feasible,
    fiveProjectProjectThreeAcceptanceAction_executes, Or.inr ?_, ?_⟩
  · exact fiveProjectProjectThreeForecast_accept_improves_on_idle
  · intro alternative halternative hbetter
    have hmenu := fiveProjectProjectThreeAcceptanceAction_complete_menu
      alternative halternative
    change fiveProjectPhysicalSuffixPreference
      fiveProjectProjectThreeAcceptanceSuffix.program 3
      (fiveProjectPhysicalBorrower 3)
      FiniteEconomyProgram.ProgramMoment.root
      fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
      (fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory alternative)
      (fiveProjectProjectThreeSubjectiveFrame.IntendedEnd
        (fiveProjectPhysicalBorrower 3) FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
        fiveProjectProjectThreeAcceptanceAction) at hbetter
    rcases hmenu with hidle | haccept
    · subst alternative
      exact (fiveProjectProjectThreeAcceptanceFrame.pref_asymm
        (fiveProjectPhysicalBorrower 3)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
        fiveProjectProjectThreeForecast_accept_improves_on_idle) hbetter
    · subst alternative
      exact fiveProjectProjectThreeAcceptanceFrame.pref_asymm
        (fiveProjectPhysicalBorrower 3)
        FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory hbetter hbetter

/-- Project three's actual acceptance is regrettable under the same
deterministic context: after default, declining the loan preserves the
borrower's collateral, while the generated actual branch transfers it. -/
theorem fiveProjectProjectThreeAcceptance_hasContextMatchedRegret :
    let F := fiveProjectProjectThreeAcceptanceFrame
    letI : ActionFrame := F
    ContextMatchedRegret F.deterministicCorrespondence
      (fiveProjectPhysicalBorrower 3)
      (F.decisionIndex FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
        (FiniteEconomyProgram.ProgramMoment.root_memHist _))
      (F.ExpectedMaturation (fiveProjectPhysicalBorrower 3)
        fiveProjectProjectThreeAcceptanceAction FiniteEconomyProgram.ProgramMoment.root
        fiveProjectProjectThreeAcceptanceSuffix.selectedHistory)
      fiveProjectProjectThreeAcceptanceAction EconomyAction.idle := by
  let actor := fiveProjectPhysicalBorrower 3
  let history := fiveProjectProjectThreeAcceptanceSuffix.selectedHistory
  exact @contextMatchedRegret_of_selected_outcome_improvement
    fiveProjectProjectThreeAcceptanceFrame actor
    (fiveProjectProjectThreeAcceptanceFrame.decisionIndex
      FiniteEconomyProgram.ProgramMoment.root history
      (FiniteEconomyProgram.ProgramMoment.root_memHist history))
    fiveProjectProjectThreeAcceptanceAction EconomyAction.idle
    fiveProjectProjectThreeAcceptanceAction_feasible
    fiveProjectProjectThreeAcceptanceAction_executes
    (ActionFrame.alpha_zero_feasible fiveProjectProjectThreeAcceptanceFrame actor
      FiniteEconomyProgram.ProgramMoment.root history)
    fiveProjectProjectThreeLoanEntryDeclinePreferredInFrame

end Praxeology

end
