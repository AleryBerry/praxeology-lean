/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.ProfileProgram

/-!
# Economic outcomes of the five-project physical program

The inventory interpreter already records physical holdings and delivered
services. The event cursor separately records matched contracts and their
settlements. This structure joins those existing records for appraisal without
turning a quote, proposed transfer, or absent behavioral certificate into an
executed economic fact.
-/

@[expose] public section

namespace Praxeology

/-- One actually originated credit position. Contract terms and settlement
status remain separate: the assigned quote supplies the promised amount, while
matched transfer events supply repayment or maturity status. -/
structure FiveProjectCreditPosition where
  bid : LoanReservationBid
  terms : FundedLoanTerms
  status : FiveProjectLoanStatus
  collateralAtBank : Nat

/-- The five-project program's end state preserves physical goods and service
delivery alongside the contract events that actually matched. Collateral
custody is read from inventory; deposit and loan positions are read from the
cursor's matched event projections. -/
structure FiveProjectEconomicOutcome where
  inventory : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat
  householdConsumptionServices : Nat
  depositContract : Option FiveProjectDepositTerms
  /-- The active deposit obligation remains present only before its matched
  redemption. -/
  depositLiabilityOutstanding : Option FiveProjectDepositTerms
  depositClaimHeldByHousehold : Nat
  depositRedemptions : List FiveProjectDepositTerms
  advances : List LoanReservationBid
  repayments : List LoanReservationBid
  defaults : List LoanReservationBid
  collateralAtBank : Fin 5 → Nat
  /-- Legal title follows the recorded origination agreement and lifecycle
  status. This is distinct from the bank's physical custody balance. -/
  collateralLegalOwner : Fin 5 → FiveProjectPhysicalAgent
  /-- An absent quote stays absent; present positions arise only from matched
  advances and carry their event-derived status. -/
  creditPositions : Option (List FiveProjectCreditPosition)
  outstandingCreditPositions : Option (List FiveProjectCreditPosition)

/-- Legal title follows the agreement recorded at origination and the actual
credit lifecycle status. This is distinct from physical custody. -/
def FiveProjectPhysicalRun.collateralLegalOwner
    (run : FiveProjectPhysicalRun) (project : Fin 5) :
    FiveProjectPhysicalAgent :=
  match run.cursor.actualPawnAgreements.find? fun agreement =>
      decide (agreement.bid.borrower = project) with
  | none => fiveProjectPhysicalBorrower project
  | some agreement => agreement.titleOwner (run.cursor.loanStatus agreement.bid)

/-- Fixed entrepreneur appraisal inputs: terminal collateral ownership first,
terminal money second, and total physical holdings as a monotone tie-break.
The same relation is used for selected outcomes and replayed alternatives. -/
structure FiveProjectEntrepreneurOutcome where
  collateralOwned : Nat
  terminalMoney : Nat
  totalPhysicalHoldings : Nat
  deriving DecidableEq, Repr

/-- Actor-specific terminal appraisal from the same physical run used for
market and settlement accounting. -/
def FiveProjectPhysicalRun.entrepreneurOutcome
    (run : FiveProjectPhysicalRun) (project : Fin 5) :
    FiveProjectEntrepreneurOutcome :=
  let borrower := fiveProjectPhysicalBorrower project
  { collateralOwned := if run.collateralLegalOwner project = borrower then 1 else 0
    terminalMoney := run.state.stock borrower fiveProjectMoneyGood
    totalPhysicalHoldings := Finset.univ.sum fun good => run.state.stock borrower good }

/-- Strict lexicographic ordinal preference on the stated terminal attributes.
No production success or loan purposefulness is inferred from this ranking. -/
def fiveProjectEntrepreneurPrefers
    (preferred other : FiveProjectEntrepreneurOutcome) : Prop :=
  preferred.collateralOwned > other.collateralOwned ∨
    (preferred.collateralOwned = other.collateralOwned ∧
      preferred.terminalMoney > other.terminalMoney) ∨
    (preferred.collateralOwned = other.collateralOwned ∧
      preferred.terminalMoney = other.terminalMoney ∧
      preferred.totalPhysicalHoldings > other.totalPhysicalHoldings)

theorem fiveProjectEntrepreneurPrefers_irrefl
    (outcome : FiveProjectEntrepreneurOutcome) :
    ¬ fiveProjectEntrepreneurPrefers outcome outcome := by
  simp only [fiveProjectEntrepreneurPrefers]
  omega

theorem fiveProjectEntrepreneurPrefers_asymmetric
    (preferred other : FiveProjectEntrepreneurOutcome)
    (h : fiveProjectEntrepreneurPrefers preferred other) :
    ¬ fiveProjectEntrepreneurPrefers other preferred := by
  simp only [fiveProjectEntrepreneurPrefers] at h ⊢
  omega

private theorem fiveProjectEntrepreneurPrefers_of_more_collateral
    (preferred other : FiveProjectEntrepreneurOutcome)
    (h : preferred.collateralOwned > other.collateralOwned) :
    fiveProjectEntrepreneurPrefers preferred other := by
  unfold fiveProjectEntrepreneurPrefers
  exact Or.inl h

/-- A deposit liability remains active until the same contract terms have a
matched redemption event. -/
def FiveProjectPhysicalCursor.depositLiabilityOutstanding
    (cursor : FiveProjectPhysicalCursor) : Option FiveProjectDepositTerms :=
  cursor.actualDepositContract.filter fun terms =>
    !cursor.actualDepositRedemptions.contains terms

/-- Attach assigned terms and event-derived status to each matched advance.
An absent quote is preserved explicitly. -/
def FiveProjectPhysicalRun.creditPositions
    (run : FiveProjectPhysicalRun) : Option (List FiveProjectCreditPosition) :=
  run.cursor.loanQuote.map fun promisedRepayment =>
    run.cursor.actualAdvances.map fun bid =>
      { bid := bid
        terms :=
          { borrower := bid.borrower
            principal := fiveProjectLoanMarket.principal
            principal_positive := fiveProjectLoanMarket.principal_positive
            promisedRepayment := promisedRepayment }
        status := run.cursor.loanStatus bid
        collateralAtBank := run.state.stock fiveProjectBank
          (fiveProjectCollateralGood bid.borrower) }

/-- Retain only positions whose debt remains open after the recorded events. -/
def FiveProjectPhysicalRun.outstandingCreditPositions
    (run : FiveProjectPhysicalRun) : Option (List FiveProjectCreditPosition) :=
  run.creditPositions.map fun positions =>
    positions.filter fun position => position.status = .outstanding

/-- Project a completed physical run into its full recorded outcome. Every
field is a projection of the interpreted state or matched event trace. -/
def FiveProjectPhysicalRun.economicOutcome
    (run : FiveProjectPhysicalRun) : FiveProjectEconomicOutcome where
  inventory := run.state
  householdConsumptionServices := run.cursor.actualHouseholdConsumptionServices
  depositContract := run.cursor.actualDepositContract
  depositLiabilityOutstanding := run.cursor.depositLiabilityOutstanding
  depositClaimHeldByHousehold := run.state.stock fiveProjectHousehold
    fiveProjectDepositClaimGood
  depositRedemptions := run.cursor.actualDepositRedemptions
  advances := run.cursor.actualAdvances
  repayments := run.cursor.actualRepayments
  defaults := run.cursor.actualDefaults
  collateralAtBank project := run.state.stock fiveProjectBank
    (fiveProjectCollateralGood project)
  collateralLegalOwner := run.collateralLegalOwner
  creditPositions := run.creditPositions
  outstandingCreditPositions := run.outstandingCreditPositions

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_inventory
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.inventory = run.state := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_services
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.householdConsumptionServices =
      run.cursor.actualHouseholdConsumptionServices := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_depositContract
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.depositContract = run.cursor.actualDepositContract := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_depositLiability
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.depositLiabilityOutstanding =
      run.cursor.depositLiabilityOutstanding := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_depositClaim
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.depositClaimHeldByHousehold =
      run.state.stock fiveProjectHousehold fiveProjectDepositClaimGood := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_creditEvents
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.advances = run.cursor.actualAdvances ∧
    run.economicOutcome.repayments = run.cursor.actualRepayments ∧
    run.economicOutcome.defaults = run.cursor.actualDefaults := by
  exact ⟨rfl, rfl, rfl⟩

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_collateral
    (run : FiveProjectPhysicalRun) (project : Fin 5) :
    run.economicOutcome.collateralAtBank project =
      run.state.stock fiveProjectBank (fiveProjectCollateralGood project) := rfl

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_collateralLegalOwner
    (run : FiveProjectPhysicalRun) (project : Fin 5) :
    run.economicOutcome.collateralLegalOwner project =
      run.collateralLegalOwner project := rfl

theorem FiveProjectPawnAgreement.unpaid_maturity_transfers_title_and_discharges
    (agreement : FiveProjectPawnAgreement) :
    agreement.titleOwner .defaulted = agreement.lender ∧
    agreement.remainingObligation .defaulted = none := by
  exact ⟨agreement.title_after_unpaid_maturity,
    agreement.obligation_discharged_by_collateral_at_default⟩

/-- The entrepreneur's lower-quote forecast holds its observed local cash,
note issue, completion-factor stock, and published loan rules fixed. It
conjectures that the household preserves its two factors for sale rather than
consuming them; actual household consumption remains whatever the selected
physical history records. -/
def fiveProjectFourFactorForecastData : FiveProjectRegimeData :=
  { fiveProjectRegimeData .fiduciaryExpansion with
    householdFactorsConsumed := 0
    householdFactorsOffered := 2
    household_factor_accounting := by decide }

/-- Execute the explicit lower-quote forecast using the same physical
instruction generator and market rules as the selected cycle runs. -/
def fiveProjectFourFactorForecastRun : FiveProjectPhysicalRun :=
  fiveProjectNamedProgramRun fiveProjectFourFactorForecastData

set_option maxRecDepth 2048 in
/-- The four-factor forecast funds four published advances, quotes four,
clears the completion-factor market at one, and physically completes and
repays all four projects. These are computed forecast consequences, not facts
about the actual hidden household consumption path. -/
theorem fiveProject_four_factor_forecast_executes_all_projects :
    fiveProjectFourFactorForecastRun.cursor.actualAdvances.map
        LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    fiveProjectFourFactorForecastRun.cursor.loanQuote = some 4 ∧
    fiveProjectFourFactorForecastRun.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (1, [0, 1, 2, 3]) ∧
    fiveProjectFourFactorForecastRun.cursor.completedProjects.map
        LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    fiveProjectFourFactorForecastRun.cursor.actualRepayments.map
        LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    fiveProjectFourFactorForecastRun.cursor.actualDefaults = [] := by
  decide

/-- A forecast alternative declines one published loan while the bank's offer
and every other actor's scheduled action stay fixed at the acceptance phase.
Later markets and settlements are regenerated from the refusal branch. -/
def fiveProjectFourFactorForecastDeclineRun (project : Fin 5) :
    FiveProjectPhysicalRun :=
  fiveProjectRunUsingProfileSelector fiveProjectFourFactorForecastData
    (fiveProjectProfileSelectorWithUnilateralIdle fiveProjectFourFactorForecastData
      (.loanAcceptance project) (fiveProjectPhysicalBorrower project))
    fiveProjectPhysicalFuel
    (fiveProjectInitialRun fiveProjectFourFactorForecastData)

set_option maxRecDepth 4096 in
/-- Under the same fixed collateral-first, money-second preference, accepting
either marginal loan improves on declining in the four-factor forecast. The
comparison is executed through the same state-dependent program; it does not
assert that the hidden household choice matches the forecast. -/
theorem fiveProject_four_factor_forecast_marginal_entry_improves_on_declining :
    (fiveProjectFourFactorForecastRun.entrepreneurOutcome 2).collateralOwned = 1 ∧
    (fiveProjectFourFactorForecastRun.entrepreneurOutcome 2).terminalMoney = 3 ∧
    (fiveProjectFourFactorForecastDeclineRun 2).cursor.actualAdvances.map
      LoanReservationBid.borrower = [0, 1, 3] ∧
    (fiveProjectFourFactorForecastDeclineRun 2).cursor.loanQuote = some 4 ∧
    ((fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2).collateralOwned = 1 ∧
    ((fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2).terminalMoney = 1 ∧
    fiveProjectEntrepreneurPrefers
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 2)
      ((fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2) ∧
    (fiveProjectFourFactorForecastRun.entrepreneurOutcome 3).collateralOwned = 1 ∧
    (fiveProjectFourFactorForecastRun.entrepreneurOutcome 3).terminalMoney = 2 ∧
    (fiveProjectFourFactorForecastDeclineRun 3).cursor.actualAdvances.map
      LoanReservationBid.borrower = [0, 1, 2] ∧
    (fiveProjectFourFactorForecastDeclineRun 3).cursor.loanQuote = some 4 ∧
    ((fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3).collateralOwned = 1 ∧
    ((fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3).terminalMoney = 1 ∧
    fiveProjectEntrepreneurPrefers
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 3)
      ((fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3) := by
  have hcollateralAcceptedTwo :
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 2).collateralOwned = 1 := by
    decide
  have hmoneyAcceptedTwo :
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 2).terminalMoney = 3 := by
    decide
  have hcollateralDeclinedTwo :
      ((fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2).collateralOwned = 1 := by
    decide
  have hmoneyDeclinedTwo :
      ((fiveProjectFourFactorForecastDeclineRun 2).entrepreneurOutcome 2).terminalMoney = 1 := by
    decide
  have hcollateralAcceptedThree :
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 3).collateralOwned = 1 := by
    decide
  have hmoneyAcceptedThree :
      (fiveProjectFourFactorForecastRun.entrepreneurOutcome 3).terminalMoney = 2 := by
    decide
  have hcollateralDeclinedThree :
      ((fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3).collateralOwned = 1 := by
    decide
  have hmoneyDeclinedThree :
      ((fiveProjectFourFactorForecastDeclineRun 3).entrepreneurOutcome 3).terminalMoney = 1 := by
    decide
  refine ⟨hcollateralAcceptedTwo, hmoneyAcceptedTwo, by decide, by decide,
    hcollateralDeclinedTwo, hmoneyDeclinedTwo, ?_, hcollateralAcceptedThree,
    hmoneyAcceptedThree, by decide, by decide, hcollateralDeclinedThree,
    hmoneyDeclinedThree, ?_⟩
  · unfold fiveProjectEntrepreneurPrefers
    rw [hcollateralAcceptedTwo, hcollateralDeclinedTwo,
      hmoneyAcceptedTwo, hmoneyDeclinedTwo]
    simp
  · unfold fiveProjectEntrepreneurPrefers
    rw [hcollateralAcceptedThree, hcollateralDeclinedThree,
      hmoneyAcceptedThree, hmoneyDeclinedThree]
    simp

def fiveProjectHouseholdPlanOutcomeFor (D : FiveProjectRegimeData)
    (plan : FiveProjectHouseholdPlan) : FiveProjectHouseholdOutcome :=
  (fiveProjectHouseholdRunForPlan D plan).householdOutcome

private theorem fiveProjectHouseholdPrefers_of_higher_first_rank
    (preferred other : FiveProjectHouseholdOutcome)
    (h : (fiveProjectHouseholdPreferenceRank preferred).1 >
      (fiveProjectHouseholdPreferenceRank other).1) :
    fiveProjectHouseholdPrefers preferred other := by
  simp only [fiveProjectHouseholdPrefers]
  exact Or.inl h

private theorem fiveProjectHousehold_not_prefers_of_lower_first_rank
    (preferred other : FiveProjectHouseholdOutcome)
    (h : (fiveProjectHouseholdPreferenceRank preferred).1 <
      (fiveProjectHouseholdPreferenceRank other).1) :
    ¬ fiveProjectHouseholdPrefers preferred other := by
  intro hprefer
  simp only [fiveProjectHouseholdPrefers] at hprefer
  omega

private def fiveProjectHouseholdTransferPlans :
    Finset FiveProjectHouseholdPlan :=
  { { deposit := 0, consumedFactors := 0, offeredFactors := 0 },
    { deposit := 0, consumedFactors := 0, offeredFactors := 1 },
    { deposit := 0, consumedFactors := 0, offeredFactors := 2 },
    { deposit := 0, consumedFactors := 1, offeredFactors := 0 },
    { deposit := 0, consumedFactors := 1, offeredFactors := 1 },
    { deposit := 0, consumedFactors := 2, offeredFactors := 0 },
    { deposit := 2, consumedFactors := 0, offeredFactors := 0 },
    { deposit := 2, consumedFactors := 0, offeredFactors := 1 },
    { deposit := 2, consumedFactors := 0, offeredFactors := 2 },
    { deposit := 2, consumedFactors := 1, offeredFactors := 0 },
    { deposit := 2, consumedFactors := 1, offeredFactors := 1 },
    { deposit := 2, consumedFactors := 2, offeredFactors := 0 } }

private theorem fiveProject_household_transfer_menu_explicit :
    fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer) =
        fiveProjectHouseholdTransferPlans := by
  decide

/-- Explicit public listing of the household-transfer choice set used by the
finite outcome and ActionFrame menu witnesses. -/
theorem fiveProjectHouseholdTransferPlanChoices_explicit :
    fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer) =
    { { deposit := 0, consumedFactors := 0, offeredFactors := 0 },
      { deposit := 0, consumedFactors := 0, offeredFactors := 1 },
      { deposit := 0, consumedFactors := 0, offeredFactors := 2 },
      { deposit := 0, consumedFactors := 1, offeredFactors := 0 },
      { deposit := 0, consumedFactors := 1, offeredFactors := 1 },
      { deposit := 0, consumedFactors := 2, offeredFactors := 0 },
      { deposit := 2, consumedFactors := 0, offeredFactors := 0 },
      { deposit := 2, consumedFactors := 0, offeredFactors := 1 },
      { deposit := 2, consumedFactors := 0, offeredFactors := 2 },
      { deposit := 2, consumedFactors := 1, offeredFactors := 0 },
      { deposit := 2, consumedFactors := 1, offeredFactors := 1 },
      { deposit := 2, consumedFactors := 2, offeredFactors := 0 } } := by
  rw [fiveProject_household_transfer_menu_explicit]
  rfl

-- Each of the twelve menu alternatives is evaluated through the full finite
-- program, so this computation needs more kernel heartbeats than the default.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The twelve branch-sensitive runs are reduced through the shared physical
-- instruction interpreter and all downstream market and settlement stages.
/-- The selected saving plan is best within the full twelve-plan menu when
every plan is executed through the same cash transfer, auctions, production,
customer sales, repayment, and deposit-redemption rules. The preference is the
fixed reserve/service/money/holdings order stated at the household choice. -/
theorem fiveProject_household_saving_plan_is_menu_undominated :
    let D := fiveProjectRegimeData .householdTransfer
    let selected := fiveProjectHouseholdPlanOf D
    ∀ plan ∈ fiveProjectHouseholdPlanChoices D,
      ¬ fiveProjectHouseholdPrefers
        (fiveProjectHouseholdPlanOutcomeFor D plan)
        (fiveProjectHouseholdPlanOutcomeFor D selected) := by
  dsimp only
  intro plan hplan
  have hcases : plan ∈ fiveProjectHouseholdTransferPlans := by
    simpa [fiveProject_household_transfer_menu_explicit] using hplan
  simp only [fiveProjectHouseholdTransferPlans, Finset.mem_insert,
    Finset.mem_singleton] at hcases
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    exact fiveProjectHouseholdPrefers_irrefl _
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide
  · subst plan
    apply fiveProjectHousehold_not_prefers_of_lower_first_rank
    decide

set_option maxRecDepth 8192 in
/-- The chosen household plan strictly improves on idling under the same
terminal preference. Its menu optimality is proved separately above. -/
theorem fiveProject_household_saving_plan_improves_on_idle :
    let D := fiveProjectRegimeData .householdTransfer
    fiveProjectHouseholdPrefers
      (fiveProjectHouseholdPlanOutcomeFor D (fiveProjectHouseholdPlanOf D))
      (fiveProjectHouseholdIdleRunFor D).householdOutcome := by
  apply fiveProjectHouseholdPrefers_of_higher_first_rank
  decide

set_option maxRecDepth 16384 in
/-- Computed key household alternatives in the full settlement program. The
no-deposit outcomes keep terminal money and delivered services separate; the
deposit-two plan reaches the reserve threshold only when both household
factors are offered and sold. -/
theorem fiveProject_household_plan_key_outcomes :
    let D := fiveProjectRegimeData .householdTransfer
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 0, consumedFactors := 2, offeredFactors := 0 }).terminalMoney = 2 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 0, consumedFactors := 2, offeredFactors := 0 }).deliveredServices = 2 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 0, consumedFactors := 0, offeredFactors := 2 }).terminalMoney = 2 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 2, consumedFactors := 2, offeredFactors := 0 }).terminalMoney = 3 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 2, consumedFactors := 2, offeredFactors := 0 }).deliveredServices = 2 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 2, consumedFactors := 0, offeredFactors := 2 }).terminalMoney = 5 ∧
    (fiveProjectHouseholdPlanOutcomeFor D
      { deposit := 2, consumedFactors := 0, offeredFactors := 2 }).deliveredServices = 0 ∧
    let creditData :=
      { (fiveProjectRegimeData .fiduciaryExpansion) with
        householdFactorsConsumed := 0
        householdFactorsOffered := 2
        household_factor_accounting := by decide }
    let creditNoDepositPlan : FiveProjectHouseholdPlan :=
      { deposit := 0, consumedFactors := 0, offeredFactors := 2 }
    (fiveProjectHouseholdPlanOutcomeFor creditData creditNoDepositPlan).terminalMoney = 4 := by
  decide

set_option maxRecDepth 16384 in
/-- Offering at most one household factor leaves later supply at three. The
current-cash auction recomputes its price as two; the household's terminal
cash is three after deposit redemption. -/
theorem fiveProject_household_one_factor_offer_recomputes_market :
    let D := fiveProjectRegimeData .householdTransfer
    let plan : FiveProjectHouseholdPlan :=
      { deposit := 2, consumedFactors := 0, offeredFactors := 1 }
    let run := fiveProjectHouseholdRunForPlan D plan
    run.cursor.factorClearing.map Prod.fst = some 2 ∧
    run.state.stock fiveProjectHousehold fiveProjectMoneyGood = 3 := by
  decide

@[simp]
theorem FiveProjectPhysicalRun.economicOutcome_creditPositions
    (run : FiveProjectPhysicalRun) :
    run.economicOutcome.creditPositions = run.creditPositions ∧
    run.economicOutcome.outstandingCreditPositions =
      run.outstandingCreditPositions := by
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 2048 in
/-- The integrated outcomes preserve actual debt status and the deposit
liability separately from terminal inventories. In the credit-expansion path,
the two completed loans are repaid and the two unfinished loans are settled by
the stipulated nonrecourse maturity contract. In the saving path, the matched
deposit is redeemed and no liability remains outstanding. -/
theorem fiveProject_named_outcomes_preserve_contract_positions :
    let credit := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)
    let saving := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .householdTransfer)
    credit.economicOutcome.creditPositions.map (List.map fun position =>
      (position.bid.borrower, position.status)) =
        some [(0, .repaid), (1, .repaid), (2, .defaulted), (3, .defaulted)] ∧
    credit.economicOutcome.outstandingCreditPositions.map List.length = some 0 ∧
    credit.economicOutcome.collateralAtBank 2 = 1 ∧
    credit.economicOutcome.collateralAtBank 3 = 1 ∧
    credit.economicOutcome.collateralLegalOwner 2 = fiveProjectBank ∧
    credit.economicOutcome.collateralLegalOwner 3 = fiveProjectBank ∧
    (saving.economicOutcome.depositContract.map fun terms =>
      (terms.principal, terms.promisedRepayment)) = some (2, 3) ∧
    saving.economicOutcome.depositLiabilityOutstanding.isNone = true ∧
    saving.economicOutcome.depositClaimHeldByHousehold = 0 ∧
    saving.economicOutcome.householdConsumptionServices = 0 := by
  decide

set_option maxRecDepth 2048 in
/-- Declining at either marginal borrower's acceptance node preserves the
published quote and every peer's idle action at that node, then follows the
same later generated schedule. The accepted borrower defaults and transfers
collateral title to the bank; the declined borrower retains both title and the
initial buffer. The comparison uses the fixed collateral-first preference. -/
theorem fiveProject_marginal_loan_entry_decline_is_preferred :
    let accepted := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)
    let declineTwo := fiveProjectFiduciaryProjectTwoDeclineRun
    let declineThree := fiveProjectFiduciaryProjectThreeDeclineRun
    declineTwo.cursor.loanQuote = accepted.cursor.loanQuote ∧
    declineThree.cursor.loanQuote = accepted.cursor.loanQuote ∧
    declineTwo.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 3] ∧
    declineThree.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2] ∧
    declineTwo.cursor.actualDefaults.map LoanReservationBid.borrower = [3] ∧
    declineThree.cursor.actualDefaults.map LoanReservationBid.borrower = [2] ∧
    fiveProjectEntrepreneurPrefers
      (declineTwo.entrepreneurOutcome 2)
      (accepted.entrepreneurOutcome 2) ∧
    fiveProjectEntrepreneurPrefers
      (declineThree.entrepreneurOutcome 3)
      (accepted.entrepreneurOutcome 3) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · apply fiveProjectEntrepreneurPrefers_of_more_collateral
    decide
  · apply fiveProjectEntrepreneurPrefers_of_more_collateral
    decide

end Praxeology
