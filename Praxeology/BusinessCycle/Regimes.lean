/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Auctions
public import Praxeology.BusinessCycle.Information

/-!
# Three five-project funding regimes

These records expose the money and completion-factor sources for the baseline,
fiduciary expansion, and household-funding comparison. The household amount is
a cash transfer to the bank, bounded by an explicitly supplied household
money endowment; household factor consumption and offers exactly account for
its factor stock. This scenario data and its physical executor represent the
cash-transfer leg only: they do not record a deposit claim, a bank repayment
obligation, or purposeful household choice. The derived outcomes compose the
loan auction, the ascending factor clock, completion eligibility, and
unit-price customer sales.

The stated fixed example does not specify an initial household cash balance.
`fiveProjectRegimeDataWithHouseholdMoney` therefore takes the household cash
endowment and transfer as explicit inputs. `fiveProjectRegimeData` is only the
illustrative two-unit endowment/two-unit transfer calibration. Its resource
results are conditional on those extra scenario premises and do not establish
purposeful household saving.

This module is a scenario-accounting calculation over explicitly supplied
resource and market data. It does not construct executed action histories or
prove that household saving and entrepreneurial investment are purposeful.
Its demand and revenue-plan theorems are conditional market calculations;
`FactorExecution` separately runs factor transfers, completion operations,
customer sales, and auction-quoted repayments for projects that physically
complete. That execution does not establish default for excluded projects,
legal foreclosure, or preference-grounded choice.
-/

@[expose] public section

namespace Praxeology

inductive FiveProjectRegime where
  | baseline
  | fiduciaryExpansion
  /-- Scenario data representing a household-to-bank cash transfer and
  forgone factor consumption. The transfer is not yet paired with a recorded
  deposit claim or bank repayment obligation, and this constructor does not
  assert a voluntary or purposeful choice. -/
  | householdTransfer
  deriving DecidableEq, Repr

/-- Explicit source and use data for one regime. -/
structure FiveProjectRegimeData where
  bankMoney : ℕ
  fiduciaryNotesIssued : ℕ
  /-- Household money initially available before any scenario transfer. -/
  householdMoneyEndowment : ℕ
  /-- Household cash transferred to the bank in the scenario. This records a
  source of loanable funds, not the bank's deposit liability or the household's
  claim to repayment. -/
  householdMoneyTransferred : ℕ
  transfer_affordable : householdMoneyTransferred ≤ householdMoneyEndowment
  supplierFactorStock : ℕ
  householdFactorEndowment : ℕ
  householdFactorsConsumed : ℕ
  householdFactorsOffered : ℕ
  household_factor_accounting :
    householdFactorsConsumed + householdFactorsOffered = householdFactorEndowment

/-- The three regimes keep the stated bank and completion-factor resources
fixed while taking household money endowment and transfer as inputs. The
named illustration supplies two units for each household money quantity. -/
def fiveProjectRegimeDataWithHouseholdMoney
    (householdMoneyEndowment householdMoneyTransferred : ℕ)
    (transfer_affordable : householdMoneyTransferred ≤ householdMoneyEndowment) :
    FiveProjectRegime → FiveProjectRegimeData
  | .baseline =>
      { bankMoney := 2
        fiduciaryNotesIssued := 0
        householdMoneyEndowment := householdMoneyEndowment
        householdMoneyTransferred := 0
        transfer_affordable := Nat.zero_le _
        supplierFactorStock := 2
        householdFactorEndowment := 2
        householdFactorsConsumed := 2
        householdFactorsOffered := 0
        household_factor_accounting := by decide }
  | .fiduciaryExpansion =>
      { bankMoney := 2
        fiduciaryNotesIssued := 2
        householdMoneyEndowment := householdMoneyEndowment
        householdMoneyTransferred := 0
        transfer_affordable := Nat.zero_le _
        supplierFactorStock := 2
        householdFactorEndowment := 2
        householdFactorsConsumed := 2
        householdFactorsOffered := 0
        household_factor_accounting := by decide }
  | .householdTransfer =>
      { bankMoney := 2
        fiduciaryNotesIssued := 0
        householdMoneyEndowment := householdMoneyEndowment
        householdMoneyTransferred := householdMoneyTransferred
        transfer_affordable := transfer_affordable
        supplierFactorStock := 2
        householdFactorEndowment := 2
        householdFactorsConsumed := 0
        householdFactorsOffered := 2
        household_factor_accounting := by decide }

/-- Initial household cash used by the illustrative saving calculation. This
quantity is not specified by the fixed project table. -/
def fiveProjectIllustrativeHouseholdMoneyEndowment : ℕ := 2

/-- Household cash transferred in the illustrative funding calculation. -/
def fiveProjectIllustrativeHouseholdMoneyTransfer : ℕ := 2

/-- The named transfer calibration assumes two initial household money units
and transfers both, neither specified by the fixed project table. The
parameterized constructor above accepts other endowments and transfer amounts. -/
def fiveProjectRegimeData : FiveProjectRegime → FiveProjectRegimeData :=
  fiveProjectRegimeDataWithHouseholdMoney
    fiveProjectIllustrativeHouseholdMoneyEndowment
    fiveProjectIllustrativeHouseholdMoneyTransfer (by decide)

/-- Change only the supplier's stated factor stock while preserving the rest
of a regime's funding and household data. -/
def FiveProjectRegimeData.withSupplierFactorStock
    (D : FiveProjectRegimeData) (supplierStock : ℕ) : FiveProjectRegimeData :=
  { D with supplierFactorStock := supplierStock }

/-- Scenario loanable money is existing bank money plus issued notes plus the
household cash transfer. Deposit liabilities are not represented here. -/
def FiveProjectRegimeData.loanableMoney (D : FiveProjectRegimeData) : ℕ :=
  D.bankMoney + D.fiduciaryNotesIssued + D.householdMoneyTransferred

/-- Completion-factor supply is supplier stock plus factors the household
does not consume and offers to production. -/
def FiveProjectRegimeData.completionFactorSupply
    (D : FiveProjectRegimeData) : ℕ :=
  D.supplierFactorStock + D.householdFactorsOffered

/-- The named regime data conserves its actual loanable-money sources. -/
theorem fiveProjectRegimeData_money_sources (r : FiveProjectRegime) :
    (fiveProjectRegimeData r).loanableMoney =
      (fiveProjectRegimeData r).bankMoney +
        (fiveProjectRegimeData r).fiduciaryNotesIssued +
        (fiveProjectRegimeData r).householdMoneyTransferred := by
  rfl

/-- Existing bank money is the same in each comparison. -/
theorem fiveProjectRegimeData_common_bank_money (r : FiveProjectRegime) :
    (fiveProjectRegimeData r).bankMoney = 2 := by
  cases r <;> rfl

/-- Fiduciary expansion adds two issued notes while preserving household
consumption and leaving completion-factor supply at two. -/
theorem fiveProject_fiduciary_sources_and_uses :
    (fiveProjectRegimeData .fiduciaryExpansion).loanableMoney = 4 ∧
    (fiveProjectRegimeData .fiduciaryExpansion).fiduciaryNotesIssued = 2 ∧
    (fiveProjectRegimeData .fiduciaryExpansion).householdFactorsConsumed = 2 ∧
    (fiveProjectRegimeData .fiduciaryExpansion).completionFactorSupply = 2 := by
  decide

/-- The household-transfer scenario assigns two owned money units to a bank
cash transfer, forgoes the household's two-factor consumption, and offers
those factors to production. This accounting theorem does not establish a
deposit claim or purposeful choices. -/
theorem fiveProject_household_transfer_sources_and_uses :
    (fiveProjectRegimeData .householdTransfer).loanableMoney = 4 ∧
    (fiveProjectRegimeData .householdTransfer).householdMoneyTransferred = 2 ∧
    (fiveProjectRegimeData .householdTransfer).householdFactorsConsumed = 0 ∧
    (fiveProjectRegimeData .householdTransfer).householdFactorsOffered = 2 ∧
    (fiveProjectRegimeData .householdTransfer).completionFactorSupply = 4 := by
  decide

/-- The household-transfer funding and factor totals follow for any supplied
household cash endowment and transfer, provided the transfer is exactly two
units and is affordable. This exposes the extra cash premise instead of
deriving it from the household's completion-factor endowment. -/
theorem fiveProject_household_transfer_sources_and_uses_of_two_unit_transfer
    (householdMoneyEndowment householdMoneyTransferred : ℕ)
    (haffordable : householdMoneyTransferred ≤ householdMoneyEndowment)
    (htransfer : householdMoneyTransferred = 2) :
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).loanableMoney = 4 ∧
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).householdMoneyEndowment =
        householdMoneyEndowment ∧
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).householdMoneyTransferred = 2 ∧
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).householdFactorsConsumed = 0 ∧
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).householdFactorsOffered = 2 ∧
    (fiveProjectRegimeDataWithHouseholdMoney householdMoneyEndowment
      householdMoneyTransferred haffordable .householdTransfer).completionFactorSupply = 4 := by
  subst householdMoneyTransferred
  simp [fiveProjectRegimeDataWithHouseholdMoney,
    FiveProjectRegimeData.loanableMoney, FiveProjectRegimeData.completionFactorSupply]

/-- Projected loan-market outcome from a regime's stated source totals. The
state-dependent physical program later clears from the bank's executed
post-transfer money balance. -/
def fiveProjectLoanOutcomeFor (D : FiveProjectRegimeData) : LoanAuctionResult :=
  clearLoanMarket fiveProjectLoanMarket D.loanableMoney

/-- Loan-market outcome for one of the named regimes. -/
def fiveProjectLoanOutcome (r : FiveProjectRegime) : LoanAuctionResult :=
  fiveProjectLoanOutcomeFor (fiveProjectRegimeData r)

/-- Projected factor price from a regime's source totals and offered supply.
This preserves the initial-buffer participation rule; the state-dependent
physical program separately clears from its branch's actual advances and
offered stocks. A loan quote is not evidence of an accepted contract. -/
def fiveProjectFactorPriceFor (D : FiveProjectRegimeData) : Option ℕ :=
  match (fiveProjectLoanOutcomeFor D).quotedRepayment with
  | none => none
  | some quote =>
      ascendingCompletionFactorPrice?
        (fiveProjectLoanOutcomeFor D).funded quote 1 D.completionFactorSupply 3

/-- Factor price in one of the named regimes. -/
def fiveProjectFactorPrice (r : FiveProjectRegime) : Option ℕ :=
  fiveProjectFactorPriceFor (fiveProjectRegimeData r)

/-- A forecast policy maps the already defined credit observation to an
expected completion-factor supply. The policy is behavioral scenario data;
the observation alone does not determine this map. -/
structure FiveProjectForecastPolicy where
  expectedFactorSupply : CreditObservation → ℕ

/-- The fixed witness policy treats an unverified lower loan-rate signal as
evidence that completion-factor supply will rise to four. Verified funding
source signals distinguish a household-transfer observation from fiduciary
credit. This is an explicit forecast assumption, not a conclusion from equal
rates. Under it, the factor-price-one assumption used to form reservation
bids is self-consistent with the entrepreneurs' predicted supply. -/
def fiveProjectFundingCapacityForecast : FiveProjectForecastPolicy where
  expectedFactorSupply
    | .unchangedRate => 2
    | .lowerRate => 4
    | .householdFundsVerified => 4
    | .creditVerified => 2

/-- The information scenario classifies a quote against the baseline
repayment: equality is unchanged, a strictly lower quote is a lower-rate
signal, and higher or absent quotes receive no classification. -/
def fiveProjectRateObservationFromBaseline (baselineRepayment : ℕ)
    (quotedRepayment : Option ℕ) : Option CreditObservation :=
  match quotedRepayment with
  | none => none
  | some repayment =>
      if repayment = baselineRepayment then some .unchangedRate
      else if repayment < baselineRepayment then some .lowerRate
      else none

/-- The named regimes' rate observation relative to the baseline quote six. -/
def fiveProjectRateObservation (r : FiveProjectRegime) : Option CreditObservation :=
  fiveProjectRateObservationFromBaseline 6 (fiveProjectLoanOutcome r).quotedRepayment

/-- Apply one forecast policy to a regime's observed loan quote, then run the
same ascending factor-price mechanism against its predicted supply. -/
def FiveProjectForecastPolicy.factorPriceAtSignal
    (P : FiveProjectForecastPolicy) (r : FiveProjectRegime)
    (signal : CreditObservation) : Option ℕ :=
  match (fiveProjectLoanOutcome r).quotedRepayment with
  | none => none
  | some quote =>
      ascendingCompletionFactorPrice?
        (fiveProjectLoanOutcome r).funded quote 1
        (P.expectedFactorSupply signal) 3

/-- The forecast price under a policy, when the fixed quote has a classified
rate observation. -/
def FiveProjectForecastPolicy.predictedFactorPrice?
    (P : FiveProjectForecastPolicy) (r : FiveProjectRegime) : Option ℕ :=
  (fiveProjectRateObservation r).bind (P.factorPriceAtSignal r)

/-- Under the stated funding-capacity forecast policy, all three regimes
predict factor price one. In the fiduciary regime this forecast differs from
the buffer-based projection computed from the regime's stated supply. -/
theorem fiveProject_funding_capacity_forecast_prices :
    fiveProjectFundingCapacityForecast.predictedFactorPrice? .baseline = some 1 ∧
    fiveProjectFundingCapacityForecast.predictedFactorPrice?
      .fiduciaryExpansion = some 1 ∧
    fiveProjectFundingCapacityForecast.predictedFactorPrice?
      .householdTransfer = some 1 := by
  decide

/-- The household-transfer and fiduciary-expansion scenarios yield the same
observed lower-rate signal but different stated factor supplies and projected
buffer-based prices. The signal therefore does not identify the physical
regime or force the forecast policy. -/
theorem fiveProject_same_lower_rate_different_factor_conditions :
    fiveProjectRateObservation .fiduciaryExpansion = some .lowerRate ∧
    fiveProjectRateObservation .householdTransfer = some .lowerRate ∧
    (fiveProjectRegimeData .fiduciaryExpansion).completionFactorSupply = 2 ∧
    (fiveProjectRegimeData .householdTransfer).completionFactorSupply = 4 ∧
    fiveProjectFactorPrice .fiduciaryExpansion = some 2 ∧
    fiveProjectFactorPrice .householdTransfer = some 1 := by
  decide

/-- A second policy makes a more cautious prediction under an unverified
lower-rate signal. The same observation can then yield a different expected
factor price; beliefs must be supplied as policy data, not inferred from the
signal's equality. -/
def fiveProjectCautiousForecast : FiveProjectForecastPolicy where
  expectedFactorSupply
    | .unchangedRate => 2
    | .lowerRate => 2
    | .householdFundsVerified => 4
    | .creditVerified => 2

theorem fiveProject_same_signal_does_not_fix_forecast_price :
    fiveProjectFundingCapacityForecast.factorPriceAtSignal
      .fiduciaryExpansion .lowerRate = some 1 ∧
    fiveProjectCautiousForecast.factorPriceAtSignal
      .fiduciaryExpansion .lowerRate = some 2 := by
  decide

/-- Recompute loan reservations using a stated forecast factor price, then
clear the resulting loan book against the regime's actual money supply. -/
def fiveProjectReestimatedLoanOutcomeFor (D : FiveProjectRegimeData)
    (forecastFactorPrice : ℕ) : LoanAuctionResult :=
  fiveProjectLoanOutcomeAtFactorPrice D.loanableMoney forecastFactorPrice

/-- Run the same ascending factor clock after recomputing project reservations
at the supplied forecast factor price. -/
def fiveProjectReestimatedFactorPriceFor (D : FiveProjectRegimeData)
    (forecastFactorPrice : ℕ) : Option ℕ :=
  let outcome := fiveProjectReestimatedLoanOutcomeFor D forecastFactorPrice
  match outcome.quotedRepayment with
  | none => none
  | some quote =>
      ascendingCompletionFactorPrice? outcome.funded quote 1
        D.completionFactorSupply 3

/-- Apply a forecast policy to a re-estimated loan outcome. The caller supplies
the observation assigned to that outcome's quote and the factor price used to
form its reservation bids. -/
def FiveProjectForecastPolicy.factorPriceAtReestimatedSignal
    (P : FiveProjectForecastPolicy) (D : FiveProjectRegimeData)
    (forecastFactorPrice : ℕ) (signal : CreditObservation) : Option ℕ :=
  let outcome := fiveProjectReestimatedLoanOutcomeFor D forecastFactorPrice
  match outcome.quotedRepayment with
  | none => none
  | some quote =>
      ascendingCompletionFactorPrice? outcome.funded quote 1
        (P.expectedFactorSupply signal) 3

/-- Classify a re-estimated quote against an explicitly supplied baseline.
This exposes the scenario's observation rule separately from the forecast
policy that interprets the resulting signal. -/
def fiveProjectReestimatedRateObservationFromBaseline
    (D : FiveProjectRegimeData) (forecastFactorPrice baselineRepayment : ℕ) :
    Option CreditObservation :=
  fiveProjectRateObservationFromBaseline baselineRepayment
    (fiveProjectReestimatedLoanOutcomeFor D forecastFactorPrice).quotedRepayment

/-- Projects passing the ordinary buffer and terminal-preference test after
the forecast-indexed loan auction and actual-supply factor clock. -/
def fiveProjectReestimatedFactorDemandFor (D : FiveProjectRegimeData)
    (forecastFactorPrice : ℕ) : Option (List LoanReservationBid) :=
  let outcome := fiveProjectReestimatedLoanOutcomeFor D forecastFactorPrice
  (fiveProjectReestimatedFactorPriceFor D forecastFactorPrice).map fun price =>
    factorDemandingProjectsAt outcome.funded
      (outcome.quotedRepayment.getD 0) price

/-- Projects excluded by the same recomputed market calculation. -/
def fiveProjectReestimatedFactorExcludedFor (D : FiveProjectRegimeData)
    (forecastFactorPrice : ℕ) : Option (List LoanReservationBid) :=
  let outcome := fiveProjectReestimatedLoanOutcomeFor D forecastFactorPrice
  (fiveProjectReestimatedFactorPriceFor D forecastFactorPrice).map fun price =>
    factorExcludedProjectsAt outcome.funded
      (outcome.quotedRepayment.getD 0) price

/-- With the cautious lower-rate forecast, recomputed reservations lower the
fiduciary quote to three. Running the unchanged buffer-based factor auction
against its stated two-unit supply returns price two and demand by projects
zero and one; projects two and three fail the one-unit initial-buffer
participation threshold. This remains a conditional market calculation, not
an executed investment history. -/
theorem fiveProject_cautious_forecast_recomputed_market :
    fiveProjectCautiousForecast.factorPriceAtSignal
      .fiduciaryExpansion .lowerRate = some 2 ∧
    (fiveProjectReestimatedLoanOutcomeFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2).funded.map
        LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    (fiveProjectReestimatedLoanOutcomeFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2).quotedRepayment = some 3 ∧
    fiveProjectReestimatedFactorPriceFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2 = some 2 ∧
    (fiveProjectReestimatedFactorDemandFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2).map
        (List.map LoanReservationBid.borrower) = some [0, 1] ∧
    (fiveProjectReestimatedFactorExcludedFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2).map
        (List.map LoanReservationBid.borrower) = some [2, 3] := by
  decide

/-- Re-estimating the fiduciary loan book at forecast factor price two lowers
its quote from the baseline six to three. Under the explicitly stated
baseline-relative observation rule, that remains a lower-rate signal; the
cautious policy maps that signal to a two-unit supply forecast, consistent
with both the re-estimated factor auction at forecast supply and the auction
at actual fiduciary supply. This is a finite consistency check, not a causal
claim that the quote determines the forecast or that trades were purposeful. -/
theorem fiveProject_cautious_reestimated_quote_forecast_consistent :
    fiveProjectReestimatedRateObservationFromBaseline
      (fiveProjectRegimeData .fiduciaryExpansion) 2 6 = some .lowerRate ∧
    fiveProjectCautiousForecast.factorPriceAtReestimatedSignal
      (fiveProjectRegimeData .fiduciaryExpansion) 2 .lowerRate = some 2 ∧
    fiveProjectReestimatedFactorPriceFor
      (fiveProjectRegimeData .fiduciaryExpansion) 2 = some 2 := by
  decide

/-- The same re-estimated quote and baseline-relative lower-rate observation
support different factor-price forecasts under the two explicitly supplied
policies. The observation therefore does not identify expected factor supply
or a unique forecast price. -/
theorem fiveProject_reestimated_signal_does_not_identify_forecast :
    fiveProjectReestimatedRateObservationFromBaseline
      (fiveProjectRegimeData .fiduciaryExpansion) 2 6 = some .lowerRate ∧
    fiveProjectFundingCapacityForecast.factorPriceAtReestimatedSignal
      (fiveProjectRegimeData .fiduciaryExpansion) 2 .lowerRate = some 1 ∧
    fiveProjectCautiousForecast.factorPriceAtReestimatedSignal
      (fiveProjectRegimeData .fiduciaryExpansion) 2 .lowerRate = some 2 := by
  decide

/-- Verifying the funding source changes the forecast under the fixed policy:
the fiduciary regime predicts the two-factor price of two, while the
household-transfer signal predicts the reserve price with four factors. These
are price predictions under the policy, not purposeful action evidence. -/
theorem fiveProject_verified_source_forecast_prices :
    fiveProjectFundingCapacityForecast.factorPriceAtSignal
      .fiduciaryExpansion .creditVerified = some 2 ∧
    fiveProjectFundingCapacityForecast.factorPriceAtSignal
      .householdTransfer .householdFundsVerified = some 1 := by
  decide

/-- Once the fiduciary source is verified, the stated forecast policy predicts
the two-unit factor price. At the fixed loan quote, the two marginal borrowers
fail the initial-buffer participation threshold. The executed funding branch
also leaves each with two money units, so the threshold failure does not imply
physical unaffordability at the later purchase node. Neither result establishes
a full purposeful investment history. -/
theorem fiveProject_verified_source_fails_marginal_buffer_test :
    fiveProjectFundingCapacityForecast.factorPriceAtSignal
      .fiduciaryExpansion .creditVerified = some 2 ∧
    ∀ entrepreneur, 2 ≤ entrepreneur.val → entrepreneur.val < 4 →
      ¬ projectPassesCashBufferAndReturnTestAt
        (fiveProjectLoanBid entrepreneur) 4 2 := by
  refine ⟨by decide, ?_⟩
  intro entrepreneur hafterTwo hbeforeFour
  exact (fiveProject_marginal_projects_fail_buffer_bound_at_squeezed_price
    entrepreneur hafterTwo hbeforeFour).2

/-- Projects that pass the projected buffer and terminal-money conditions at
the regime's derived clearing price. Physical execution separately checks
current holdings for each matched transfer. -/
def fiveProjectFactorDemandFor (D : FiveProjectRegimeData) :
    Option (List LoanReservationBid) :=
  (fiveProjectFactorPriceFor D).map fun price =>
    factorDemandingProjectsAt (fiveProjectLoanOutcomeFor D).funded
      ((fiveProjectLoanOutcomeFor D).quotedRepayment.getD 0) price

/-- Funded projects blocked at the regime's derived factor price. -/
def fiveProjectFactorExcludedFor (D : FiveProjectRegimeData) :
    Option (List LoanReservationBid) :=
  (fiveProjectFactorPriceFor D).map fun price =>
    factorExcludedProjectsAt (fiveProjectLoanOutcomeFor D).funded
      ((fiveProjectLoanOutcomeFor D).quotedRepayment.getD 0) price

/-- A projected final-customer schedule assigns forecast output at one money
unit per unit, subject to the stated forty-unit budget. The physical program
generates purchases from output and cash remaining on its branch. -/
def fiveProjectCustomerPurchasePlanFor (D : FiveProjectRegimeData) :
    Option (List (Fin 5 × ℕ)) :=
  (fiveProjectFactorDemandFor D).map (customerUnitPurchasePlan 40)

/-- Planned customer revenue computed from the purchase schedule. The record
does not transfer output or money. -/
def fiveProjectCustomerRevenuePlanFor (D : FiveProjectRegimeData) : Option ℕ :=
  (fiveProjectCustomerPurchasePlanFor D).map customerUnitRevenuePlan

/-- The corresponding outcomes for one of the three named comparisons. -/
def fiveProjectFactorDemand (r : FiveProjectRegime) : Option (List LoanReservationBid) :=
  fiveProjectFactorDemandFor (fiveProjectRegimeData r)

def fiveProjectFactorExcluded (r : FiveProjectRegime) : Option (List LoanReservationBid) :=
  fiveProjectFactorExcludedFor (fiveProjectRegimeData r)

def fiveProjectCustomerPurchasePlan (r : FiveProjectRegime) : Option (List (Fin 5 × ℕ)) :=
  fiveProjectCustomerPurchasePlanFor (fiveProjectRegimeData r)

def fiveProjectCustomerRevenuePlan (r : FiveProjectRegime) : Option ℕ :=
  fiveProjectCustomerRevenuePlanFor (fiveProjectRegimeData r)

/-- Borrower identities in an optional result list. -/
def borrowerIdentities? (xs : Option (List LoanReservationBid)) : Option (List (Fin 5)) :=
  xs.map (List.map LoanReservationBid.borrower)

/-- In the fiduciary scenario, the loan auction funds four borrowers at quote
four and the explicit forecast policy gives them a factor price of one. Under
the existing terminal-money preference, all four prefer the forecast plan to
idling. The initial-buffer participation rule at price two excludes borrowers
two and three even though the physical executor records two money units for
each after the advances. Early input production and the investment actions
remain outside this projected market calculation. -/
theorem fiveProject_fiduciary_forecast_preference_and_supply_squeeze :
    (fiveProjectLoanOutcome .fiduciaryExpansion).quotedRepayment = some 4 ∧
    fiveProjectFundingCapacityForecast.predictedFactorPrice?
      .fiduciaryExpansion = some 1 ∧
    fiveProjectFactorPrice .fiduciaryExpansion = some 2 ∧
    (∀ entrepreneur, entrepreneur.val < 4 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 4 1)
        (fiveProjectIdleTerminalMoney entrepreneur)) ∧
    (∀ entrepreneur, 2 ≤ entrepreneur.val → entrepreneur.val < 4 →
      fiveProjectCashBuffer entrepreneur = 1 ∧
        ¬ projectPassesCashBufferAndReturnTestAt
          (fiveProjectLoanBid entrepreneur) 4 2) ∧
    borrowerIdentities? (fiveProjectFactorExcluded .fiduciaryExpansion) = some [2, 3] := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, by decide⟩
  · intro entrepreneur hfunded
    exact fiveProject_expansion_funded_projects_prefer_forecast_plan
      entrepreneur hfunded
  · intro entrepreneur hafterTwo hbeforeFour
    exact fiveProject_marginal_projects_fail_buffer_bound_at_squeezed_price
      entrepreneur hafterTwo hbeforeFour

/-- The two borrowers funded in the baseline regime strictly prefer their
forecast-price project at the quoted repayment to preserving their cash
buffers. This is a preference comparison derived from the reservation
threshold; it does not assert that a loan or production action was enacted. -/
theorem fiveProject_baseline_funded_projects_prefer_forecast_plan :
    ∀ entrepreneur, entrepreneur.val < 2 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 6 1)
        (fiveProjectIdleTerminalMoney entrepreneur) := by
  intro entrepreneur hfunded
  apply (fiveProject_project_preferred_iff_below_reservation entrepreneur 6).2
  unfold fiveProjectReservationRepayment fiveProjectReservationRepaymentAtFactorPrice
    projectedReservationRepayment fiveProjectOutput
  omega

/-- The four borrowers funded in the household-transfer scenario strictly prefer
their forecast-price projects at the quoted repayment to preserving their
cash buffers. This follows from the same preference threshold as the
fiduciary case; the theorem does not establish that the household cash
transfer was purposeful or that a project action was enacted. -/
theorem fiveProject_household_transfer_funded_projects_prefer_forecast_plan :
    ∀ entrepreneur, entrepreneur.val < 4 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 4 1)
        (fiveProjectIdleTerminalMoney entrepreneur) := by
  intro entrepreneur hfunded
  exact fiveProject_expansion_funded_projects_prefer_forecast_plan
    entrepreneur hfunded

/-- Reservation preferences for all three named funding regimes. The common
forecast price and stable terminal-money order generate the funded-project
preferences; the result remains a preference comparison rather than an
executed ActionFrame history. -/
theorem fiveProject_named_funded_projects_prefer_forecast_plan :
    (∀ entrepreneur, entrepreneur.val < 2 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 6 1)
        (fiveProjectIdleTerminalMoney entrepreneur)) ∧
    (∀ entrepreneur, entrepreneur.val < 4 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 4 1)
        (fiveProjectIdleTerminalMoney entrepreneur)) ∧
    (∀ entrepreneur, entrepreneur.val < 4 →
      terminalMoneyPreferred
        (fiveProjectTerminalMoney entrepreneur 4 1)
        (fiveProjectIdleTerminalMoney entrepreneur)) := by
  exact ⟨fiveProject_baseline_funded_projects_prefer_forecast_plan,
    fiveProject_expansion_funded_projects_prefer_forecast_plan,
    fiveProject_household_transfer_funded_projects_prefer_forecast_plan⟩

/-- Baseline market calculation: two funded projects, quote six, factor price
one, two projects eligible for the factor, and planned customer revenue of
seventeen. It records no executed trades or completed production. -/
theorem fiveProject_baseline_market_calculation :
    (fiveProjectLoanOutcome .baseline).fundingCapacity = 2 ∧
    (fiveProjectLoanOutcome .baseline).quotedRepayment = some 6 ∧
    fiveProjectFactorPrice .baseline = some 1 ∧
    borrowerIdentities? (fiveProjectFactorDemand .baseline) = some [0, 1] ∧
    borrowerIdentities? (fiveProjectFactorExcluded .baseline) = some [] ∧
    fiveProjectCustomerRevenuePlan .baseline = some 17 := by
  decide

/-- Fiduciary-credit market calculation: four projects are funded at quote
four; factor price rises to two, two projects meet the factor eligibility
conditions, two are excluded, and planned customer revenue is seventeen. It
records no executed trades or completed production. -/
theorem fiveProject_fiduciary_market_calculation :
    (fiveProjectLoanOutcome .fiduciaryExpansion).fundingCapacity = 4 ∧
    (fiveProjectLoanOutcome .fiduciaryExpansion).quotedRepayment = some 4 ∧
    fiveProjectFactorPrice .fiduciaryExpansion = some 2 ∧
    borrowerIdentities? (fiveProjectFactorDemand .fiduciaryExpansion) = some [0, 1] ∧
    borrowerIdentities? (fiveProjectFactorExcluded .fiduciaryExpansion) = some [2, 3] ∧
    fiveProjectCustomerRevenuePlan .fiduciaryExpansion = some 17 := by
  decide

/-- Household-transfer market calculation: two units of household money and
two household factors specified as transferred/offered fund four projects at
repayment four and factor price one; all four are factor-eligible and planned
customer revenue is thirty. It proves neither purposeful saving nor executed
transfers or completed production. -/
theorem fiveProject_household_transfer_market_calculation :
    (fiveProjectLoanOutcome .householdTransfer).fundingCapacity = 4 ∧
    (fiveProjectLoanOutcome .householdTransfer).quotedRepayment = some 4 ∧
    fiveProjectFactorPrice .householdTransfer = some 1 ∧
    borrowerIdentities? (fiveProjectFactorDemand .householdTransfer) = some [0, 1, 2, 3] ∧
    borrowerIdentities? (fiveProjectFactorExcluded .householdTransfer) = some [] ∧
    fiveProjectCustomerRevenuePlan .householdTransfer = some 30 := by
  decide

/-- A separate boundary case changes only supplier stock to four while
preserving the fiduciary regime's issued funds and household consumption. -/
def fiveProject_fiduciaryWithSufficientFactors : FiveProjectRegimeData :=
  (fiveProjectRegimeData .fiduciaryExpansion).withSupplierFactorStock 4

/-- With enough stated completion inputs, the same four funded projects clear
at the reserve price, all four satisfy the modeled factor eligibility tests,
and the customer purchase plan assigns their thirty output units. This
boundary is a market calculation, not an executed ActionFrame history. -/
theorem fiveProject_expansion_with_sufficient_real_inputs_succeeds :
    fiveProject_fiduciaryWithSufficientFactors.loanableMoney = 4 ∧
    fiveProject_fiduciaryWithSufficientFactors.fiduciaryNotesIssued = 2 ∧
    fiveProject_fiduciaryWithSufficientFactors.householdFactorsConsumed = 2 ∧
    fiveProject_fiduciaryWithSufficientFactors.completionFactorSupply = 4 ∧
    (fiveProjectLoanOutcomeFor fiveProject_fiduciaryWithSufficientFactors).fundingCapacity = 4 ∧
    (fiveProjectLoanOutcomeFor fiveProject_fiduciaryWithSufficientFactors).quotedRepayment =
      some 4 ∧
    fiveProjectFactorPriceFor fiveProject_fiduciaryWithSufficientFactors = some 1 ∧
    borrowerIdentities? (fiveProjectFactorDemandFor
      fiveProject_fiduciaryWithSufficientFactors) = some [0, 1, 2, 3] ∧
    borrowerIdentities? (fiveProjectFactorExcludedFor
      fiveProject_fiduciaryWithSufficientFactors) = some [] ∧
    fiveProjectCustomerRevenuePlanFor fiveProject_fiduciaryWithSufficientFactors = some 30 := by
  decide

end Praxeology

end
