/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Market

/-!
# Finite loan and completion-factor auctions

This module specifies deterministic market rules as scenario data rather than
adding them to `ActionFrame`. A standardized loan auction funds a prefix of a
descending reservation-repayment book and quotes the first rejected bid. The
completion-factor clock starts at the supplier's reserve price and increments
by one until affordable and strictly profitable demand fits supply.

The five-project witness derives its reservation repayments from projected
unit-price output proceeds less the forecast completion-factor cost. The
module provides market and price calculations only; it does not infer that a
project is purposeful or that an entrepreneur holds the forecast.
-/

@[expose] public section

namespace Praxeology

/-- A borrower's maximum promised repayment for one standardized loan. -/
structure LoanReservationBid where
  borrower : Fin 5
  reservationRepayment : ℕ
  deriving DecidableEq, Repr

namespace LoanReservationBid

/-- Descending repayment rank; equal bids are ordered by borrower index. -/
def precedes (left right : LoanReservationBid) : Prop :=
  right.reservationRepayment ≤ left.reservationRepayment ∧
    (left.reservationRepayment = right.reservationRepayment →
      left.borrower.val < right.borrower.val)

instance precedesDecidable (left right : LoanReservationBid) :
    Decidable (precedes left right) := by
  unfold precedes
  infer_instance

end LoanReservationBid

/-- A standardized-principal loan market with a deterministically ranked bid
book. The order records the market's descending-price and tie-breaking rule.
-/
structure FiniteLoanMarket where
  principal : ℕ
  principal_positive : 0 < principal
  bids : List LoanReservationBid
  ranked : bids.Pairwise LoanReservationBid.precedes
  one_bid_per_borrower : (bids.map LoanReservationBid.borrower).Nodup

/-- Result of allocating available principal across a ranked loan book. The
first rejected reservation is the quoted repayment; if there is no rejected
bid, the market returns no marginal-rejection quote. -/
structure LoanAuctionResult where
  fundingCapacity : ℕ
  funded : List LoanReservationBid
  rejected : List LoanReservationBid
  quotedRepayment : Option ℕ
  deriving DecidableEq, Repr

/-- Run the standardized loan auction using the lender's actual money balance.
Each funded loan consumes exactly `principal` units. -/
def clearLoanMarket (market : FiniteLoanMarket) (availableMoney : ℕ) :
    LoanAuctionResult :=
  let capacity := availableMoney / market.principal
  let rejected := market.bids.drop capacity
  { fundingCapacity := capacity
    funded := market.bids.take capacity
    rejected := rejected
    quotedRepayment := rejected.head?.map LoanReservationBid.reservationRepayment }

/-- Clearing partitions the original ranked bid book into its funded prefix
and rejected suffix. -/
theorem clearLoanMarket_funded_append_rejected (market : FiniteLoanMarket)
    (availableMoney : ℕ) :
    (clearLoanMarket market availableMoney).funded ++
        (clearLoanMarket market availableMoney).rejected = market.bids := by
  simp [clearLoanMarket, List.take_append_drop]

/-- The marginal quote is exactly the repayment on the first rejected bid;
when no bid is rejected, this auction rule supplies no quote. -/
theorem clearLoanMarket_quote_is_first_rejected (market : FiniteLoanMarket)
    (availableMoney : ℕ) :
    (clearLoanMarket market availableMoney).quotedRepayment =
      (clearLoanMarket market availableMoney).rejected.head?.map
        LoanReservationBid.reservationRepayment := by
  rfl

/-- Contract terms assigned to one funded borrower by the standardized loan
auction. This records principal and promised repayment separately; it does not
assert that an advance or later repayment has physically occurred. -/
structure FundedLoanTerms where
  borrower : Fin 5
  principal : ℕ
  principal_positive : 0 < principal
  promisedRepayment : ℕ
  deriving DecidableEq, Repr

/-- When the loan auction has a marginal-rejection quote, form one contract
terms record for each funded borrower. The common promised repayment is the
quoted amount and principal is the market's standardized amount. -/
def clearLoanTerms? (market : FiniteLoanMarket) (availableMoney : ℕ) :
    Option (List FundedLoanTerms) :=
  let result := clearLoanMarket market availableMoney
  result.quotedRepayment.map fun promisedRepayment =>
    result.funded.map fun bid =>
      { borrower := bid.borrower
        principal := market.principal
        principal_positive := market.principal_positive
        promisedRepayment := promisedRepayment }

/-- Equal whole-loan funding capacity leaves the complete auction result
unchanged. This follows directly from the existing clearing rule. -/
theorem clearLoanMarket_eq_of_equal_capacity (market : FiniteLoanMarket)
    (money₁ money₂ : ℕ)
    (hcapacity : money₁ / market.principal = money₂ / market.principal) :
    clearLoanMarket market money₁ = clearLoanMarket market money₂ := by
  simp [clearLoanMarket, hcapacity]

/-- Physical output sold at one money unit per unit, net of the forecast
completion-factor purchase at the stated price. -/
def projectedReservationRepayment (projectedOutput forecastFactorPrice : ℕ) : ℕ :=
  projectedOutput - forecastFactorPrice

/-- Project outputs in the fixed witness, ordered from highest to lowest. -/
def fiveProjectOutput (entrepreneur : Fin 5) : ℕ := 9 - entrepreneur.val

/-- Reservation repayment at a stated forecast factor price, derived from
projected unit-price output proceeds less the completion-factor cost. -/
def fiveProjectReservationRepaymentAtFactorPrice
    (entrepreneur : Fin 5) (forecastFactorPrice : ℕ) : ℕ :=
  projectedReservationRepayment (fiveProjectOutput entrepreneur) forecastFactorPrice

/-- Entrepreneur cash buffers in the specified five-project scenario. -/
def fiveProjectCashBuffer (entrepreneur : Fin 5) : ℕ :=
  if entrepreneur.val < 2 then 3 else 1

/-- The entrepreneurs' reservation repayments are derived from projected
sale proceeds and the common forecast factor price of one. -/
def fiveProjectReservationRepayment (entrepreneur : Fin 5) : ℕ :=
  fiveProjectReservationRepaymentAtFactorPrice entrepreneur 1

/-- The loan-market bid generated by one entrepreneur under a stated forecast
factor price. -/
def fiveProjectLoanBidAtFactorPrice (forecastFactorPrice : ℕ)
    (entrepreneur : Fin 5) : LoanReservationBid :=
  { borrower := entrepreneur
    reservationRepayment :=
      fiveProjectReservationRepaymentAtFactorPrice entrepreneur forecastFactorPrice }

/-- The bid record generated by one entrepreneur's projected reservation. -/
def fiveProjectLoanBid (entrepreneur : Fin 5) : LoanReservationBid :=
  fiveProjectLoanBidAtFactorPrice 1 entrepreneur

/-- Projected terminal money after output sales, completion-factor payment, and
promised repayment. This projection starts from the pre-existing cash buffer;
it does not track an enacted principal advance or the principal's earlier
physical use, so it is not the inventory at the later purchase node. -/
def fiveProjectTerminalMoney (entrepreneur : Fin 5)
    (promisedRepayment factorPrice : ℕ) : ℤ :=
  (fiveProjectCashBuffer entrepreneur : ℤ) +
    (fiveProjectOutput entrepreneur : ℤ) - (factorPrice : ℤ) -
      (promisedRepayment : ℤ)

/-- The outside option preserves the entrepreneur's initial cash buffer. -/
def fiveProjectIdleTerminalMoney (entrepreneur : Fin 5) : ℤ :=
  fiveProjectCashBuffer entrepreneur

/-- Stable ordinal preference over terminal money: more terminal money is
strictly preferred. This is a scenario preference rule, not an ActionFrame
axiom or a claim about every agent. -/
def terminalMoneyPreferred (preferred other : ℤ) : Prop := other < preferred

/-- The scenario's terminal-money relation inherits asymmetry from the strict
integer order; no further preference axiom is needed for this comparison. -/
theorem terminalMoneyPreferred_asymm {preferred other : ℤ}
    (h : terminalMoneyPreferred preferred other) :
    ¬ terminalMoneyPreferred other preferred := by
  unfold terminalMoneyPreferred at *
  exact (lt_asymm h)

/-- The terminal-money relation is transitive because integer strict order is
transitive. -/
theorem terminalMoneyPreferred_trans {a b c : ℤ}
    (hab : terminalMoneyPreferred a b) (hbc : terminalMoneyPreferred b c) :
    terminalMoneyPreferred a c := by
  unfold terminalMoneyPreferred at *
  exact lt_trans hbc hab

/-- No terminal holding is strictly preferred to itself under this order. -/
theorem terminalMoneyPreferred_irrefl (a : ℤ) :
    ¬ terminalMoneyPreferred a a := by
  unfold terminalMoneyPreferred
  exact lt_irrefl a

/-- At the forecast factor price, the reservation repayment leaves the
entrepreneur exactly at the idle terminal-money holding. -/
theorem fiveProjectReservation_is_break_even (entrepreneur : Fin 5) :
    fiveProjectTerminalMoney entrepreneur
        (fiveProjectReservationRepayment entrepreneur) 1 =
      fiveProjectIdleTerminalMoney entrepreneur := by
  unfold fiveProjectTerminalMoney fiveProjectIdleTerminalMoney
    fiveProjectReservationRepayment fiveProjectReservationRepaymentAtFactorPrice
    projectedReservationRepayment
    fiveProjectOutput
  omega

/-- Repayment below the derived reservation makes the planned project
strictly preferred to preserving the cash buffer. -/
theorem fiveProject_below_reservation_preferred (entrepreneur : Fin 5)
    (repayment : ℕ)
    (hrepayment : repayment < fiveProjectReservationRepayment entrepreneur) :
    terminalMoneyPreferred
      (fiveProjectTerminalMoney entrepreneur repayment 1)
      (fiveProjectIdleTerminalMoney entrepreneur) := by
  unfold terminalMoneyPreferred fiveProjectTerminalMoney
    fiveProjectIdleTerminalMoney fiveProjectReservationRepayment
    fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
    fiveProjectOutput at *
  omega

/-- Repayment above the derived reservation makes preserving the cash buffer
strictly preferred to the planned project. -/
theorem fiveProject_above_reservation_rejected (entrepreneur : Fin 5)
    (repayment : ℕ)
    (hrepayment : fiveProjectReservationRepayment entrepreneur < repayment) :
    terminalMoneyPreferred
      (fiveProjectIdleTerminalMoney entrepreneur)
      (fiveProjectTerminalMoney entrepreneur repayment 1) := by
  unfold terminalMoneyPreferred fiveProjectTerminalMoney
    fiveProjectIdleTerminalMoney fiveProjectReservationRepayment
    fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
    fiveProjectOutput at *
  omega

/-- The quoted reservation is the exact threshold induced by the model's
terminal-money preference: at the forecast factor price, the planned project
is strictly preferred to idling precisely below this repayment. -/
theorem fiveProject_project_preferred_iff_below_reservation
    (entrepreneur : Fin 5) (repayment : ℕ) :
    terminalMoneyPreferred
      (fiveProjectTerminalMoney entrepreneur repayment 1)
      (fiveProjectIdleTerminalMoney entrepreneur) ↔
    repayment < fiveProjectReservationRepayment entrepreneur := by
  unfold terminalMoneyPreferred fiveProjectTerminalMoney
    fiveProjectIdleTerminalMoney fiveProjectReservationRepayment
    fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
    fiveProjectOutput
  omega

/-- At any forecast factor price, a repayment is strictly preferred to idling
exactly when the repayment plus factor cost is below projected sale proceeds;
the reservation formula is derived from that inequality. -/
theorem fiveProject_project_preferred_iff_below_reservation_at_factor_price
    (entrepreneur : Fin 5) (repayment forecastFactorPrice : ℕ) :
    terminalMoneyPreferred
      (fiveProjectTerminalMoney entrepreneur repayment forecastFactorPrice)
      (fiveProjectIdleTerminalMoney entrepreneur) ↔
    repayment <
      fiveProjectReservationRepaymentAtFactorPrice entrepreneur forecastFactorPrice := by
  unfold terminalMoneyPreferred fiveProjectTerminalMoney fiveProjectIdleTerminalMoney
    fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
    fiveProjectOutput
  omega

/-- A factor-price increase weakly lowers every project's derived reservation
repayment, holding projected output fixed. -/
theorem fiveProjectReservationRepaymentAtFactorPrice_antitone
    (entrepreneur : Fin 5) {price₁ price₂ : ℕ} (hprice : price₁ ≤ price₂) :
    fiveProjectReservationRepaymentAtFactorPrice entrepreneur price₂ ≤
      fiveProjectReservationRepaymentAtFactorPrice entrepreneur price₁ := by
  unfold fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
  exact Nat.sub_le_sub_left hprice (fiveProjectOutput entrepreneur)

private theorem fiveProjectLoanBidAtFactorPrice_precedes
    (forecastFactorPrice : ℕ) {earlier later : Fin 5}
    (horder : earlier.val < later.val) :
    LoanReservationBid.precedes
      (fiveProjectLoanBidAtFactorPrice forecastFactorPrice earlier)
      (fiveProjectLoanBidAtFactorPrice forecastFactorPrice later) := by
  constructor
  · change fiveProjectReservationRepaymentAtFactorPrice later forecastFactorPrice ≤
      fiveProjectReservationRepaymentAtFactorPrice earlier forecastFactorPrice
    unfold fiveProjectReservationRepaymentAtFactorPrice projectedReservationRepayment
      fiveProjectOutput
    omega
  · intro _
    exact horder

/-- Ranked loan book for the five-project witness. Its list order implements
the borrower-index tie rule; the current reservation values are strictly
descending. -/
def fiveProjectLoanBidsAtFactorPrice (forecastFactorPrice : ℕ) :
    List LoanReservationBid :=
  (List.finRange 5).map (fiveProjectLoanBidAtFactorPrice forecastFactorPrice)

/-- Standardized-principal loan market using reservations derived at the
stated forecast factor price. The fixed witness below is its price-one case. -/
def fiveProjectLoanMarketAtFactorPrice (forecastFactorPrice : ℕ) : FiniteLoanMarket where
  principal := 1
  principal_positive := by decide
  bids := fiveProjectLoanBidsAtFactorPrice forecastFactorPrice
  ranked := by
    rw [fiveProjectLoanBidsAtFactorPrice, List.pairwise_map]
    rw [List.pairwise_iff_get]
    intro i j hij
    rw [List.get_finRange, List.get_finRange]
    exact fiveProjectLoanBidAtFactorPrice_precedes forecastFactorPrice
      (by simpa using hij)
  one_bid_per_borrower := by
    change ((List.finRange 5).map fun entrepreneur => entrepreneur).Nodup
    simpa using List.nodup_finRange 5

/-- The concrete witness uses the reservations derived under forecast factor
price one. -/
def fiveProjectLoanMarket : FiniteLoanMarket :=
  fiveProjectLoanMarketAtFactorPrice 1

/-- Loan-auction result when reservations are recomputed at a stated forecast
factor price. -/
def fiveProjectLoanOutcomeAtFactorPrice
    (availableMoney forecastFactorPrice : ℕ) : LoanAuctionResult :=
  clearLoanMarket (fiveProjectLoanMarketAtFactorPrice forecastFactorPrice) availableMoney

/-- The projected-output and forecast-cost rule gives reservations
`8, 7, 6, 5, 4` in the stated entrepreneur order. -/
theorem five_project_reservation_table :
    (List.finRange 5).map fiveProjectReservationRepayment = [8, 7, 6, 5, 4] := by
  decide

/-- Recomputing reservations at factor price two lowers each project's
reservation repayment by one in this witness. -/
theorem five_project_price_two_reservation_table :
    (List.finRange 5).map
      (fun entrepreneur =>
        fiveProjectReservationRepaymentAtFactorPrice entrepreneur 2) =
      [7, 6, 5, 4, 3] := by
  decide

/-- With two actual money units and unit principal, the first two borrowers
are funded and borrower two supplies the marginal rejected quote of six. -/
theorem five_project_baseline_loan_auction :
    let result := clearLoanMarket fiveProjectLoanMarket 2
    result.fundingCapacity = 2 ∧
      result.funded.map LoanReservationBid.borrower = [0, 1] ∧
      result.rejected.map LoanReservationBid.borrower = [2, 3, 4] ∧
      result.quotedRepayment = some 6 := by
  decide

/-- After four actual money units are available, four borrowers are funded
and the fifth borrower's rejected bid quotes repayment four. -/
theorem five_project_expanded_loan_auction :
    let result := clearLoanMarket fiveProjectLoanMarket 4
    result.fundingCapacity = 4 ∧
      result.funded.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
      result.rejected.map LoanReservationBid.borrower = [4] ∧
      result.quotedRepayment = some 4 := by
  decide

/-- At forecast factor price two, the same four-unit loan supply still funds
four projects, but the fifth reservation now quotes repayment three. -/
theorem five_project_price_two_loan_auction :
    let result := fiveProjectLoanOutcomeAtFactorPrice 4 2
    result.fundingCapacity = 4 ∧
      result.funded.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
      result.rejected.map LoanReservationBid.borrower = [4] ∧
      result.quotedRepayment = some 3 := by
  decide

/-- A one-unit increase cannot change entry when each standardized loan
requires two units. The same auction definition therefore leaves the funded
borrowers and marginal-rejection quote unchanged below that capacity step. -/
def fiveProjectTwoUnitPrincipalMarket : FiniteLoanMarket where
  principal := 2
  principal_positive := by decide
  bids := fiveProjectLoanMarket.bids
  ranked := fiveProjectLoanMarket.ranked
  one_bid_per_borrower := fiveProjectLoanMarket.one_bid_per_borrower

theorem two_unit_principal_subunit_expansion_no_entry_or_quote_change :
    (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 2).funded.map
        LoanReservationBid.borrower =
      (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 3).funded.map
        LoanReservationBid.borrower ∧
    (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 2).quotedRepayment =
      (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 3).quotedRepayment := by
  have hcapacity : 2 / fiveProjectTwoUnitPrincipalMarket.principal =
      3 / fiveProjectTwoUnitPrincipalMarket.principal := by
    norm_num [fiveProjectTwoUnitPrincipalMarket]
  have hresult := clearLoanMarket_eq_of_equal_capacity
    fiveProjectTwoUnitPrincipalMarket 2 3 hcapacity
  rw [hresult]
  decide

/-- Raising funds from four to five does not change the result when each
standardized principal requires two units. Both balances still authorize two
loans, so this calibration changes neither entry nor the marginal quote. -/
theorem two_unit_principal_four_to_five_no_entry_or_quote_change :
    (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 4).funded.map
        LoanReservationBid.borrower =
      (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 5).funded.map
        LoanReservationBid.borrower ∧
    (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 4).quotedRepayment =
      (clearLoanMarket fiveProjectTwoUnitPrincipalMarket 5).quotedRepayment := by
  have hcapacity : 4 / fiveProjectTwoUnitPrincipalMarket.principal =
      5 / fiveProjectTwoUnitPrincipalMarket.principal := by
    norm_num [fiveProjectTwoUnitPrincipalMarket]
  have hresult := clearLoanMarket_eq_of_equal_capacity
    fiveProjectTwoUnitPrincipalMarket 4 5 hcapacity
  rw [hresult]
  decide

/-- The current project filter passes a funded project only when its initial
cash buffer covers the factor price and projected unit-price receipts
strictly exceed the loan repayment plus that factor cost. This is the model's
initial-buffer participation rule, distinct from the physical affordability
check against inventory at the purchase node. -/
def projectPassesCashBufferAndReturnTestAt (bid : LoanReservationBid)
    (quotedRepayment price : ℕ) : Prop :=
  price ≤ fiveProjectCashBuffer bid.borrower ∧
    terminalMoneyPreferred
      (fiveProjectTerminalMoney bid.borrower quotedRepayment price)
      (fiveProjectIdleTerminalMoney bid.borrower)

instance projectPassesCashBufferAndReturnTestAtDecidable (bid : LoanReservationBid)
    (quotedRepayment price : ℕ) :
    Decidable (projectPassesCashBufferAndReturnTestAt bid quotedRepayment price) := by
  unfold projectPassesCashBufferAndReturnTestAt terminalMoneyPreferred
  infer_instance

/-- Passing the cash-buffer and return test is exactly the initial-buffer
bound together with the same terminal-money preference used to derive loan
reservations. This is a projected eligibility condition, not physical
completion or an enacted investment choice. -/
theorem projectPassesCashBufferAndReturnTestAt_iff_terminal_preference
    (bid : LoanReservationBid) (quotedRepayment price : ℕ) :
    projectPassesCashBufferAndReturnTestAt bid quotedRepayment price ↔
      price ≤ fiveProjectCashBuffer bid.borrower ∧
        quotedRepayment + price < fiveProjectOutput bid.borrower := by
  unfold projectPassesCashBufferAndReturnTestAt terminalMoneyPreferred fiveProjectTerminalMoney
    fiveProjectIdleTerminalMoney
  unfold fiveProjectOutput
  omega

/-- At the forecast factor price of one, each borrower funded by the
four-loan expansion strictly prefers the project plan at quote four to
preserving the initial cash buffer. This is a terminal-preference comparison,
not evidence of an enacted purposeful action. -/
theorem fiveProject_expansion_funded_projects_prefer_forecast_plan
    (entrepreneur : Fin 5) (hfunded : entrepreneur.val < 4) :
    terminalMoneyPreferred
      (fiveProjectTerminalMoney entrepreneur 4 1)
      (fiveProjectIdleTerminalMoney entrepreneur) := by
  rw [fiveProject_project_preferred_iff_below_reservation]
  unfold fiveProjectReservationRepayment fiveProjectReservationRepaymentAtFactorPrice
    projectedReservationRepayment
    fiveProjectOutput
  omega

/-- Entrepreneurs two and three each have a one-unit pre-existing cash buffer,
so that buffer does not meet the model's two-unit participation threshold.
This buffer-bound result is separate from physical affordability at the
purchase node, where current holdings are checked by the interpreter. -/
theorem fiveProject_marginal_projects_fail_buffer_bound_at_squeezed_price
    (entrepreneur : Fin 5) (hafterTwo : 2 ≤ entrepreneur.val)
    (hbeforeFour : entrepreneur.val < 4) :
    fiveProjectCashBuffer entrepreneur = 1 ∧
    ¬ projectPassesCashBufferAndReturnTestAt
      (fiveProjectLoanBid entrepreneur) 4 2 := by
  have hbuffer : fiveProjectCashBuffer entrepreneur = 1 := by
    simp [fiveProjectCashBuffer, show ¬ entrepreneur.val < 2 by omega]
  constructor
  · exact hbuffer
  · intro hcomplete
    have hprice := hcomplete.1
    change 2 ≤ fiveProjectCashBuffer entrepreneur at hprice
    rw [hbuffer] at hprice
    omega

/-- A funded entrepreneur demands one completion factor at price `p` when the
buffer covers the purchase and projected proceeds strictly exceed repayment
plus the factor cost. -/
def completionFactorDemandAt (funded : List LoanReservationBid)
    (quotedRepayment price : ℕ) : ℕ :=
  (funded.filter fun bid => decide
    (projectPassesCashBufferAndReturnTestAt bid quotedRepayment price)).length

/-- Projects whose cash and strictly-positive projected-return constraints
permit purchase at the quoted completion-factor price. At a clearing price, these demands fit the
offered supply by construction of the ascending clock. -/
def factorDemandingProjectsAt (funded : List LoanReservationBid)
    (quotedRepayment price : ℕ) : List LoanReservationBid :=
  funded.filter fun bid => decide
    (projectPassesCashBufferAndReturnTestAt bid quotedRepayment price)

/-- Funded projects excluded from completion at the clearing price. -/
def factorExcludedProjectsAt (funded : List LoanReservationBid)
    (quotedRepayment price : ℕ) : List LoanReservationBid :=
  funded.filter fun bid => !(decide
    (projectPassesCashBufferAndReturnTestAt bid quotedRepayment price))

/-- Prices visited by an integer ascending clock. The endpoint is at least one
above the greatest buffer, so demand is zero there under the affordability
rule. -/
def completionFactorPriceCandidates (reservePrice greatestBuffer : ℕ) : List ℕ :=
  let upper := max reservePrice (greatestBuffer + 1)
  (List.range (upper - reservePrice + 1)).map (fun offset => reservePrice + offset)

/-- Return the first ascending integer price at which affordable,
strictly profitable demand fits the offered supply. The list order resolves
the price deterministically. -/
def ascendingCompletionFactorPrice? (funded : List LoanReservationBid)
    (quotedRepayment reservePrice supply greatestBuffer : ℕ) : Option ℕ :=
  (completionFactorPriceCandidates reservePrice greatestBuffer).find?
    (fun price => decide
      (completionFactorDemandAt funded quotedRepayment price ≤ supply))

/-- Current-node factor eligibility uses the entrepreneur's actual money at
the market node and projected output receipts. It requires current cash to
cover the purchase and applies the existing terminal-money preference to the
projected outcome: current cash plus output, less factor cost and repayment,
must strictly exceed preserving current cash. -/
def projectPassesCurrentCashAndReturnTest
    (currentCash projectedOutput quotedRepayment price : ℕ) : Prop :=
  price ≤ currentCash ∧ terminalMoneyPreferred
    ((currentCash : ℤ) + projectedOutput - price - quotedRepayment)
    (currentCash : ℤ)

instance projectPassesCurrentCashAndReturnTestDecidable
    (currentCash projectedOutput quotedRepayment price : ℕ) :
    Decidable (projectPassesCurrentCashAndReturnTest currentCash projectedOutput
      quotedRepayment price) := by
  unfold projectPassesCurrentCashAndReturnTest terminalMoneyPreferred
  infer_instance

/-- The current-cash return screen is the existing terminal-money comparison
expressed in the current market node's cash coordinate. Cash cancels from the
strict return test; it remains separately required for physical purchase
affordability. -/
theorem projectPassesCurrentCashAndReturnTest_iff
    (currentCash projectedOutput quotedRepayment price : ℕ) :
    projectPassesCurrentCashAndReturnTest currentCash projectedOutput
      quotedRepayment price ↔
      price ≤ currentCash ∧ quotedRepayment + price < projectedOutput := by
  unfold projectPassesCurrentCashAndReturnTest terminalMoneyPreferred
  constructor <;> intro h <;> rcases h with ⟨haffordable, hreturn⟩ <;>
    constructor <;> omega

/-- Demand at the market node, parameterized by actual current cash and
projected output for each funded bid. -/
def factorDemandingProjectsAtCurrentCash (funded : List LoanReservationBid)
    (quotedRepayment price : ℕ) (currentCash projectedOutput :
      LoanReservationBid → ℕ) : List LoanReservationBid :=
  funded.filter fun bid => decide
    (projectPassesCurrentCashAndReturnTest (currentCash bid)
      (projectedOutput bid) quotedRepayment price)

/-- Ascending price clock using the same current-cash and projected-return
eligibility rule as `factorDemandingProjectsAtCurrentCash`. -/
def ascendingCompletionFactorPriceAtCurrentCash? (funded : List LoanReservationBid)
    (quotedRepayment reservePrice supply greatestCurrentCash : ℕ)
    (currentCash projectedOutput : LoanReservationBid → ℕ) : Option ℕ :=
  (completionFactorPriceCandidates reservePrice greatestCurrentCash).find?
    (fun price => decide
      ((factorDemandingProjectsAtCurrentCash funded quotedRepayment price
        currentCash projectedOutput).length ≤ supply))

/-- Every returned current-cash clearing price satisfies the same quantity
constraint used by the ascending clock. -/
theorem ascendingCompletionFactorPriceAtCurrentCash?_clears
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestCurrentCash price : ℕ)
    (currentCash projectedOutput : LoanReservationBid → ℕ)
    (hprice : ascendingCompletionFactorPriceAtCurrentCash? funded
      quotedRepayment reservePrice supply greatestCurrentCash currentCash
      projectedOutput = some price) :
    (factorDemandingProjectsAtCurrentCash funded quotedRepayment price
      currentCash projectedOutput).length ≤ supply := by
  unfold ascendingCompletionFactorPriceAtCurrentCash? at hprice
  have hclears := List.find?_some
    (p := fun candidate => decide
      ((factorDemandingProjectsAtCurrentCash funded quotedRepayment candidate
        currentCash projectedOutput).length ≤ supply))
    (a := price) hprice
  exact of_decide_eq_true hclears

/-- Current-cash factor demand cannot exceed the offered physical supply at
any price returned by its clearing clock. -/
theorem factorDemandingProjectsAtCurrentCash_length_le_supply
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestCurrentCash price : ℕ)
    (currentCash projectedOutput : LoanReservationBid → ℕ)
    (hprice : ascendingCompletionFactorPriceAtCurrentCash? funded
      quotedRepayment reservePrice supply greatestCurrentCash currentCash
      projectedOutput = some price) :
    (factorDemandingProjectsAtCurrentCash funded quotedRepayment price
      currentCash projectedOutput).length ≤ supply :=
  ascendingCompletionFactorPriceAtCurrentCash?_clears funded quotedRepayment
    reservePrice supply greatestCurrentCash price currentCash projectedOutput hprice

/-- The ascending clock returns a price when `greatestBuffer` really bounds
every funded project's cash buffer. At a strictly higher candidate price no
project is affordable, so demand is zero. The bound is explicit because the
price-clock function otherwise accepts an arbitrary finite search endpoint. -/
theorem ascendingCompletionFactorPrice?_exists_of_buffer_bound
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestBuffer : ℕ)
    (hbufferBound : ∀ bid, bid ∈ funded →
      fiveProjectCashBuffer bid.borrower ≤ greatestBuffer) :
    ∃ price, ascendingCompletionFactorPrice? funded quotedRepayment reservePrice
      supply greatestBuffer = some price := by
  let upper := max reservePrice (greatestBuffer + 1)
  have hreserve : reservePrice ≤ upper := by
    dsimp [upper]
    exact Nat.le_max_left _ _
  have hbuffer : greatestBuffer < upper := by
    dsimp [upper]
    omega
  have hupper_mem : upper ∈ completionFactorPriceCandidates reservePrice greatestBuffer := by
    unfold completionFactorPriceCandidates
    rw [List.mem_map]
    refine ⟨upper - reservePrice, List.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  have hno_project : ∀ bid, bid ∈ funded →
      ¬ projectPassesCashBufferAndReturnTestAt bid quotedRepayment upper := by
    intro bid hbid hproject
    have hfundedBuffer := hbufferBound bid hbid
    exact (Nat.not_le_of_gt hbuffer) (le_trans hproject.1 hfundedBuffer)
  have hno_demand : completionFactorDemandAt funded quotedRepayment upper = 0 := by
    have hfilter : funded.filter
        (fun bid => decide
          (projectPassesCashBufferAndReturnTestAt bid quotedRepayment upper)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro bid hbid hproject
      exact hno_project bid hbid (of_decide_eq_true hproject)
    simp [completionFactorDemandAt, hfilter]
  have hupper_clears :
      decide (completionFactorDemandAt funded quotedRepayment upper ≤ supply) = true := by
    rw [hno_demand]
    simp
  have hfind_some :
      ((completionFactorPriceCandidates reservePrice greatestBuffer).find?
        (fun price => decide
          (completionFactorDemandAt funded quotedRepayment price ≤ supply))).isSome = true :=
    (List.find?_isSome).2 ⟨upper, hupper_mem, hupper_clears⟩
  unfold ascendingCompletionFactorPrice?
  cases hfind : (completionFactorPriceCandidates reservePrice greatestBuffer).find?
      (fun price => decide
        (completionFactorDemandAt funded quotedRepayment price ≤ supply)) with
  | none => simp [hfind] at hfind_some
  | some price => exact ⟨price, rfl⟩

/-- Any price returned by the ascending clock satisfies the market's stated
quantity-clearing condition. The result follows from the first satisfying
candidate selected by `List.find?`; it does not require a witness-specific
calculation. -/
theorem ascendingCompletionFactorPrice?_clears
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestBuffer price : ℕ)
    (hprice : ascendingCompletionFactorPrice? funded quotedRepayment reservePrice
      supply greatestBuffer = some price) :
    completionFactorDemandAt funded quotedRepayment price ≤ supply := by
  unfold ascendingCompletionFactorPrice? at hprice
  have hclears := List.find?_some
    (p := fun candidate => decide
      (completionFactorDemandAt funded quotedRepayment candidate ≤ supply))
    (a := price) hprice
  exact of_decide_eq_true hclears

/-- If demand already fits supply at the reserve price, the ascending clock
returns the reserve price. The candidate list begins there, so no higher
candidate is consulted. -/
theorem ascendingCompletionFactorPrice?_eq_reserve_of_demand_fits
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestBuffer : ℕ)
    (hfits : completionFactorDemandAt funded quotedRepayment reservePrice ≤ supply) :
    ascendingCompletionFactorPrice? funded quotedRepayment reservePrice supply
      greatestBuffer = some reservePrice := by
  have hfitsBool :
      decide (completionFactorDemandAt funded quotedRepayment reservePrice ≤ supply) = true :=
    decide_eq_true_eq.mpr hfits
  apply (List.find?_eq_some_iff_getElem).2
  refine ⟨of_decide_eq_true hfitsBool, 0, ?_, ?_, ?_⟩
  · simp [completionFactorPriceCandidates, List.length_map, List.length_range]
  · simp [completionFactorPriceCandidates]
  · intro j hj
    omega

/-- If reserve-price demand exceeds supply, every clearing price returned by
the ascending clock is strictly above the reserve price. Thus the price rise
is derived from the reserve shortage and the clock's ascending order. -/
theorem ascendingCompletionFactorPrice?_gt_reserve_of_reserve_shortage
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestBuffer price : ℕ)
    (hshortage : supply <
      completionFactorDemandAt funded quotedRepayment reservePrice)
    (hprice : ascendingCompletionFactorPrice? funded quotedRepayment reservePrice
      supply greatestBuffer = some price) :
    reservePrice < price := by
  have hpriceOriginal := hprice
  rcases (List.find?_eq_some_iff_getElem).1 hpriceOriginal with
    ⟨hpricePredicate, index, _, hcandidate, _⟩
  have hpriceValue : reservePrice + index = price := by
    simpa [completionFactorPriceCandidates] using hcandidate
  have hnotReserve : price ≠ reservePrice := by
    intro heq
    have hclearsAtPrice :
        completionFactorDemandAt funded quotedRepayment price ≤ supply :=
      of_decide_eq_true hpricePredicate
    have hclearsReserve :
        completionFactorDemandAt funded quotedRepayment reservePrice ≤ supply := by
      simpa [heq] using hclearsAtPrice
    omega
  omega

/-- At a returned clearing price, the number of eligible project plans does
not exceed the offered factor supply. This is a quantity-clearing result;
executed factor transfers and physical completion are not defined here. -/
theorem factorDemandingProjectsAt_length_le_supply
    (funded : List LoanReservationBid) (quotedRepayment reservePrice supply
      greatestBuffer price : ℕ)
    (hprice : ascendingCompletionFactorPrice? funded quotedRepayment reservePrice
      supply greatestBuffer = some price) :
    (factorDemandingProjectsAt funded quotedRepayment price).length ≤ supply := by
  have hclears := ascendingCompletionFactorPrice?_clears funded quotedRepayment
    reservePrice supply greatestBuffer price hprice
  simpa [completionFactorDemandAt, factorDemandingProjectsAt] using hclears

/-- At the reserve price one, the baseline's two funded projects demand two
factors, so the clock clears immediately at one. -/
theorem five_project_baseline_factor_price :
    ascendingCompletionFactorPrice?
      (clearLoanMarket fiveProjectLoanMarket 2).funded 6 1 2 3 = some 1 := by
  apply ascendingCompletionFactorPrice?_eq_reserve_of_demand_fits
  decide

/-- Under fiduciary expansion, all four funded projects demand the factor at
price one, exceeding supplier stock two; at price two only the first two have
both sufficient buffers and strictly positive projected proceeds, so the clock
clears at two. -/
theorem five_project_credit_factor_price :
    completionFactorDemandAt
        (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 = 4 ∧
    completionFactorDemandAt
        (clearLoanMarket fiveProjectLoanMarket 4).funded 4 2 = 2 ∧
    ascendingCompletionFactorPrice?
      (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 2 3 = some 2 := by
  decide

/-- In the credit expansion, reserve-price demand is four against supply two.
The general shortage theorem therefore forces the clearing price above the
reserve quote; the fixed clock calculation identifies that price as two. -/
theorem five_project_credit_price_rises_from_reserve_shortage :
    2 < completionFactorDemandAt
        (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 ∧
    ascendingCompletionFactorPrice?
      (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 2 3 = some 2 ∧
    1 < 2 := by
  have hmarket := five_project_credit_factor_price
  have hshortage : 2 < completionFactorDemandAt
      (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 := by
    omega
  have hprice : ascendingCompletionFactorPrice?
      (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 2 3 = some 2 :=
    hmarket.2.2
  have hrise := ascendingCompletionFactorPrice?_gt_reserve_of_reserve_shortage
    (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 2 3 2 hshortage hprice
  refine ⟨hshortage, hprice, ?_⟩
  exact hrise

/-- The household-transfer scenario specifies two household factors as offered
for production. With four total factors, the same funded cohort clears at the
reserve price. This is scenario accounting, not evidence of a purposeful
saving choice. -/
theorem five_project_household_transfer_factor_price :
    completionFactorDemandAt
        (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 = 4 ∧
    ascendingCompletionFactorPrice?
      (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1 4 3 = some 1 := by
  refine ⟨by decide, ?_⟩
  apply ascendingCompletionFactorPrice?_eq_reserve_of_demand_fits
  decide

/-- The credit expansion funds four projects, but at the derived factor price
two only the first two satisfy the modeled affordability and preference tests.
The remaining two are excluded from the factor-demand list; this does not yet
assert a matched trade or physical completion. -/
theorem five_project_credit_factor_demand_sets :
    (factorDemandingProjectsAt (clearLoanMarket fiveProjectLoanMarket 4).funded 4 2).map
        LoanReservationBid.borrower = [0, 1] ∧
    (factorExcludedProjectsAt (clearLoanMarket fiveProjectLoanMarket 4).funded 4 2).map
        LoanReservationBid.borrower = [2, 3] := by
  decide

/-- With the two household factors specified as offered in the transfer
scenario added to supplier stock, all four funded projects are eligible at
the reserve price and quantity demand fits the stated supply. -/
theorem five_project_household_transfer_factor_demand_set :
    (factorDemandingProjectsAt (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1).map
      LoanReservationBid.borrower = [0, 1, 2, 3] := by
  decide

/-- Calculate a final customer's unit-price-one purchase plan in the market's
project order, never assigning more output than its budget can buy. This is a
schedule calculation, not an enacted bilateral exchange. -/
def customerUnitPurchasePlan (availableMoney : ℕ) :
    List LoanReservationBid → List (Fin 5 × ℕ)
  | [] => []
  | bid :: rest =>
      let sold := min (fiveProjectOutput bid.borrower) availableMoney
      (bid.borrower, sold) :: customerUnitPurchasePlan (availableMoney - sold) rest

/-- Planned proceeds equal the total units in the purchase schedule because
the modeled customer price is one money unit per physical output unit. -/
def customerUnitRevenuePlan (sales : List (Fin 5 × ℕ)) : ℕ :=
  sales.foldl (fun total sale => total + sale.2) 0

/-- With forty customer money units, the plan assigns purchases of all output
from the two factor-eligible credit projects, for seventeen planned money
units of proceeds. -/
theorem five_project_credit_customer_purchase_plan :
    customerUnitPurchasePlan 40
        (factorDemandingProjectsAt (clearLoanMarket fiveProjectLoanMarket 4).funded 4 2) =
      [(0, 9), (1, 8)] ∧
    customerUnitRevenuePlan
        (customerUnitPurchasePlan 40
          (factorDemandingProjectsAt
            (clearLoanMarket fiveProjectLoanMarket 4).funded 4 2)) = 17 := by
  decide

/-- With forty customer money units, the plan assigns purchases of all output
from the four factor-eligible projects in the household-transfer scenario, for
thirty planned money units of proceeds. -/
theorem five_project_household_transfer_customer_purchase_plan :
    customerUnitPurchasePlan 40
        (factorDemandingProjectsAt (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1) =
      [(0, 9), (1, 8), (2, 7), (3, 6)] ∧
    customerUnitRevenuePlan
        (customerUnitPurchasePlan 40
          (factorDemandingProjectsAt
            (clearLoanMarket fiveProjectLoanMarket 4).funded 4 1)) = 30 := by
  decide

end Praxeology

end
