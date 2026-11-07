/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Regimes
public import Praxeology.Catallactics.Credit
public import Praxeology.FiniteEconomy.Compiler
public import Praxeology.FiniteEconomy.Physical

/-!
# Physical execution of completion-factor purchases

The Regimes factor-demand lists are projected calculations; this executor
clears again from each prepared branch's actual funded advances, current cash,
and offered stocks. The shared current-cash auction selects eligible bids,
then the physical interpreter checks each transfer against current holdings.
The resulting purchases run as sequential bilateral transfers. The household's
stated consumption is run first; offered factors remain in its inventory until
a matched trade sells them. The existing output schedule then supplies the
completion operations, and customer purchases execute through matched trades.
Each factor-sale stage keeps idle and unilateral offer/accept profiles in its
finite menu; only the matched profile transfers inventory. Regime-specified
fiduciary notes, the household cash transfer, and standardized loan advances are also
executed through operation or matched-transfer stages. After sales, each
completed project's auction-quoted repayment is a separate matched transfer.
In the household-transfer regime, the household exchanges two money units for
one identified deposit claim promising three units at redemption. The claim
and its redemption are recorded only when their transfers match. Funded
borrowers purchase one early input and convert it one-to-one into project
capital before completion. Unpaid maturity follows the explicit five-project
nonrecourse agreement: title to collateral held by the bank transfers to it,
and the remaining obligation is discharged. This contractual settlement is
distinct from physical project completion.
-/

@[expose] public section

namespace Praxeology

abbrev FiveProjectPhysicalAgent := Fin 9
abbrev FiveProjectPhysicalGood := Fin 11

def fiveProjectFactorSupplier : FiveProjectPhysicalAgent := 0
def fiveProjectBank : FiveProjectPhysicalAgent := 7
def fiveProjectHousehold : FiveProjectPhysicalAgent := 8
def fiveProjectMoneyGood : FiveProjectPhysicalGood := 0
def fiveProjectCompletionGood : FiveProjectPhysicalGood := 1
def fiveProjectOutputGood : FiveProjectPhysicalGood := 2
def fiveProjectEarlyInputGood : FiveProjectPhysicalGood := 3
def fiveProjectCapitalGood : FiveProjectPhysicalGood := 4
def fiveProjectDepositClaimGood : FiveProjectPhysicalGood := 10

/-- Named stages in the finite physical program. The cursor consumes these
positions in order; loan and deposit contracts can name their settlement
stage without relying on a numeric offset. -/
inductive FiveProjectPhysicalPhase where
  | chooseHouseholdPlan
  | noteIssuance
  | householdCashTransfer
  | loanClearing
  | loanAcceptance (project : Fin 5)
  | earlyInputPurchase (project : Fin 5)
  | capitalConversion (project : Fin 5)
  | householdConsumption
  | factorClearing
  | factorPurchase (slot : Fin 5)
  | completion (project : Fin 5)
  | customerSale (project : Fin 5)
  | loanSettlement (project : Fin 5)
  | loanMaturitySettlement (project : Fin 5)
  | depositSettlement
  deriving DecidableEq, Repr

/-- Terms accepted at deposit origination. The same holder, issuer, claim,
promised amount, and named settlement stage parameterize later redemption. -/
structure FiveProjectDepositTerms where
  holder : FiveProjectPhysicalAgent
  issuer : FiveProjectPhysicalAgent
  holder_ne_issuer : holder ≠ issuer
  principal : ℕ
  claimQuantity : ℕ
  claimGood : FiveProjectPhysicalGood
  moneyGood : FiveProjectPhysicalGood
  promisedRepayment : ℕ
  redemptionPhase : FiveProjectPhysicalPhase
  deriving DecidableEq

def fiveProjectHouseholdDepositTerms : FiveProjectDepositTerms where
  holder := fiveProjectHousehold
  issuer := fiveProjectBank
  holder_ne_issuer := by decide
  principal := 2
  claimQuantity := 1
  claimGood := fiveProjectDepositClaimGood
  moneyGood := fiveProjectMoneyGood
  promisedRepayment := 3
  redemptionPhase := .depositSettlement

def fiveProjectPhysicalBorrower (project : Fin 5) : FiveProjectPhysicalAgent :=
  ⟨project.val + 1, by omega⟩

/-- Each borrower pledges a distinct, initially owned collateral good. -/
def fiveProjectCollateralGood (project : Fin 5) : FiveProjectPhysicalGood :=
  ⟨project.val + 5, by omega⟩

/-- Contract supplied at origination for one project's collateralized advance.
The terms state custody of the named collateral, return of title after full
repayment, and an all-or-nothing nonrecourse settlement at unpaid maturity:
title transfers to the lender and no loan balance remains collectible. -/
structure FiveProjectPawnAgreement where
  bid : LoanReservationBid
  terms : FundedLoanTerms
  lender : FiveProjectPhysicalAgent
  collateral : FiveProjectPhysicalGood
  collateralQuantity : Nat
  titleOwner : CreditStatus → FiveProjectPhysicalAgent
  remainingObligation : CreditStatus → Option Nat
  borrower_matches : terms.borrower = bid.borrower
  principal_matches : terms.principal = fiveProjectLoanMarket.principal
  lender_is_bank : lender = fiveProjectBank
  collateral_is_pledged_good : collateral = fiveProjectCollateralGood bid.borrower
  collateral_quantity_is_one : collateralQuantity = 1
  title_before_default : titleOwner .unadvanced = fiveProjectPhysicalBorrower bid.borrower ∧
    titleOwner .outstanding = fiveProjectPhysicalBorrower bid.borrower
  title_after_repayment : titleOwner .repaid = fiveProjectPhysicalBorrower bid.borrower
  title_after_unpaid_maturity : titleOwner .defaulted = lender
  obligation_not_open_before_advance : remainingObligation .unadvanced = none
  obligation_open_after_advance : remainingObligation .outstanding =
    some terms.promisedRepayment
  obligation_discharged_after_repayment : remainingObligation .repaid = none
  obligation_discharged_by_collateral_at_default : remainingObligation .defaulted = none

/-- The named agreement preserves the clearing quote and encodes exactly the
stated nonrecourse collateral disposition. It introduces no seizure profile:
the lender already has physical custody from the matched origination. -/
def fiveProjectPawnAgreement (bid : LoanReservationBid) (repayment : Nat) :
    FiveProjectPawnAgreement := by
  let terms : FundedLoanTerms :=
    { borrower := bid.borrower
      principal := fiveProjectLoanMarket.principal
      principal_positive := fiveProjectLoanMarket.principal_positive
      promisedRepayment := repayment }
  refine
    { bid := bid
      terms := terms
      lender := fiveProjectBank
      collateral := fiveProjectCollateralGood bid.borrower
      collateralQuantity := 1
      titleOwner := fun status =>
        if status = .defaulted then fiveProjectBank
        else fiveProjectPhysicalBorrower bid.borrower
      remainingObligation := fun status =>
        if status = .outstanding then some repayment else none
      borrower_matches := rfl
      principal_matches := rfl
      lender_is_bank := rfl
      collateral_is_pledged_good := rfl
      collateral_quantity_is_one := rfl
      title_before_default := ?_
      title_after_repayment := ?_
      title_after_unpaid_maturity := ?_
      obligation_not_open_before_advance := ?_
      obligation_open_after_advance := ?_
      obligation_discharged_after_repayment := ?_
      obligation_discharged_by_collateral_at_default := ?_ }
  · constructor <;> simp
  · simp
  · simp
  · simp
  · rfl
  · simp
  · simp

/-- The customer's initial money endowment in the fixed physical witness. -/
def fiveProjectCustomerMoneyEndowment : ℕ := 40

/-- Household plan data chosen before its deposit, consumption, and factor-offer
actions. The program records the selection in its cursor; the plan operation
itself changes no physical inventory. -/
structure FiveProjectHouseholdPlan where
  deposit : ℕ
  consumedFactors : ℕ
  offeredFactors : ℕ
  deriving DecidableEq, Repr

/-- The fixed regime schedule is the selected-plan profile used by its named
path. The compiled choice stage also exposes its affordable alternatives. -/
def fiveProjectHouseholdPlanOf (D : FiveProjectRegimeData) :
    FiveProjectHouseholdPlan where
  deposit := D.householdMoneyTransferred
  consumedFactors := D.householdFactorsConsumed
  offeredFactors := D.householdFactorsOffered

theorem fiveProjectHousehold_ne_bank :
    fiveProjectHousehold ≠ fiveProjectBank := by
  decide

inductive FiveProjectPhysicalOperation where
  | issueFiduciaryNotes (quantity : ℕ)
  | chooseHouseholdPlan (plan : FiveProjectHouseholdPlan)
  | consumeHouseholdFactors (quantity : ℕ)
  | convertEarlyInputToCapital (project : Fin 5)
  | completeProject (project : Fin 5)
  deriving DecidableEq

/-- The household's delivered consumption-service quantity. -/
def fiveProjectConsumptionService : ℕ := 0

def fiveProjectPhysicalOperations :
    OperationSemantics FiveProjectPhysicalOperation
      FiveProjectPhysicalGood Nat where
  input operation good :=
    match operation with
    | .issueFiduciaryNotes _ => 0
    | .chooseHouseholdPlan _ => 0
    | .consumeHouseholdFactors quantity =>
        if good = fiveProjectCompletionGood then quantity else 0
    | .convertEarlyInputToCapital _ =>
        if good = fiveProjectEarlyInputGood then 1 else 0
    | .completeProject _ =>
        if good = fiveProjectCompletionGood ∨ good = fiveProjectCapitalGood then 1 else 0
  output operation good :=
    match operation with
    | .issueFiduciaryNotes quantity =>
        if good = fiveProjectMoneyGood then quantity else 0
    | .chooseHouseholdPlan _ => 0
    | .consumeHouseholdFactors _ => 0
    | .convertEarlyInputToCapital _ =>
        if good = fiveProjectCapitalGood then 1 else 0
    | .completeProject project =>
        if good = fiveProjectOutputGood then fiveProjectOutput project else 0
  service operation serviceKind :=
    if serviceKind = fiveProjectConsumptionService then
      match operation with
      | .consumeHouseholdFactors quantity => quantity
      | _ => 0
    else 0

/-- Action profile for a matched, zero-price money transfer. Both parties
enact corresponding offer and acceptance actions. -/
def fiveProjectMoneyTransferProfile (sender recipient : FiveProjectPhysicalAgent)
    (quantity : ℕ) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = sender then
      .offer sender recipient quantity fiveProjectMoneyGood 0 fiveProjectMoneyGood
    else if actor = recipient then
      .accept recipient sender quantity fiveProjectMoneyGood 0 fiveProjectMoneyGood
    else .idle

/-- Origination exchanges the bank's principal for the borrower's identified
collateral good. No advance occurs unless both actions match and both goods
are owned in the common pre-state. -/
def fiveProjectLoanAdvanceProfile (bid : LoanReservationBid) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  let borrower := fiveProjectPhysicalBorrower bid.borrower
  let collateral := fiveProjectCollateralGood bid.borrower
  fun actor =>
    if actor = fiveProjectBank then
      .offer fiveProjectBank borrower fiveProjectLoanMarket.principal
        fiveProjectMoneyGood 1 collateral
    else if actor = borrower then
      .accept borrower fiveProjectBank fiveProjectLoanMarket.principal
        fiveProjectMoneyGood 1 collateral
    else .idle

/-- Physically enact one collateralized principal advance through the common
inventory interpreter. -/
def executeFiveProjectLoanAdvance
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (bid : LoanReservationBid) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectLoanAdvanceProfile bid)

/-- Repayment transfers the promised money back to the bank and returns that
borrower's pledged collateral in the same matched exchange. -/
def fiveProjectLoanRepaymentProfile (contract : FundedLoanTerms) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  let borrower := fiveProjectPhysicalBorrower contract.borrower
  let collateral := fiveProjectCollateralGood contract.borrower
  fun actor =>
    if actor = borrower then
      .offer borrower fiveProjectBank contract.promisedRepayment
        fiveProjectMoneyGood 1 collateral
    else if actor = fiveProjectBank then
      .accept fiveProjectBank borrower contract.promisedRepayment
        fiveProjectMoneyGood 1 collateral
    else .idle

/-- Physically settle one funded loan only when the borrower can transfer the
promised repayment and the bank holds the pledged collateral. -/
def executeFiveProjectLoanRepayment
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (contract : FundedLoanTerms) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectLoanRepaymentProfile contract)

/-- Origination exchanges the specified household principal for the bank's
identified deposit claim. -/
def fiveProjectDepositOriginationProfile :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = fiveProjectHouseholdDepositTerms.holder then
      .offer fiveProjectHouseholdDepositTerms.holder
        fiveProjectHouseholdDepositTerms.issuer
        fiveProjectHouseholdDepositTerms.principal
        fiveProjectHouseholdDepositTerms.moneyGood
        fiveProjectHouseholdDepositTerms.claimQuantity
        fiveProjectHouseholdDepositTerms.claimGood
    else if actor = fiveProjectHouseholdDepositTerms.issuer then
      .accept fiveProjectHouseholdDepositTerms.issuer
        fiveProjectHouseholdDepositTerms.holder
        fiveProjectHouseholdDepositTerms.principal
        fiveProjectHouseholdDepositTerms.moneyGood
        fiveProjectHouseholdDepositTerms.claimQuantity
        fiveProjectHouseholdDepositTerms.claimGood
    else .idle

/-- Redemption follows the recorded agreement and pays its promised cash only
against return of the same claim. -/
def fiveProjectDepositRedemptionProfile (terms : FiveProjectDepositTerms) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = terms.holder then
      .offer terms.holder terms.issuer terms.claimQuantity terms.claimGood
        terms.promisedRepayment terms.moneyGood
    else if actor = terms.issuer then
      .accept terms.issuer terms.holder terms.claimQuantity terms.claimGood
        terms.promisedRepayment terms.moneyGood
    else .idle

/-- Execute deposit redemption only if its matched transfer is affordable. -/
def executeFiveProjectDepositRedemption (terms : FiveProjectDepositTerms)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectDepositRedemptionProfile terms)

/-- A complete profile for one proposed factor sale. Only the seller and buyer
act; the interpreter transfers stocks only when both actions match exactly. -/
def fiveProjectFactorPurchaseProfile (seller buyer : FiveProjectPhysicalAgent)
    (price : ℕ) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = seller then
      .offer seller buyer 1 fiveProjectCompletionGood price fiveProjectMoneyGood
    else if actor = buyer then
      .accept buyer seller 1 fiveProjectCompletionGood price fiveProjectMoneyGood
    else .idle

/-- Each funded borrower can purchase one early input from the supplier for
one unit of money through the same matched-transfer interpreter. -/
def fiveProjectEarlyInputPurchaseProfile (project : Fin 5) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  let seller := fiveProjectFactorSupplier
  let buyer := fiveProjectPhysicalBorrower project
  fun actor =>
    if actor = seller then
      .offer seller buyer 1 fiveProjectEarlyInputGood 1 fiveProjectMoneyGood
    else if actor = buyer then
      .accept buyer seller 1 fiveProjectEarlyInputGood 1 fiveProjectMoneyGood
    else .idle

def executeFiveProjectEarlyInputPurchase
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectEarlyInputPurchaseProfile project)

/-- Convert one owned early input to one capital unit with the declared
operation semantics. -/
def executeFiveProjectCapitalConversion
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  let borrower := fiveProjectPhysicalBorrower project
  let profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
    fun actor =>
      if actor = borrower then .operate (.convertEarlyInputToCapital project)
      else .idle
  advanceIfAffordable fiveProjectPhysicalOperations state profile

/-- Apply one matched completion-factor purchase to the current inventory.
Insufficient seller stock or buyer money yields `none` under the existing
pre-transition affordability check. -/
def executeFiveProjectFactorPurchase
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectFactorPurchaseProfile seller buyer price)

/-- A successful factor purchase obeys the interpreter's exact bilateral
inventory balances: one completion unit and `price` money units move between
the two parties. No additional transfer rule is assumed here. -/
theorem executeFiveProjectFactorPurchase_balances
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ)
    (hdistinct : seller ≠ buyer)
    (hstep : executeFiveProjectFactorPurchase state seller buyer price = some next) :
    next.stock seller fiveProjectCompletionGood + 1 =
        state.stock seller fiveProjectCompletionGood ∧
      next.stock buyer fiveProjectMoneyGood + price =
        state.stock buyer fiveProjectMoneyGood ∧
      next.stock seller fiveProjectMoneyGood =
        state.stock seller fiveProjectMoneyGood + price ∧
      next.stock buyer fiveProjectCompletionGood =
        state.stock buyer fiveProjectCompletionGood + 1 := by
  unfold executeFiveProjectFactorPurchase at hstep
  have hbalance := advanceIfAffordable_matchedTransfer_balance
    fiveProjectPhysicalOperations state next
    (fiveProjectFactorPurchaseProfile seller buyer price) seller buyer
    1 fiveProjectCompletionGood price fiveProjectMoneyGood hstep
    (by simp [fiveProjectFactorPurchaseProfile])
    (by simp [fiveProjectFactorPurchaseProfile, hdistinct.symm])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [fiveProjectCompletionGood, fiveProjectMoneyGood] using
      hbalance.1 fiveProjectCompletionGood
  · simpa [fiveProjectCompletionGood, fiveProjectMoneyGood] using
      hbalance.2 fiveProjectMoneyGood
  · simpa [fiveProjectCompletionGood, fiveProjectMoneyGood] using
      hbalance.1 fiveProjectMoneyGood
  · simpa [fiveProjectCompletionGood, fiveProjectMoneyGood] using
      hbalance.2 fiveProjectCompletionGood

/-- A physical choice stage built around one selected complete profile. Every
active agent can choose its selected action or idle, and inactive agents can
only idle. The selected actions must already be affordable from the common
pre-state; no incoming transfer is used as an input. -/
def finitePhysicalStageOfProfile
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (active : Finset FiveProjectPhysicalAgent)
    (profile_nonidle : ∀ agent, agent ∈ active → profile agent ≠ EconomyAction.idle)
    (profile_wellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent))
    (profile_affordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent)) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat :=
  { choices := FiniteChoiceStage.ofProfile profile active profile_nonidle
      profile_wellFormed
    operations := fiveProjectPhysicalOperations
    before := state
    menu_affordable := by
      intro agent action haction
      by_cases hactive : agent ∈ active
      · simp only [FiniteChoiceStage.ofProfile, hactive, ite_true,
          Finset.mem_insert, Finset.mem_singleton] at haction
        rcases haction with haction | haction
        · subst action
          intro good
          simp [rawActionUse]
        · subst action
          exact profile_affordable agent
      · simp only [FiniteChoiceStage.ofProfile, hactive, ite_false,
          Finset.mem_singleton] at haction
        subst action
        intro good
        simp [rawActionUse] }

/-- A matched money transfer has a physical choice stage with idle and
unilateral offer/accept alternatives. The selected profile is affordable
when the sender owns the transferred amount in the common pre-state. -/
def fiveProjectMoneyTransferChoiceStage
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ)
    (hdistinct : sender ≠ recipient)
    (hfunded : quantity ≤ state.stock sender fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat := by
  let profile := fiveProjectMoneyTransferProfile sender recipient quantity
  let active : Finset FiveProjectPhysicalAgent := {sender, recipient}
  have hnonidle : ∀ agent, agent ∈ active → profile agent ≠ EconomyAction.idle := by
    intro agent hagent
    simp only [active, Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with hs | hr
    · subst agent
      simp [profile, fiveProjectMoneyTransferProfile]
    · subst agent
      simp [profile, fiveProjectMoneyTransferProfile, hdistinct.symm]
  have hwellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent) := by
    intro agent
    by_cases hs : agent = sender
    · subst agent
      simp [profile, fiveProjectMoneyTransferProfile,
        EconomyAction.WellFormed, hdistinct]
    · by_cases hr : agent = recipient
      · subst agent
        simp [profile, fiveProjectMoneyTransferProfile,
          EconomyAction.WellFormed, hs]
      · simp [profile, fiveProjectMoneyTransferProfile, hs, hr,
          EconomyAction.WellFormed]
  have hprofileAffordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent) := by
    intro agent good
    by_cases hs : agent = sender
    · subst agent
      by_cases hgood : good = fiveProjectMoneyGood
      · simpa [profile, fiveProjectMoneyTransferProfile,
          rawActionUse, hgood] using hfunded
      · simp [profile, fiveProjectMoneyTransferProfile,
          rawActionUse, hgood]
    · by_cases hr : agent = recipient
      · subst agent
        simp [profile, fiveProjectMoneyTransferProfile,
          rawActionUse, hs]
      · simp [profile, fiveProjectMoneyTransferProfile, hs, hr, rawActionUse]
  exact finitePhysicalStageOfProfile state profile active
    hnonidle hwellFormed hprofileAffordable

/-- A deposit origination choice stage with the same idle and unilateral
branches as other bilateral transfers. Both the household's principal and
the bank's claim must be present before the matched profile is feasible. -/
def fiveProjectDepositOriginationChoiceStage
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (hprincipal : fiveProjectHouseholdDepositTerms.principal ≤
      state.stock fiveProjectHousehold fiveProjectMoneyGood)
    (hclaim : 1 ≤ state.stock fiveProjectBank fiveProjectDepositClaimGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat := by
  let profile := fiveProjectDepositOriginationProfile
  let active : Finset FiveProjectPhysicalAgent :=
    {fiveProjectHousehold, fiveProjectBank}
  have hnonidle : ∀ agent, agent ∈ active → profile agent ≠ EconomyAction.idle := by
    intro agent hagent
    simp only [active, Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with hh | hb
    · subst agent
      simp [profile, fiveProjectDepositOriginationProfile,
        fiveProjectHouseholdDepositTerms]
    · subst agent
      simp [profile, fiveProjectDepositOriginationProfile,
        fiveProjectHouseholdDepositTerms, fiveProjectHousehold_ne_bank.symm]
  have hwellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent) := by
    intro agent
    by_cases hh : agent = fiveProjectHousehold
    · subst agent
      simp [profile, fiveProjectDepositOriginationProfile,
        EconomyAction.WellFormed, fiveProjectHouseholdDepositTerms,
        fiveProjectHousehold_ne_bank]
    · by_cases hb : agent = fiveProjectBank
      · subst agent
        simp [profile, fiveProjectDepositOriginationProfile,
          EconomyAction.WellFormed, fiveProjectHouseholdDepositTerms, hh]
      · simp [profile, fiveProjectDepositOriginationProfile, hh, hb,
          fiveProjectHouseholdDepositTerms, EconomyAction.WellFormed]
  have hprofileAffordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent) := by
    intro agent good
    by_cases hh : agent = fiveProjectHousehold
    · subst agent
      by_cases hgood : good = fiveProjectMoneyGood
      · simpa [profile, fiveProjectDepositOriginationProfile,
          rawActionUse, fiveProjectHouseholdDepositTerms, hgood] using hprincipal
      · simp [profile, fiveProjectDepositOriginationProfile,
          rawActionUse, fiveProjectHouseholdDepositTerms, hgood]
    · by_cases hb : agent = fiveProjectBank
      · subst agent
        by_cases hgood : good = fiveProjectDepositClaimGood
        · simpa [profile, fiveProjectDepositOriginationProfile,
            rawActionUse, fiveProjectHouseholdDepositTerms, hgood,
            fiveProjectHousehold_ne_bank.symm] using hclaim
        · simp [profile, fiveProjectDepositOriginationProfile,
            rawActionUse, fiveProjectHouseholdDepositTerms, hgood,
            fiveProjectHousehold_ne_bank.symm]
      · simp [profile, fiveProjectDepositOriginationProfile, rawActionUse,
          fiveProjectHouseholdDepositTerms, hh, hb]
  exact finitePhysicalStageOfProfile state profile active
    hnonidle hwellFormed hprofileAffordable

/-- Every actor's action in the matched deposit profile belongs to the
origination stage's finite menu. -/
theorem fiveProjectDepositOriginationChoiceStage_profile_mem
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (hprincipal : fiveProjectHouseholdDepositTerms.principal ≤
      state.stock fiveProjectHousehold fiveProjectMoneyGood)
    (hclaim : 1 ≤ state.stock fiveProjectBank fiveProjectDepositClaimGood) :
    ∀ agent,
      fiveProjectDepositOriginationProfile agent ∈
        (fiveProjectDepositOriginationChoiceStage state hprincipal hclaim).choices.menu
          agent := by
  intro agent
  by_cases hh : agent = fiveProjectHousehold
  · subst agent
    simp [fiveProjectDepositOriginationChoiceStage,
      finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
      fiveProjectDepositOriginationProfile, fiveProjectHouseholdDepositTerms]
  · by_cases hb : agent = fiveProjectBank
    · subst agent
      simp [fiveProjectDepositOriginationChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectDepositOriginationProfile, fiveProjectHouseholdDepositTerms, hh]
    · simp [fiveProjectDepositOriginationChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectDepositOriginationProfile, fiveProjectHouseholdDepositTerms, hh, hb]

/-- Execute the selected deposit exchange through its finite physical choice
stage. The stage is unavailable unless both sides own their offered goods. -/
def executeFiveProjectDepositOrigination
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  if hprincipal : fiveProjectHouseholdDepositTerms.principal ≤
      state.stock fiveProjectHousehold fiveProjectMoneyGood then
    if hclaim : 1 ≤ state.stock fiveProjectBank fiveProjectDepositClaimGood then
      let stage := fiveProjectDepositOriginationChoiceStage state hprincipal hclaim
      some (stage.advance
        ⟨fiveProjectDepositOriginationProfile,
          fiveProjectDepositOriginationChoiceStage_profile_mem state hprincipal hclaim⟩)
    else none
  else none

/-- The transfer stage contains both parties' unilateral choices and the
complete matched profile. Each unilateral profile leaves the other party idle. -/
theorem fiveProjectMoneyTransferChoiceStage_branches
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ)
    (hdistinct : sender ≠ recipient)
    (hfunded : quantity ≤ state.stock sender fiveProjectMoneyGood) :
    let stage := fiveProjectMoneyTransferChoiceStage
      state sender recipient quantity hdistinct hfunded
    (∃ offerProfile ∈ stage.choices.profiles,
      offerProfile.1 sender =
        EconomyAction.offer sender recipient quantity
          fiveProjectMoneyGood 0 fiveProjectMoneyGood ∧
      offerProfile.1 recipient = EconomyAction.idle) ∧
    (∃ acceptProfile ∈ stage.choices.profiles,
      acceptProfile.1 recipient =
        EconomyAction.accept recipient sender quantity
          fiveProjectMoneyGood 0 fiveProjectMoneyGood ∧
      acceptProfile.1 sender = EconomyAction.idle) ∧
    ∃ matchedProfile ∈ stage.choices.profiles,
      matchedProfile.1 sender =
        EconomyAction.offer sender recipient quantity
          fiveProjectMoneyGood 0 fiveProjectMoneyGood ∧
      matchedProfile.1 recipient = EconomyAction.accept recipient sender quantity
        fiveProjectMoneyGood 0 fiveProjectMoneyGood := by
  let stage := fiveProjectMoneyTransferChoiceStage
    state sender recipient quantity hdistinct hfunded
  let offer : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .offer sender recipient quantity fiveProjectMoneyGood 0 fiveProjectMoneyGood
  let accept : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .accept recipient sender quantity fiveProjectMoneyGood 0 fiveProjectMoneyGood
  have hoff : offer ∈ stage.choices.menu sender := by
    simp [stage, fiveProjectMoneyTransferChoiceStage,
      finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
      fiveProjectMoneyTransferProfile, offer, hdistinct]
  have haccept : accept ∈ stage.choices.menu recipient := by
    simp [stage, fiveProjectMoneyTransferChoiceStage,
      finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
      fiveProjectMoneyTransferProfile, accept, hdistinct.symm]
  have hmatched : ∀ agent,
      fiveProjectMoneyTransferProfile sender recipient quantity agent ∈
        stage.choices.menu agent := by
    intro agent
    by_cases hs : agent = sender
    · subst agent
      simp [stage, fiveProjectMoneyTransferChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectMoneyTransferProfile, hdistinct]
    · by_cases hr : agent = recipient
      · subst agent
        simp [stage, fiveProjectMoneyTransferChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectMoneyTransferProfile, hs]
      · simp [stage, fiveProjectMoneyTransferChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectMoneyTransferProfile, hs, hr]
  refine ⟨?_, ?_, ?_⟩
  · let profile := stage.choices.unilateralProfile sender offer hoff
    refine ⟨profile, stage.choices.unilateralProfile_mem_profiles sender offer hoff,
      ?_, ?_⟩
    · exact stage.choices.unilateralProfile_self sender offer hoff
    · exact stage.choices.unilateralProfile_other sender recipient offer hoff hdistinct.symm
  · let profile := stage.choices.unilateralProfile recipient accept haccept
    refine ⟨profile, stage.choices.unilateralProfile_mem_profiles recipient accept haccept,
      ?_, ?_⟩
    · exact stage.choices.unilateralProfile_self recipient accept haccept
    · exact stage.choices.unilateralProfile_other recipient sender accept haccept hdistinct
  · let profile : stage.choices.Profile :=
      ⟨fiveProjectMoneyTransferProfile sender recipient quantity, hmatched⟩
    refine ⟨profile, stage.choices.mem_profiles profile, ?_, ?_⟩
    · change fiveProjectMoneyTransferProfile sender recipient quantity sender = offer
      simp [offer, fiveProjectMoneyTransferProfile]
    · change fiveProjectMoneyTransferProfile sender recipient quantity recipient = accept
      simp [accept, fiveProjectMoneyTransferProfile, hdistinct.symm]

/-- Package a profile after proving that every actor chose from the physical
stage's finite menu. -/
def finitePhysicalSelectedProfile
    (stage : FinitePhysicalChoiceStage FiveProjectPhysicalAgent
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Nat)
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (selected : ∀ agent, profile agent ∈ stage.choices.menu agent) :
    stage.choices.Profile :=
  ⟨profile, selected⟩

/-- A completion-factor purchase stage generated from the same action profile
that the physical interpreter executes. The menu includes the supplier's
unilateral offer and the borrower's unilateral acceptance alongside idling. -/
def fiveProjectFactorPurchaseChoiceStage
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ)
    (hdistinct : seller ≠ buyer)
    (hsupply : 1 ≤ state.stock seller fiveProjectCompletionGood)
    (hcash : price ≤ state.stock buyer fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat := by
  let profile := fiveProjectFactorPurchaseProfile seller buyer price
  let active : Finset FiveProjectPhysicalAgent := {seller, buyer}
  have hnonidle : ∀ agent, agent ∈ active →
      profile agent ≠ EconomyAction.idle := by
    intro agent hagent
    simp only [active, Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with hs | hb
    · subst agent
      simp [profile, fiveProjectFactorPurchaseProfile]
    · subst agent
      simp [profile, fiveProjectFactorPurchaseProfile, hdistinct.symm]
  have hwellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent) := by
    intro agent
    by_cases hs : agent = seller
    · subst agent
      simp [profile, fiveProjectFactorPurchaseProfile,
        EconomyAction.WellFormed, hdistinct]
    · by_cases hb : agent = buyer
      · subst agent
        simp [profile, fiveProjectFactorPurchaseProfile,
          EconomyAction.WellFormed, hs]
      · simp [profile, fiveProjectFactorPurchaseProfile, hs, hb,
          EconomyAction.WellFormed]
  have hprofileAffordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent) := by
    intro agent good
    by_cases hs : agent = seller
    · subst agent
      simp only [profile, fiveProjectFactorPurchaseProfile,
        ↓reduceIte, rawActionUse]
      split_ifs with hgood
      · simpa [hgood] using hsupply
      · exact Nat.zero_le _
    · by_cases hb : agent = buyer
      · subst agent
        simp only [profile, fiveProjectFactorPurchaseProfile, hs,
          ↓reduceIte, rawActionUse]
        split_ifs with hgood
        · simpa [hgood] using hcash
        · exact Nat.zero_le _
      · simp [profile, fiveProjectFactorPurchaseProfile, hs, hb, rawActionUse]
  exact finitePhysicalStageOfProfile state profile active
    hnonidle hwellFormed hprofileAffordable

/-- The complete matched purchase profile belongs to the stage's generated
menu product, while each unilateral action is also a generated branch. -/
theorem fiveProjectFactorPurchaseChoiceStage_branches
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ)
    (hdistinct : seller ≠ buyer)
    (hsupply : 1 ≤ state.stock seller fiveProjectCompletionGood)
    (hcash : price ≤ state.stock buyer fiveProjectMoneyGood) :
    let stage := fiveProjectFactorPurchaseChoiceStage
      state seller buyer price hdistinct hsupply hcash
    (∃ offerProfile ∈ stage.choices.profiles,
      offerProfile.1 seller =
        EconomyAction.offer seller buyer 1 fiveProjectCompletionGood price fiveProjectMoneyGood ∧
      offerProfile.1 buyer = EconomyAction.idle) ∧
    (∃ acceptProfile ∈ stage.choices.profiles,
      acceptProfile.1 buyer =
        EconomyAction.accept buyer seller 1 fiveProjectCompletionGood price fiveProjectMoneyGood ∧
      acceptProfile.1 seller = EconomyAction.idle) ∧
    ∃ matchedProfile ∈ stage.choices.profiles,
      matchedProfile.1 seller =
        EconomyAction.offer seller buyer 1 fiveProjectCompletionGood price fiveProjectMoneyGood ∧
      matchedProfile.1 buyer =
        EconomyAction.accept buyer seller 1
          fiveProjectCompletionGood price fiveProjectMoneyGood := by
  let stage := fiveProjectFactorPurchaseChoiceStage
    state seller buyer price hdistinct hsupply hcash
  let offer : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .offer seller buyer 1 fiveProjectCompletionGood price fiveProjectMoneyGood
  let accept : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .accept buyer seller 1 fiveProjectCompletionGood price fiveProjectMoneyGood
  have hoff : offer ∈ stage.choices.menu seller := by
    simp [stage, fiveProjectFactorPurchaseChoiceStage,
      finitePhysicalStageOfProfile, fiveProjectFactorPurchaseProfile,
      FiniteChoiceStage.ofProfile, offer, hdistinct]
  have haccept : accept ∈ stage.choices.menu buyer := by
    simp [stage, fiveProjectFactorPurchaseChoiceStage,
      finitePhysicalStageOfProfile, fiveProjectFactorPurchaseProfile,
      FiniteChoiceStage.ofProfile, accept, hdistinct.symm]
  have hmatched : ∀ agent,
      fiveProjectFactorPurchaseProfile seller buyer price agent ∈
        stage.choices.menu agent := by
    intro agent
    by_cases hs : agent = seller
    · subst agent
      simp [fiveProjectFactorPurchaseProfile, stage,
        fiveProjectFactorPurchaseChoiceStage, finitePhysicalStageOfProfile,
        FiniteChoiceStage.ofProfile, hdistinct]
    · by_cases hb : agent = buyer
      · subst agent
        simp [fiveProjectFactorPurchaseProfile, stage,
          fiveProjectFactorPurchaseChoiceStage, finitePhysicalStageOfProfile,
          FiniteChoiceStage.ofProfile, hs]
      · simp [fiveProjectFactorPurchaseProfile, stage,
          fiveProjectFactorPurchaseChoiceStage, finitePhysicalStageOfProfile,
          FiniteChoiceStage.ofProfile, hs, hb]
  refine ⟨?_, ?_, ?_⟩
  · let profile := stage.choices.unilateralProfile seller offer hoff
    refine ⟨profile, stage.choices.unilateralProfile_mem_profiles seller offer hoff,
      ?_, ?_⟩
    · exact stage.choices.unilateralProfile_self seller offer hoff
    · exact stage.choices.unilateralProfile_other seller buyer offer hoff hdistinct.symm
  · let profile := stage.choices.unilateralProfile buyer accept haccept
    refine ⟨profile, stage.choices.unilateralProfile_mem_profiles buyer accept haccept,
      ?_, ?_⟩
    · exact stage.choices.unilateralProfile_self buyer accept haccept
    · exact stage.choices.unilateralProfile_other buyer seller accept haccept hdistinct
  · let profile := finitePhysicalSelectedProfile stage
      (fiveProjectFactorPurchaseProfile seller buyer price) hmatched
    refine ⟨profile, stage.choices.mem_profiles profile, ?_, ?_⟩
    · change fiveProjectFactorPurchaseProfile seller buyer price seller = offer
      simp [offer, fiveProjectFactorPurchaseProfile]
    · change fiveProjectFactorPurchaseProfile seller buyer price buyer = accept
      simp [accept, fiveProjectFactorPurchaseProfile, hdistinct.symm]

/-- The actual matched purchase transition is exactly the transition selected
from its finite physical choice stage. -/
theorem fiveProjectFactorPurchase_is_choiceStage_advance
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ)
    (hdistinct : seller ≠ buyer)
    (hsupply : 1 ≤ state.stock seller fiveProjectCompletionGood)
    (hcash : price ≤ state.stock buyer fiveProjectMoneyGood) :
    let stage := fiveProjectFactorPurchaseChoiceStage
      state seller buyer price hdistinct hsupply hcash
    executeFiveProjectFactorPurchase state seller buyer price =
      some (stage.advance
        (finitePhysicalSelectedProfile stage
          (fiveProjectFactorPurchaseProfile seller buyer price) (by
            intro agent
            by_cases hs : agent = seller
            · subst agent
              simp [stage, fiveProjectFactorPurchaseChoiceStage,
                finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                fiveProjectFactorPurchaseProfile, hdistinct]
            · by_cases hb : agent = buyer
              · subst agent
                simp [stage, fiveProjectFactorPurchaseChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectFactorPurchaseProfile, hs]
              · simp [stage, fiveProjectFactorPurchaseChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectFactorPurchaseProfile, hs, hb]))) := by
  let stage := fiveProjectFactorPurchaseChoiceStage
    state seller buyer price hdistinct hsupply hcash
  have hselected : ∀ agent,
      fiveProjectFactorPurchaseProfile seller buyer price agent ∈
        stage.choices.menu agent := by
    intro agent
    by_cases hs : agent = seller
    · subst agent
      simp [stage, fiveProjectFactorPurchaseChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectFactorPurchaseProfile, hdistinct]
    · by_cases hb : agent = buyer
      · subst agent
        simp [stage, fiveProjectFactorPurchaseChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectFactorPurchaseProfile, hs]
      · simp [stage, fiveProjectFactorPurchaseChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectFactorPurchaseProfile, hs, hb]
  let selected := finitePhysicalSelectedProfile stage
    (fiveProjectFactorPurchaseProfile seller buyer price) hselected
  have htransition :=
    FinitePhysicalChoiceStage.advanceIfAffordable_eq_some_advance stage selected
  simpa [executeFiveProjectFactorPurchase, stage, selected,
    fiveProjectFactorPurchaseChoiceStage, finitePhysicalStageOfProfile,
    finitePhysicalSelectedProfile, fiveProjectFactorPurchaseProfile] using htransition

/-- Initial money belongs to the bank, five entrepreneurs, household, and final
customer; physical factor stocks remain with the supplier and household until
consumption or a matched sale occurs. Notes, the household cash transfer, and
loan advances are executed as later stages. -/
def fiveProjectFactorInitialStateWithCashBuffers (D : FiveProjectRegimeData)
    (cashBuffer : Fin 5 → ℕ) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat :=
  PhysicalState.zeroServices fun agent good =>
    match good.val with
    | 0 =>
        match agent.val with
        | 1 => cashBuffer 0
        | 2 => cashBuffer 1
        | 3 => cashBuffer 2
        | 4 => cashBuffer 3
        | 5 => cashBuffer 4
        | 6 => fiveProjectCustomerMoneyEndowment
        | 7 => D.bankMoney
        | 8 => D.householdMoneyEndowment
        | _ => 0
    | 1 =>
        if agent = fiveProjectFactorSupplier then D.supplierFactorStock
        else if agent = fiveProjectHousehold then D.householdFactorEndowment
        else 0
    | 3 => if agent = fiveProjectFactorSupplier then D.supplierEarlyInputStock else 0
    | 5 => if agent = fiveProjectPhysicalBorrower 0 then 1 else 0
    | 6 => if agent = fiveProjectPhysicalBorrower 1 then 1 else 0
    | 7 => if agent = fiveProjectPhysicalBorrower 2 then 1 else 0
    | 8 => if agent = fiveProjectPhysicalBorrower 3 then 1 else 0
    | 9 => if agent = fiveProjectPhysicalBorrower 4 then 1 else 0
    | 10 => if agent = fiveProjectBank then 1 else 0
    | _ => 0

/-- Initial state of the named scenario, with the specified entrepreneur cash
buffers as its specialization. -/
def fiveProjectFactorInitialState (D : FiveProjectRegimeData) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat :=
  fiveProjectFactorInitialStateWithCashBuffers D fiveProjectCashBuffer

/-- Fiduciary notes specified by a regime are issued by the bank operation
before the loan auction's funded advances. The amount comes directly from the
regime's explicit note-issuance field. -/
def issueFiveProjectFiduciaryNotes (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  let profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
    fun actor =>
      if actor = fiveProjectBank then
        .operate (.issueFiduciaryNotes D.fiduciaryNotesIssued)
      else .idle
  advanceIfAffordable fiveProjectPhysicalOperations state profile

/-- A matched, zero-price transfer of money. Both parties must enact the
corresponding offer and acceptance; the sender must hold the full quantity in
the common pre-state. -/
def executeFiveProjectMoneyTransfer
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  if quantity = 0 then some state
  else if sender = recipient then none
  else advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectMoneyTransferProfile sender recipient quantity)

/-- For a positive affordable transfer, the executable transition equals the
matched profile's branch in the choice stage that also contains the two
unilateral alternatives. -/
theorem fiveProjectMoneyTransfer_is_choiceStage_advance
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ)
    (hdistinct : sender ≠ recipient) (hpositive : 0 < quantity)
    (hfunded : quantity ≤ state.stock sender fiveProjectMoneyGood) :
    let stage := fiveProjectMoneyTransferChoiceStage
      state sender recipient quantity hdistinct hfunded
    executeFiveProjectMoneyTransfer state sender recipient quantity =
      some (stage.advance
        (finitePhysicalSelectedProfile stage
          (fiveProjectMoneyTransferProfile sender recipient quantity) (by
            intro agent
            by_cases hs : agent = sender
            · subst agent
              simp [stage, fiveProjectMoneyTransferChoiceStage,
                finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                fiveProjectMoneyTransferProfile, hdistinct]
            · by_cases hr : agent = recipient
              · subst agent
                simp [stage, fiveProjectMoneyTransferChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectMoneyTransferProfile, hs]
              · simp [stage, fiveProjectMoneyTransferChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectMoneyTransferProfile, hs, hr]))) := by
  let stage := fiveProjectMoneyTransferChoiceStage
    state sender recipient quantity hdistinct hfunded
  have hselected : ∀ agent,
      fiveProjectMoneyTransferProfile sender recipient quantity agent ∈
        stage.choices.menu agent := by
    intro agent
    by_cases hs : agent = sender
    · subst agent
      simp [stage, fiveProjectMoneyTransferChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectMoneyTransferProfile, hdistinct]
    · by_cases hr : agent = recipient
      · subst agent
        simp [stage, fiveProjectMoneyTransferChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectMoneyTransferProfile, hs]
      · simp [stage, fiveProjectMoneyTransferChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectMoneyTransferProfile, hs, hr]
  let selected := finitePhysicalSelectedProfile stage
    (fiveProjectMoneyTransferProfile sender recipient quantity) hselected
  have htransition :=
    FinitePhysicalChoiceStage.advanceIfAffordable_eq_some_advance stage selected
  simpa [executeFiveProjectMoneyTransfer, stage, selected, hpositive.ne',
    hdistinct, fiveProjectMoneyTransferChoiceStage, finitePhysicalStageOfProfile,
    finitePhysicalSelectedProfile, fiveProjectMoneyTransferProfile] using htransition

/-- A successful non-self money transfer obeys the physical interpreter's
inventory balance. The zero-quantity case is the identity already specified
by the executor; positive transfers require a matched offer and acceptance. -/
theorem executeFiveProjectMoneyTransfer_balances
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ)
    (hne : sender ≠ recipient)
    (hstep : executeFiveProjectMoneyTransfer state sender recipient quantity =
      some next) :
    next.stock sender fiveProjectMoneyGood + quantity =
        state.stock sender fiveProjectMoneyGood ∧
      next.stock recipient fiveProjectMoneyGood =
        state.stock recipient fiveProjectMoneyGood + quantity := by
  by_cases hzero : quantity = 0
  · have hstep' : some state = some next := by
      simpa only [executeFiveProjectMoneyTransfer, ite_eq_left hzero] using hstep
    cases Option.some.inj hstep'
    simp [hzero]
  · let profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
        (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
      fiveProjectMoneyTransferProfile sender recipient quantity
    have hprofileStep : advanceIfAffordable fiveProjectPhysicalOperations state profile =
        some next := by
      simpa [executeFiveProjectMoneyTransfer, fiveProjectMoneyTransferProfile,
        hzero, hne, profile] using hstep
    have hbalance := advanceIfAffordable_matchedTransfer_balance
      fiveProjectPhysicalOperations state next profile sender recipient quantity
      fiveProjectMoneyGood 0 fiveProjectMoneyGood hprofileStep
      (by simp [profile, fiveProjectMoneyTransferProfile])
      (by simp [profile, fiveProjectMoneyTransferProfile, hne.symm])
    refine ⟨?_, ?_⟩
    · simpa [fiveProjectMoneyGood] using hbalance.1 fiveProjectMoneyGood
    · simpa [fiveProjectMoneyGood] using hbalance.2 fiveProjectMoneyGood

/-- A positive self-transfer is not a matched bilateral exchange and is
rejected by the execution helper. -/
theorem executeFiveProjectMoneyTransfer_self_positive
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (agent : FiveProjectPhysicalAgent) (quantity : ℕ) (hquantity : 0 < quantity) :
    executeFiveProjectMoneyTransfer state agent agent quantity = none := by
  simp [executeFiveProjectMoneyTransfer, Nat.ne_of_gt hquantity]

/-- In the named saving regime the household exchanges its principal for the
deposit claim. Other regimes have no household deposit transaction; a
zero-sized cash transfer is the identity transition. -/
def executeFiveProjectHouseholdCashTransfer (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  if D.householdMoneyTransferred = fiveProjectHouseholdDepositTerms.principal then
    executeFiveProjectDepositOrigination state
  else
    executeFiveProjectMoneyTransfer state fiveProjectHousehold fiveProjectBank
      D.householdMoneyTransferred

/-- A funded named deposit exchange transfers exactly its principal and its
claim through the ordinary matched-transfer interpreter. -/
theorem executeFiveProjectDepositOrigination_succeeds
    (D : FiveProjectRegimeData)
    (hprincipal : D.householdMoneyTransferred =
      fiveProjectHouseholdDepositTerms.principal) :
    ∃ next,
      executeFiveProjectDepositOrigination (fiveProjectFactorInitialState D) =
        some next ∧
      next.stock fiveProjectHousehold fiveProjectMoneyGood +
          fiveProjectHouseholdDepositTerms.principal = D.householdMoneyEndowment ∧
      next.stock fiveProjectBank fiveProjectMoneyGood =
        D.bankMoney + fiveProjectHouseholdDepositTerms.principal ∧
      next.stock fiveProjectHousehold fiveProjectDepositClaimGood = 1 ∧
      next.stock fiveProjectBank fiveProjectDepositClaimGood = 0 := by
  let state := fiveProjectFactorInitialState D
  let profile := fiveProjectDepositOriginationProfile
  have hinitialHousehold : state.stock fiveProjectHousehold fiveProjectMoneyGood =
      D.householdMoneyEndowment := by rfl
  have hhouseholdCash : fiveProjectHouseholdDepositTerms.principal ≤
      state.stock fiveProjectHousehold fiveProjectMoneyGood := by
    calc
      fiveProjectHouseholdDepositTerms.principal = D.householdMoneyTransferred :=
        hprincipal.symm
      _ ≤ D.householdMoneyEndowment := D.transfer_affordable
      _ = state.stock fiveProjectHousehold fiveProjectMoneyGood :=
        hinitialHousehold.symm
  have hbankClaim : 1 ≤ state.stock fiveProjectBank fiveProjectDepositClaimGood := by
    change 1 ≤ 1
    omega
  let stage := fiveProjectDepositOriginationChoiceStage state
    hhouseholdCash hbankClaim
  let selected : stage.choices.Profile :=
    ⟨profile, fiveProjectDepositOriginationChoiceStage_profile_mem state
      hhouseholdCash hbankClaim⟩
  let next := stage.advance selected
  have hstep : executeFiveProjectDepositOrigination state = some next := by
    simp [executeFiveProjectDepositOrigination, hhouseholdCash, hbankClaim,
      stage, selected, next, state, profile]
  have hphysical : advanceIfAffordable fiveProjectPhysicalOperations
      state profile = some next := by
    have h := stage.advanceIfAffordable_eq_some_advance selected
    have hselected : stage.advance
        ⟨profile, fiveProjectDepositOriginationChoiceStage_profile_mem state
          hhouseholdCash hbankClaim⟩ = next := by rfl
    rw [hselected] at h
    simpa [fiveProjectDepositOriginationChoiceStage, stage,
      finitePhysicalStageOfProfile] using h
  have hbalances := advanceIfAffordable_matchedTransfer_balance
    fiveProjectPhysicalOperations state next profile fiveProjectHousehold
    fiveProjectBank fiveProjectHouseholdDepositTerms.principal
    fiveProjectMoneyGood 1 fiveProjectDepositClaimGood hphysical
    (by simp [profile, fiveProjectDepositOriginationProfile,
      fiveProjectHouseholdDepositTerms])
    (by simp [profile, fiveProjectDepositOriginationProfile,
      fiveProjectHouseholdDepositTerms, fiveProjectHousehold_ne_bank.symm])
  refine ⟨next, hstep, ?_, ?_, ?_, ?_⟩
  · have h := hbalances.1 fiveProjectMoneyGood
    rw [hinitialHousehold] at h
    simpa [fiveProjectMoneyGood, fiveProjectDepositClaimGood] using h
  · have hinitialBank : state.stock fiveProjectBank fiveProjectMoneyGood =
        D.bankMoney := by rfl
    have h := hbalances.2 fiveProjectMoneyGood
    rw [hinitialBank] at h
    simpa [fiveProjectMoneyGood, fiveProjectDepositClaimGood] using h
  · have hinitialClaim :
        state.stock fiveProjectHousehold fiveProjectDepositClaimGood = 0 := by rfl
    have h := hbalances.1 fiveProjectDepositClaimGood
    rw [hinitialClaim] at h
    simpa [fiveProjectMoneyGood, fiveProjectDepositClaimGood] using h
  · have hinitialClaim :
        state.stock fiveProjectBank fiveProjectDepositClaimGood = 1 := by rfl
    have h := hbalances.2 fiveProjectDepositClaimGood
    rw [hinitialClaim] at h
    simpa [fiveProjectMoneyGood, fiveProjectDepositClaimGood] using h

/-- Any household cash transfer recorded as affordable by the regime data
executes as a matched transfer from the initial physical cash balance. This
checks the funding source against the interpreter. In the saving regime the
cash leg is matched to the issued deposit claim; this physical contract alone
does not establish purposeful saving. -/
theorem executeFiveProjectHouseholdCashTransfer_succeeds_without_deposit
    (D : FiveProjectRegimeData)
    (hnotDeposit : D.householdMoneyTransferred ≠
      fiveProjectHouseholdDepositTerms.principal) :
    ∃ next,
      executeFiveProjectHouseholdCashTransfer D (fiveProjectFactorInitialState D) =
        some next ∧
      next.stock fiveProjectHousehold fiveProjectMoneyGood +
          D.householdMoneyTransferred = D.householdMoneyEndowment ∧
      next.stock fiveProjectBank fiveProjectMoneyGood =
        D.bankMoney + D.householdMoneyTransferred := by
  have hinitialHousehold :
      (fiveProjectFactorInitialState D).stock fiveProjectHousehold fiveProjectMoneyGood =
        D.householdMoneyEndowment := by
    rfl
  have hinitialBank :
      (fiveProjectFactorInitialState D).stock fiveProjectBank fiveProjectMoneyGood =
        D.bankMoney := by
    rfl
  by_cases hzero : D.householdMoneyTransferred = 0
  · refine ⟨fiveProjectFactorInitialState D, ?_, ?_, ?_⟩
    · norm_num [executeFiveProjectHouseholdCashTransfer,
        executeFiveProjectMoneyTransfer, fiveProjectHouseholdDepositTerms, hzero]
    · rw [hinitialHousehold, hzero]
      omega
    · rw [hinitialBank, hzero]
      omega
  · have hpositive : 0 < D.householdMoneyTransferred := Nat.pos_of_ne_zero hzero
    have hdistinct : fiveProjectHousehold ≠ fiveProjectBank := by decide
    have hfunded : D.householdMoneyTransferred ≤
        (fiveProjectFactorInitialState D).stock fiveProjectHousehold
          fiveProjectMoneyGood := by
      rw [hinitialHousehold]
      exact D.transfer_affordable
    let stage := fiveProjectMoneyTransferChoiceStage
      (fiveProjectFactorInitialState D) fiveProjectHousehold fiveProjectBank
      D.householdMoneyTransferred hdistinct hfunded
    let selected := finitePhysicalSelectedProfile stage
      (fiveProjectMoneyTransferProfile fiveProjectHousehold fiveProjectBank
        D.householdMoneyTransferred) (by
          intro agent
          by_cases hhousehold : agent = fiveProjectHousehold
          · subst agent
            simp [stage, fiveProjectMoneyTransferChoiceStage,
              finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
              fiveProjectMoneyTransferProfile, hdistinct]
          · by_cases hbank : agent = fiveProjectBank
            · subst agent
              simp [stage, fiveProjectMoneyTransferChoiceStage,
                finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                fiveProjectMoneyTransferProfile, hhousehold]
            · simp [stage, fiveProjectMoneyTransferChoiceStage,
                finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                fiveProjectMoneyTransferProfile, hhousehold, hbank])
    have hstep : executeFiveProjectHouseholdCashTransfer D
        (fiveProjectFactorInitialState D) = some (stage.advance selected) := by
      simpa [executeFiveProjectHouseholdCashTransfer, hnotDeposit,
        stage, selected] using
        fiveProjectMoneyTransfer_is_choiceStage_advance
          (fiveProjectFactorInitialState D) fiveProjectHousehold fiveProjectBank
          D.householdMoneyTransferred hdistinct hpositive hfunded
    have hbalances := executeFiveProjectMoneyTransfer_balances
      (fiveProjectFactorInitialState D) (stage.advance selected)
      fiveProjectHousehold fiveProjectBank D.householdMoneyTransferred hdistinct
      (by simpa [executeFiveProjectHouseholdCashTransfer, hnotDeposit] using hstep)
    refine ⟨stage.advance selected, hstep, ?_, ?_⟩
    · have hhousehold := hbalances.1
      rw [hinitialHousehold] at hhousehold
      exact hhousehold
    · have hbank := hbalances.2
      rw [hinitialBank] at hbank
      exact hbank

/-- The household-source stage succeeds either as the explicit named deposit
contract or as the existing cash-transfer specialization. -/
theorem executeFiveProjectHouseholdCashTransfer_succeeds
    (D : FiveProjectRegimeData) :
    ∃ next,
      executeFiveProjectHouseholdCashTransfer D (fiveProjectFactorInitialState D) =
        some next ∧
      next.stock fiveProjectHousehold fiveProjectMoneyGood +
          D.householdMoneyTransferred = D.householdMoneyEndowment ∧
      next.stock fiveProjectBank fiveProjectMoneyGood =
        D.bankMoney + D.householdMoneyTransferred := by
  by_cases hdeposit : D.householdMoneyTransferred =
      fiveProjectHouseholdDepositTerms.principal
  · obtain ⟨next, hstep, hhousehold, hbank, _hclaim, _hbankClaim⟩ :=
      executeFiveProjectDepositOrigination_succeeds D hdeposit
    refine ⟨next, ?_, ?_, ?_⟩
    · simpa [executeFiveProjectHouseholdCashTransfer, hdeposit] using hstep
    · simpa [hdeposit] using hhousehold
    · simpa [hdeposit] using hbank
  · exact executeFiveProjectHouseholdCashTransfer_succeeds_without_deposit D hdeposit

/-- Execute the principal advances for the loan auction's funded prefix. The
fixed market has unit principal, and each advance is a separate matched
transfer from the bank to the named borrower. -/
def executeFiveProjectLoanAdvances
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | bid :: rest =>
      (executeFiveProjectLoanAdvance state bid).bind
        fun next => executeFiveProjectLoanAdvances next rest

/-- Execute each scheduled loan transfer and return exactly the bids whose
matched transfer succeeded. -/
def executeFiveProjectLoanAdvancesWithTrace
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat ×
        List LoanReservationBid)
  | [] => some (state, [])
  | bid :: rest =>
      (executeFiveProjectLoanAdvance state bid).bind
        fun next =>
          (executeFiveProjectLoanAdvancesWithTrace next rest).map fun (final, advances) =>
            (final, bid :: advances)

/-- Clear the loan market using bank money in the state produced by the note
issuance and household-transfer branches. These source stages therefore affect
loan capacity through their executed inventory changes. -/
def fiveProjectLoanOutcomeAfterSourcesFor (D : FiveProjectRegimeData) :
    Option LoanAuctionResult :=
  (issueFiveProjectFiduciaryNotes D (fiveProjectFactorInitialState D)).bind
    fun noted =>
      (executeFiveProjectHouseholdCashTransfer D noted).map fun transferred =>
        clearLoanMarket fiveProjectLoanMarket
          (transferred.stock fiveProjectBank fiveProjectMoneyGood)

/-- Execute funding and preserve the matched advance list alongside the
resulting physical state. A list appears here only when every generated
advance transfer has executed through the interpreter. -/
def fiveProjectFundedTraceFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat ×
      List LoanReservationBid) :=
  (issueFiveProjectFiduciaryNotes D (fiveProjectFactorInitialState D)).bind
    fun noted =>
      (executeFiveProjectHouseholdCashTransfer D noted).bind fun transferred =>
        (fiveProjectLoanOutcomeAfterSourcesFor D).bind fun outcome =>
          executeFiveProjectLoanAdvancesWithTrace transferred outcome.funded

def fiveProjectExecutedLoanAdvancesFor (D : FiveProjectRegimeData) :
    Option (List LoanReservationBid) :=
  (fiveProjectFundedTraceFor D).map Prod.snd

/-- Execute early-input purchases and one-to-one capital conversion for the
loans whose advances actually matched. A failed purchase or conversion stops
this selected execution; no capital is inferred from a loan quote alone. -/
def executeFiveProjectEarlyCapitalPlan
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | bid :: rest =>
      (executeFiveProjectEarlyInputPurchase state bid.borrower).bind fun purchased =>
        (executeFiveProjectCapitalConversion purchased bid.borrower).bind fun capitalized =>
          executeFiveProjectEarlyCapitalPlan capitalized rest

/-- State after the executed funding branch and its matched early-input and
capital-formation stages. The list of projects comes from actual advances. -/
def fiveProjectCapitalizedTraceFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat ×
      List LoanReservationBid) :=
  (fiveProjectFundedTraceFor D).bind fun (state, advances) =>
    (executeFiveProjectEarlyCapitalPlan state advances).map fun capitalized =>
      (capitalized, advances)

/-- State after the executed funding branch and capital formation. -/
def fiveProjectCapitalizedStateFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectCapitalizedTraceFor D).map Prod.fst

/-- Build the pre-production physical state by executing note issuance,
the household cash transfer, and the loan auction's actual funded advances in sequence.
The loan-auction source total and physical bank receipts are the same regime
data used to compute capacity. -/
def fiveProjectFundedStateFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  fiveProjectFundedTraceFor D |>.map Prod.fst

/-- Read a money balance after the regime's notes, household transfer, and funded loan
advances have executed, before household factor consumption and factor trades.
-/
def fiveProjectFundedMoneyBalance? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) : Option ℕ :=
  (fiveProjectFundedStateFor D).map fun state =>
    state.stock agent fiveProjectMoneyGood

/-- The auction's funded prefixes are transferred as principal from the bank
in every named regime. The fiduciary notes and household cash transfer provide the
additional two advances in the corresponding cases. -/
theorem fiveProject_named_loan_advances_execute :
    (fiveProjectFundedStateFor (fiveProjectRegimeData .baseline)).isSome = true ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .baseline)
      fiveProjectBank = some 0 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .baseline)
      (fiveProjectPhysicalBorrower 0) = some 4 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .baseline)
      (fiveProjectPhysicalBorrower 1) = some 4 ∧
    (fiveProjectFundedStateFor (fiveProjectRegimeData .fiduciaryExpansion)).isSome =
      true ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      fiveProjectBank = some 0 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 0) = some 4 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 1) = some 4 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 2) = some 2 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 3) = some 2 ∧
    (fiveProjectFundedStateFor (fiveProjectRegimeData .householdTransfer)).isSome =
      true ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectBank = some 0 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectHousehold = some 0 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 2) = some 2 ∧
    fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 3) = some 2 := by
  decide

/-- At the funding checkpoint before early-input purchases, the two marginal
fiduciary borrowers each hold their one-unit buffer plus the one-unit loan
advance. This records the intermediate balance only; the later current-cash
auction is run after early-input expenditure and uses the resulting inventory.
The projected buffer-and-return test remains a separate forecast calculation.
-/
theorem fiveProject_marginal_borrowers_funded_balance_exceeds_buffer_test :
    ∀ entrepreneur, 2 ≤ entrepreneur.val → entrepreneur.val < 4 →
      fiveProjectFundedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
          (fiveProjectPhysicalBorrower entrepreneur) = some 2 ∧
      fiveProjectCashBuffer entrepreneur = 1 ∧
      2 ≤ fiveProjectCashBuffer entrepreneur + 1 ∧
      ¬ projectPassesCashBufferAndReturnTestAt
        (fiveProjectLoanBid entrepreneur) 4 2 := by
  decide

/-- Process the market's ordered factor-demand list. The supplier with the
lower agent index offers its stock first; remaining units come from the
household when that household's regime data marks them as offered. -/
def fiveProjectFactorSellerPlan (supplierStock householdStock : ℕ) :
    List LoanReservationBid →
      Option (List (Fin 5 × FiveProjectPhysicalAgent))
  | [] => some []
  | bid :: rest =>
      if 0 < supplierStock then
        (fiveProjectFactorSellerPlan (supplierStock - 1) householdStock rest).map
          fun sales => (bid.borrower, fiveProjectFactorSupplier) :: sales
      else if 0 < householdStock then
        (fiveProjectFactorSellerPlan supplierStock (householdStock - 1) rest).map
          fun sales => (bid.borrower, fiveProjectHousehold) :: sales
      else none

/-- Execute a seller-assigned factor plan in list order. Each unit is a
separate matched offer and acceptance, so a later purchase uses the state
produced by earlier transfers. -/
def executeFiveProjectFactorPlan
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (price : ℕ) : List (Fin 5 × FiveProjectPhysicalAgent) →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | (project, seller) :: rest =>
      (executeFiveProjectFactorPurchase state seller
        (fiveProjectPhysicalBorrower project) price).bind fun next =>
          executeFiveProjectFactorPlan next price rest

/-- Execute ordinary household factor consumption before the factor market,
using the regime's explicit consumption quantity. -/
def prepareFiveProjectHouseholdFactors (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  let action :=
    if D.householdFactorsConsumed = 0 then EconomyAction.idle
    else .operate (.consumeHouseholdFactors D.householdFactorsConsumed)
  let profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
    fun actor => if actor = fiveProjectHousehold then action else .idle
  advanceIfAffordable fiveProjectPhysicalOperations state profile

/-- Remaining offered completion factors are capped by both the regime's
stated offer and the seller's current physical stock. Unoffered household
stock remains with the household. -/
def fiveProjectAvailableSupplierFactors (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) : ℕ :=
  min D.supplierFactorStock (state.stock fiveProjectFactorSupplier
    fiveProjectCompletionGood)

def fiveProjectAvailableHouseholdFactors (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) : ℕ :=
  min D.householdFactorsOffered (state.stock fiveProjectHousehold
    fiveProjectCompletionGood)

/-- Shared factor clearing at one physical market node. It receives the
already matched advances and published repayment quote, reads current cash
from the supplied inventory, and combines present affordability with
projected output receipts. -/
def fiveProjectClearFactorMarketAtState
    (actualAdvances : List LoanReservationBid) (quotedRepayment supply : ℕ)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (ℕ × List LoanReservationBid) :=
  let currentCash : LoanReservationBid → ℕ := fun bid => state.stock
    (fiveProjectPhysicalBorrower bid.borrower) fiveProjectMoneyGood
  let projectedOutput : LoanReservationBid → ℕ :=
    fun bid => fiveProjectOutput bid.borrower
  let greatestCash := actualAdvances.foldl
    (fun greatest bid => max greatest (currentCash bid)) 0
  (ascendingCompletionFactorPriceAtCurrentCash? actualAdvances quotedRepayment 1 supply
    greatestCash currentCash projectedOutput).map fun price =>
      (price, factorDemandingProjectsAtCurrentCash actualAdvances quotedRepayment price
        currentCash projectedOutput)

/-- Any result returned by the current-state factor clock respects its
offered-stock constraint, regardless of the cash balances that determine its
price and eligible bids. -/
theorem fiveProjectClearFactorMarketAtState_projects_le_supply
    (actualAdvances : List LoanReservationBid) (quotedRepayment supply : ℕ)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (price : ℕ) (projects : List LoanReservationBid)
    (hclear : fiveProjectClearFactorMarketAtState actualAdvances
      quotedRepayment supply state = some (price, projects)) :
    projects.length ≤ supply := by
  let currentCash : LoanReservationBid → ℕ := fun bid => state.stock
    (fiveProjectPhysicalBorrower bid.borrower) fiveProjectMoneyGood
  let projectedOutput : LoanReservationBid → ℕ :=
    fun bid => fiveProjectOutput bid.borrower
  let greatestCash := actualAdvances.foldl
    (fun greatest bid => max greatest (currentCash bid)) 0
  have hclear' :
      (ascendingCompletionFactorPriceAtCurrentCash? actualAdvances
        quotedRepayment 1 supply greatestCash currentCash projectedOutput).map
        (fun selectedPrice =>
          (selectedPrice, factorDemandingProjectsAtCurrentCash actualAdvances
            quotedRepayment selectedPrice currentCash projectedOutput)) =
        some (price, projects) := by
    simpa [fiveProjectClearFactorMarketAtState, currentCash, projectedOutput,
      greatestCash] using hclear
  rcases Option.map_eq_some_iff.mp hclear' with
    ⟨selectedPrice, hprice, hresult⟩
  have hprojects :
      factorDemandingProjectsAtCurrentCash actualAdvances quotedRepayment
        selectedPrice currentCash projectedOutput = projects := by
    exact (Prod.mk.inj hresult).2
  rw [← hprojects]
  exact factorDemandingProjectsAtCurrentCash_length_le_supply
    actualAdvances quotedRepayment 1 supply greatestCash selectedPrice
    currentCash projectedOutput hprice

/-- Clear completion factors against currently offered stock and the actual
funding branch. This named-regime wrapper specializes the shared state-based
factor market to the regime's matched advances and published quote. -/
def fiveProjectFactorMarketAtStateFor (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (ℕ × List LoanReservationBid) :=
  (fiveProjectLoanOutcomeAfterSourcesFor D).bind fun outcome =>
    outcome.quotedRepayment.bind fun quote =>
      (fiveProjectExecutedLoanAdvancesFor D).bind fun actualAdvances =>
        let supply := fiveProjectAvailableSupplierFactors D state +
          fiveProjectAvailableHouseholdFactors D state
        fiveProjectClearFactorMarketAtState actualAdvances quote supply state

/-- State immediately before factor-market clearing, after the executed
funding branch and the household's stated factor-consumption operation. -/
def fiveProjectPreparedFactorStateFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectCapitalizedStateFor D).bind fun state =>
    prepareFiveProjectHouseholdFactors D state

/-- The factor-market result selected from that prepared branch state. -/
def fiveProjectExecutedFactorMarketFor (D : FiveProjectRegimeData) :
    Option (ℕ × List LoanReservationBid) :=
  (fiveProjectPreparedFactorStateFor D).bind fun state =>
    fiveProjectFactorMarketAtStateFor D state

def fiveProjectExecutedFactorPriceFor (D : FiveProjectRegimeData) : Option ℕ :=
  (fiveProjectExecutedFactorMarketFor D).map Prod.fst

def fiveProjectExecutedFactorDemandFor (D : FiveProjectRegimeData) :
    Option (List LoanReservationBid) :=
  (fiveProjectExecutedFactorMarketFor D).map Prod.snd

/-- Execute the factor purchases implied by one regime's computed market
result. A missing market price or purchase list produces no execution. -/
def fiveProjectFactorExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectPreparedFactorStateFor D).bind fun state =>
    (fiveProjectFactorMarketAtStateFor D state).bind fun (price, demand) =>
      (fiveProjectFactorSellerPlan
        (fiveProjectAvailableSupplierFactors D state)
        (fiveProjectAvailableHouseholdFactors D state) demand).bind fun sales =>
          executeFiveProjectFactorPlan state price sales

/-- Execute a named regime's factor-demand list through matched transfers. -/
def fiveProjectFactorExecution (regime : FiveProjectRegime) :=
  fiveProjectFactorExecutionFor (fiveProjectRegimeData regime)

/-- A production profile completes every project in the factor-demand list.
Each project uses the completion factor and yields the physical output already
specified by `fiveProjectOutput`. -/
def fiveProjectCompletionProfile (projects : List LoanReservationBid) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun agent =>
    match projects.find? (fun bid =>
        fiveProjectPhysicalBorrower bid.borrower = agent) with
    | some bid => .operate (.completeProject bid.borrower)
    | none => .idle

/-- Execute the completion operations after the matched factor purchases.
Affordability therefore checks that each listed project owns its input. -/
def fiveProjectProductionExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectFactorExecutionFor D).bind fun state =>
    (fiveProjectExecutedFactorDemandFor D).bind fun projects =>
      advanceIfAffordable fiveProjectPhysicalOperations state
        (fiveProjectCompletionProfile projects)

/-- A complete profile for one output sale at the modeled unit price. -/
def fiveProjectCustomerPurchaseProfile (project : Fin 5) (quantity : ℕ) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  let seller := fiveProjectPhysicalBorrower project
  let buyer : FiveProjectPhysicalAgent := 6
  fun actor =>
    if actor = seller then
      .offer seller buyer quantity fiveProjectOutputGood quantity fiveProjectMoneyGood
    else if actor = buyer then
      .accept buyer seller quantity fiveProjectOutputGood quantity fiveProjectMoneyGood
    else .idle

/-- A physically affordable output sale has a finite choice stage with the
seller's offer, customer's acceptance, and idle alternatives. -/
def fiveProjectCustomerPurchaseChoiceStage
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) (quantity : ℕ)
    (houtput : quantity ≤ state.stock (fiveProjectPhysicalBorrower project)
      fiveProjectOutputGood)
    (hcash : quantity ≤ state.stock 6 fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat := by
  let seller := fiveProjectPhysicalBorrower project
  let buyer : FiveProjectPhysicalAgent := 6
  let profile := fiveProjectCustomerPurchaseProfile project quantity
  let active : Finset FiveProjectPhysicalAgent := {seller, buyer}
  have hdistinct : seller ≠ buyer := by
    intro h
    have hval := congrArg Fin.val h
    simp [seller, fiveProjectPhysicalBorrower] at hval
    omega
  have hnonidle : ∀ agent, agent ∈ active →
      profile agent ≠ EconomyAction.idle := by
    intro agent hagent
    simp only [active, Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with hs | hb
    · subst agent
      simp [profile, seller, fiveProjectCustomerPurchaseProfile]
    · subst agent
      simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile,
        hdistinct.symm]
  have hwellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent) := by
    intro agent
    by_cases hs : agent = seller
    · subst agent
      simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile,
        EconomyAction.WellFormed, hdistinct]
    · by_cases hb : agent = buyer
      · subst agent
        simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile,
          EconomyAction.WellFormed, hs]
      · simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile, hs, hb,
          EconomyAction.WellFormed]
  have hprofileAffordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent) := by
    intro agent good
    by_cases hs : agent = seller
    · subst agent
      by_cases hgood : good = fiveProjectOutputGood
      · simpa [profile, seller, fiveProjectCustomerPurchaseProfile,
          rawActionUse, hgood] using houtput
      · simp [profile, seller, fiveProjectCustomerPurchaseProfile,
          rawActionUse, hgood]
    · by_cases hb : agent = buyer
      · subst agent
        by_cases hgood : good = fiveProjectMoneyGood
        · simpa [profile, seller, buyer, fiveProjectCustomerPurchaseProfile,
            rawActionUse, hs, hgood] using hcash
        · simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile,
            rawActionUse, hs, hgood]
      · simp [profile, seller, buyer, fiveProjectCustomerPurchaseProfile, hs, hb,
          rawActionUse]
  exact finitePhysicalStageOfProfile state profile active
    hnonidle hwellFormed hprofileAffordable

/-- Execute one customer purchase by matching the entrepreneur's output offer
with the customer's money acceptance at the modeled unit price. -/
def executeFiveProjectCustomerPurchase
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) (quantity : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectCustomerPurchaseProfile project quantity)

/-- A successful customer purchase obeys the physical interpreter's exact
bilateral inventory balances. The customer's money outflow and the seller's
money inflow equal the output quantity scheduled for sale. -/
theorem executeFiveProjectCustomerPurchase_balances
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) (quantity : ℕ)
    (hstep : executeFiveProjectCustomerPurchase state project quantity = some next) :
    next.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood + quantity =
        state.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood ∧
      next.stock 6 fiveProjectMoneyGood + quantity = state.stock 6 fiveProjectMoneyGood ∧
      next.stock (fiveProjectPhysicalBorrower project) fiveProjectMoneyGood =
        state.stock (fiveProjectPhysicalBorrower project) fiveProjectMoneyGood + quantity ∧
      next.stock 6 fiveProjectOutputGood = state.stock 6 fiveProjectOutputGood + quantity := by
  unfold executeFiveProjectCustomerPurchase at hstep
  have hdistinct : fiveProjectPhysicalBorrower project ≠ 6 := by
    intro h
    have hval := congrArg Fin.val h
    simp [fiveProjectPhysicalBorrower] at hval
    omega
  have hbalance := advanceIfAffordable_matchedTransfer_balance
    fiveProjectPhysicalOperations state next
    (fiveProjectCustomerPurchaseProfile project quantity)
    (fiveProjectPhysicalBorrower project) 6 quantity fiveProjectOutputGood
    quantity fiveProjectMoneyGood hstep
    (by simp [fiveProjectCustomerPurchaseProfile])
    (by simp [fiveProjectCustomerPurchaseProfile, hdistinct.symm])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [fiveProjectOutputGood, fiveProjectMoneyGood] using
      hbalance.1 fiveProjectOutputGood
  · simpa [fiveProjectOutputGood, fiveProjectMoneyGood] using
      hbalance.2 fiveProjectMoneyGood
  · simpa [fiveProjectOutputGood, fiveProjectMoneyGood] using
      hbalance.1 fiveProjectMoneyGood
  · simpa [fiveProjectOutputGood, fiveProjectMoneyGood] using
      hbalance.2 fiveProjectOutputGood

/-- The actual customer sale is exactly the transition selected from its
finite physical choice stage. -/
theorem fiveProjectCustomerPurchase_is_choiceStage_advance
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) (quantity : ℕ)
    (houtput : quantity ≤ state.stock (fiveProjectPhysicalBorrower project)
      fiveProjectOutputGood)
    (hcash : quantity ≤ state.stock 6 fiveProjectMoneyGood) :
    let stage := fiveProjectCustomerPurchaseChoiceStage
      state project quantity houtput hcash
    executeFiveProjectCustomerPurchase state project quantity =
      some (stage.advance
        (finitePhysicalSelectedProfile stage
          (fiveProjectCustomerPurchaseProfile project quantity) (by
            intro agent
            by_cases hs : agent = fiveProjectPhysicalBorrower project
            · subst agent
              simp [stage, fiveProjectCustomerPurchaseChoiceStage,
                finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                fiveProjectCustomerPurchaseProfile]
            · by_cases hb : agent = 6
              · subst agent
                simp [stage, fiveProjectCustomerPurchaseChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectCustomerPurchaseProfile, hs]
              · simp [stage, fiveProjectCustomerPurchaseChoiceStage,
                  finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
                  fiveProjectCustomerPurchaseProfile, hs, hb]))) := by
  let stage := fiveProjectCustomerPurchaseChoiceStage
    state project quantity houtput hcash
  have hselected : ∀ agent,
      fiveProjectCustomerPurchaseProfile project quantity agent ∈
        stage.choices.menu agent := by
    intro agent
    by_cases hs : agent = fiveProjectPhysicalBorrower project
    · subst agent
      simp [stage, fiveProjectCustomerPurchaseChoiceStage,
        finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
        fiveProjectCustomerPurchaseProfile]
    · by_cases hb : agent = 6
      · subst agent
        simp [stage, fiveProjectCustomerPurchaseChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectCustomerPurchaseProfile, hs]
      · simp [stage, fiveProjectCustomerPurchaseChoiceStage,
          finitePhysicalStageOfProfile, FiniteChoiceStage.ofProfile,
          fiveProjectCustomerPurchaseProfile, hs, hb]
  let selected := finitePhysicalSelectedProfile stage
    (fiveProjectCustomerPurchaseProfile project quantity) hselected
  have htransition :=
    FinitePhysicalChoiceStage.advanceIfAffordable_eq_some_advance stage selected
  simpa [executeFiveProjectCustomerPurchase, stage, selected,
    fiveProjectCustomerPurchaseChoiceStage, finitePhysicalStageOfProfile,
    finitePhysicalSelectedProfile, fiveProjectCustomerPurchaseProfile] using htransition

/-- Execute the customer's ordered purchase schedule through successive
matched sales. Each transaction consumes output and money from the current
physical inventory. -/
def executeFiveProjectCustomerPlan
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List (Fin 5 × ℕ) →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | (project, quantity) :: rest =>
      (executeFiveProjectCustomerPurchase state project quantity).bind fun next =>
        executeFiveProjectCustomerPlan next rest

/-- Generate each customer purchase from the completed project's current
output and the customer's remaining money, then continue from the resulting
inventory. The order is the actual factor-market funded order. -/
def executeFiveProjectCustomerPlanFromState
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | bid :: rest =>
      let project := bid.borrower
      let seller := fiveProjectPhysicalBorrower project
      let quantity := min (state.stock seller fiveProjectOutputGood)
        (state.stock 6 fiveProjectMoneyGood)
      (executeFiveProjectCustomerPurchase state project quantity).bind fun next =>
        executeFiveProjectCustomerPlanFromState next rest

/-- Run the market-derived production and customer purchase plan after actual
factor trades. No sale quantity is credited unless the matched physical
transfer succeeds. -/
def fiveProjectCustomerSaleExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectProductionExecutionFor D).bind fun state =>
    (fiveProjectExecutedFactorDemandFor D).bind fun projects =>
      executeFiveProjectCustomerPlanFromState state projects

/-- Loan terms are formed from the same marginal repayment quote and funded
prefix used by the regime's physical advances. -/
def fiveProjectLoanTermsFor (D : FiveProjectRegimeData) :
    Option (List FundedLoanTerms) :=
  (fiveProjectLoanOutcomeAfterSourcesFor D).bind fun outcome =>
    outcome.quotedRepayment.map fun promisedRepayment =>
      outcome.funded.map fun bid =>
        { borrower := bid.borrower
          principal := fiveProjectLoanMarket.principal
          principal_positive := fiveProjectLoanMarket.principal_positive
          promisedRepayment := promisedRepayment }

/-- Contracts attached to projects that pass the actual factor-market
eligibility rule. The physical completion profile uses this same project
list, so these are the funded terms associated with completed projects. -/
def fiveProjectCompletedLoanTermsFor (D : FiveProjectRegimeData) :
    Option (List FundedLoanTerms) :=
  (fiveProjectLoanTermsFor D).bind fun terms =>
    (fiveProjectExecutedFactorDemandFor D).map fun completed =>
      terms.filter fun contract =>
        completed.any fun bid => bid.borrower == contract.borrower

/-- Execute repayment of each completed project's promised amount as a
separate matched transfer after customer sales. A quoted term and a funded
advance do not themselves count as repayment. -/
def executeFiveProjectRepaymentPlan
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    List FundedLoanTerms →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
  | [] => some state
  | contract :: rest =>
      (executeFiveProjectLoanRepayment state contract).bind fun next =>
          executeFiveProjectRepaymentPlan next rest

/-- Attempt deposit redemption after the loan settlements. The claim and the
bank's actual cash remain preconditions of the matched physical transfer. -/
def executeFiveProjectHouseholdDepositRedemption (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  if D.householdMoneyTransferred = fiveProjectHouseholdDepositTerms.principal then
    executeFiveProjectDepositRedemption fiveProjectHouseholdDepositTerms state
  else some state

/-- Run completed-project repayments after production and customer sales. -/
def fiveProjectLoanRepaymentExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectCustomerSaleExecutionFor D).bind fun state =>
    (fiveProjectCompletedLoanTermsFor D).bind fun contracts =>
      executeFiveProjectRepaymentPlan state contracts

/-- After loan repayments, attempt redemption only for a deposit principal
specified by the household-transfer regime. -/
def fiveProjectLoanSettlementExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :=
  (fiveProjectLoanRepaymentExecutionFor D).bind
    (executeFiveProjectHouseholdDepositRedemption D)

/-- Read bank cash after project repayments and before a household claim is
redeemed. -/
def fiveProjectPreDepositRedemptionMoneyBalance? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) : Option ℕ :=
  (fiveProjectLoanRepaymentExecutionFor D).map fun state =>
    state.stock agent fiveProjectMoneyGood

/-- Read a money balance after completed-project repayments. -/
def fiveProjectSettledMoneyBalance? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) : Option ℕ :=
  (fiveProjectLoanSettlementExecutionFor D).map fun state =>
    state.stock agent fiveProjectMoneyGood

/-- Read a physical good after project repayment and any authorized matched
deposit redemption. -/
def fiveProjectSettledStock? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) (good : FiveProjectPhysicalGood) :
    Option ℕ :=
  (fiveProjectLoanSettlementExecutionFor D).map fun state => state.stock agent good

/-- For each named funding source, the funded borrowers receive terms with
unit principal and the quote produced by its actual loan-auction capacity. -/
theorem fiveProject_named_funded_loan_terms :
    (fiveProjectLoanTermsFor (fiveProjectRegimeData .baseline)).map
        (List.map fun terms =>
          (terms.borrower.val, terms.principal, terms.promisedRepayment)) =
      some [(0, 1, 6), (1, 1, 6)] ∧
    (fiveProjectLoanTermsFor (fiveProjectRegimeData .fiduciaryExpansion)).map
        (List.map fun terms =>
          (terms.borrower.val, terms.principal, terms.promisedRepayment)) =
      some [(0, 1, 4), (1, 1, 4), (2, 1, 4), (3, 1, 4)] ∧
    (fiveProjectLoanTermsFor (fiveProjectRegimeData .householdTransfer)).map
        (List.map fun terms =>
          (terms.borrower.val, terms.principal, terms.promisedRepayment)) =
      some [(0, 1, 4), (1, 1, 4), (2, 1, 4), (3, 1, 4)] := by
  decide

/-- Every completed project in the three modeled regimes physically settles
the auction-quoted promised repayment after selling its output. The result
checks successful repayment for each completed project; it makes no default
claim about projects excluded from factor purchases. -/
theorem fiveProject_named_completed_project_repayments_execute :
    (fiveProjectLoanSettlementExecutionFor
      (fiveProjectRegimeData .baseline)).isSome = true ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .baseline)
      fiveProjectBank = some 12 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .baseline)
      (fiveProjectPhysicalBorrower 0) = some 5 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .baseline)
      (fiveProjectPhysicalBorrower 1) = some 4 ∧
    (fiveProjectLoanSettlementExecutionFor
      (fiveProjectRegimeData .fiduciaryExpansion)).isSome = true ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      fiveProjectBank = some 8 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 0) = some 6 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 1) = some 5 ∧
    (fiveProjectLoanSettlementExecutionFor
      (fiveProjectRegimeData .householdTransfer)).isSome = true ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectBank = some 13 ∧
    fiveProjectPreDepositRedemptionMoneyBalance?
      (fiveProjectRegimeData .householdTransfer) fiveProjectBank = some 16 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectHousehold = some 5 ∧
    fiveProjectSettledStock? (fiveProjectRegimeData .householdTransfer)
      fiveProjectHousehold fiveProjectDepositClaimGood = some 0 ∧
    fiveProjectSettledStock? (fiveProjectRegimeData .householdTransfer)
      fiveProjectBank fiveProjectDepositClaimGood = some 1 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 0) = some 7 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 1) = some 6 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 2) = some 3 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 3) = some 2 := by
  decide

/-- Customer money spent, as read from the final physical inventory after
the executed sales. -/
def fiveProjectExecutedCustomerRevenue? (D : FiveProjectRegimeData) : Option ℕ :=
  (fiveProjectCustomerSaleExecutionFor D).map fun state =>
    fiveProjectCustomerMoneyEndowment - state.stock 6 fiveProjectMoneyGood

/-- Physical output remaining with the customer after the matched sales. -/
def fiveProjectExecutedCustomerOutput? (D : FiveProjectRegimeData) : Option ℕ :=
  (fiveProjectCustomerSaleExecutionFor D).map fun state =>
    state.stock 6 fiveProjectOutputGood

/-- Read a named agent's final physical money balance after factor and output
trades. -/
def fiveProjectExecutedMoneyBalance? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) : Option ℕ :=
  (fiveProjectCustomerSaleExecutionFor D).map fun state =>
    state.stock agent fiveProjectMoneyGood

/-- Read an inventory coordinate from a successful named-regime execution. -/
def fiveProjectExecutedStock? (regime : FiveProjectRegime)
    (agent : FiveProjectPhysicalAgent) (good : FiveProjectPhysicalGood) : Option ℕ :=
  (fiveProjectFactorExecution regime).map fun state => state.stock agent good

/-- Read a stock coordinate from a successful execution under arbitrary
explicit regime data, including parameterized boundary cases. -/
def fiveProjectExecutedStockFor? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) (good : FiveProjectPhysicalGood) : Option ℕ :=
  (fiveProjectFactorExecutionFor D).map fun state => state.stock agent good

/-- Named factor markets use actual funded advances, current cash after early
input purchases, and currently offered stock. In the fiduciary expansion the
marginal borrowers each have one cash unit at factor clearing, so the
current-cash auction excludes them at price two. -/
theorem fiveProject_named_executed_factor_markets :
    fiveProjectExecutedFactorPriceFor (fiveProjectRegimeData .baseline) = some 1 ∧
    (fiveProjectExecutedFactorDemandFor (fiveProjectRegimeData .baseline)).map
      (List.map LoanReservationBid.borrower) = some [0, 1] ∧
    fiveProjectExecutedFactorPriceFor
      (fiveProjectRegimeData .fiduciaryExpansion) = some 2 ∧
    (fiveProjectExecutedFactorDemandFor
      (fiveProjectRegimeData .fiduciaryExpansion)).map
      (List.map LoanReservationBid.borrower) = some [0, 1] ∧
    fiveProjectExecutedFactorPriceFor
      (fiveProjectRegimeData .householdTransfer) = some 1 ∧
    (fiveProjectExecutedFactorDemandFor
      (fiveProjectRegimeData .householdTransfer)).map
      (List.map LoanReservationBid.borrower) = some [0, 1, 2, 3] := by
  decide

/-- The baseline factor demand is physically transferred from the supplier to
the two funded borrowers at the reserve price. -/
theorem fiveProject_baseline_factor_trades_execute :
    (fiveProjectFactorExecution .baseline).isSome = true ∧
    fiveProjectExecutedStock? .baseline fiveProjectFactorSupplier
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStock? .baseline (fiveProjectPhysicalBorrower 0)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .baseline (fiveProjectPhysicalBorrower 1)
      fiveProjectCompletionGood = some 1 := by
  decide

/-- Under fiduciary expansion, factor clearing reads the borrowers' cash after
early-input purchases. At price two projects zero and one can pay from current
cash and acquire the supplier's factors; projects two and three cannot pay
that price. Each matched transfer is still checked by the physical
interpreter. -/
theorem fiveProject_fiduciary_factor_trades_execute :
    (fiveProjectFactorExecution .fiduciaryExpansion).isSome = true ∧
    fiveProjectExecutedStock? .fiduciaryExpansion fiveProjectFactorSupplier
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStock? .fiduciaryExpansion (fiveProjectPhysicalBorrower 0)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .fiduciaryExpansion (fiveProjectPhysicalBorrower 1)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .fiduciaryExpansion (fiveProjectPhysicalBorrower 2)
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStock? .fiduciaryExpansion (fiveProjectPhysicalBorrower 3)
      fiveProjectCompletionGood = some 0 := by
  decide

/-- In the household-transfer regime, the supplier's two factors and the two
household factors are transferred to the four eligible borrowers at price
one. The result is physical acquisition, not proof of purposeful saving. -/
theorem fiveProject_household_factor_trades_execute :
    (fiveProjectFactorExecution .householdTransfer).isSome = true ∧
    fiveProjectExecutedStock? .householdTransfer fiveProjectFactorSupplier
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStock? .householdTransfer fiveProjectHousehold
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStock? .householdTransfer (fiveProjectPhysicalBorrower 0)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .householdTransfer (fiveProjectPhysicalBorrower 1)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .householdTransfer (fiveProjectPhysicalBorrower 2)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStock? .householdTransfer (fiveProjectPhysicalBorrower 3)
      fiveProjectCompletionGood = some 1 := by
  decide

/-- The derived baseline and fiduciary projects physically complete after
acquiring factors, then sell their output through matched customer trades.
The customer spends seventeen money units in each executed market run. -/
theorem fiveProject_baseline_and_credit_output_sales_execute :
    (fiveProjectCustomerSaleExecutionFor (fiveProjectRegimeData .baseline)).isSome = true ∧
    fiveProjectExecutedCustomerRevenue? (fiveProjectRegimeData .baseline) = some 17 ∧
    fiveProjectExecutedCustomerOutput? (fiveProjectRegimeData .baseline) = some 17 ∧
    (fiveProjectCustomerSaleExecutionFor
      (fiveProjectRegimeData .fiduciaryExpansion)).isSome = true ∧
    fiveProjectExecutedCustomerRevenue?
      (fiveProjectRegimeData .fiduciaryExpansion) = some 17 ∧
    fiveProjectExecutedCustomerOutput?
      (fiveProjectRegimeData .fiduciaryExpansion) = some 17 := by
  decide

/-- With the two household factors physically sold to the remaining eligible
borrowers, all four complete and sell thirty output units to the customer. -/
theorem fiveProject_household_factor_output_sales_execute :
    (fiveProjectCustomerSaleExecutionFor (fiveProjectRegimeData .householdTransfer)).isSome =
      true ∧
    fiveProjectExecutedCustomerRevenue? (fiveProjectRegimeData .householdTransfer) = some 30 ∧
    fiveProjectExecutedCustomerOutput? (fiveProjectRegimeData .householdTransfer) = some 30 := by
  decide

/-- When the fiduciary regime is supplied with the four completion factors in
its explicit real-input boundary case, both the projected market calculation
and the executed current-cash market return to the reserve price. All four
funded projects acquire inputs, complete, and sell their thirty physical
output units. This is an executed physical boundary, not a loan-origination
or household-purposefulness result. -/
theorem fiveProject_sufficient_real_inputs_output_sales_execute :
    (fiveProjectFactorPriceFor fiveProject_fiduciaryWithSufficientFactors) =
      some 1 ∧
    (fiveProjectFactorDemandFor fiveProject_fiduciaryWithSufficientFactors).map
        (List.map LoanReservationBid.borrower) = some [0, 1, 2, 3] ∧
    fiveProjectExecutedFactorPriceFor fiveProject_fiduciaryWithSufficientFactors =
      some 1 ∧
    (fiveProjectExecutedFactorDemandFor
      fiveProject_fiduciaryWithSufficientFactors).map
        (List.map LoanReservationBid.borrower) = some [0, 1, 2, 3] ∧
    (fiveProjectFactorExecutionFor fiveProject_fiduciaryWithSufficientFactors).isSome =
      true ∧
    fiveProjectExecutedStockFor? fiveProject_fiduciaryWithSufficientFactors
      fiveProjectFactorSupplier
      fiveProjectCompletionGood = some 0 ∧
    fiveProjectExecutedStockFor? fiveProject_fiduciaryWithSufficientFactors
      (fiveProjectPhysicalBorrower 0)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStockFor? fiveProject_fiduciaryWithSufficientFactors
      (fiveProjectPhysicalBorrower 1)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStockFor? fiveProject_fiduciaryWithSufficientFactors
      (fiveProjectPhysicalBorrower 2)
      fiveProjectCompletionGood = some 1 ∧
    fiveProjectExecutedStockFor? fiveProject_fiduciaryWithSufficientFactors
      (fiveProjectPhysicalBorrower 3)
      fiveProjectCompletionGood = some 1 ∧
    (fiveProjectCustomerSaleExecutionFor
      fiveProject_fiduciaryWithSufficientFactors).isSome = true ∧
    fiveProjectExecutedCustomerRevenue?
      fiveProject_fiduciaryWithSufficientFactors = some 30 ∧
    fiveProjectExecutedCustomerOutput?
      fiveProject_fiduciaryWithSufficientFactors = some 30 := by
  decide

/-- In each named regime, the executed customer's money loss equals the
market's planned revenue because every scheduled unit passed the physical
output and cash checks and was transferred at the modeled unit price. -/
theorem fiveProject_executed_sales_match_revenue_plans :
    fiveProjectCustomerRevenuePlan .baseline = some 17 ∧
    fiveProjectExecutedCustomerRevenue? (fiveProjectRegimeData .baseline) = some 17 ∧
    fiveProjectCustomerRevenuePlan .fiduciaryExpansion = some 17 ∧
    fiveProjectExecutedCustomerRevenue?
      (fiveProjectRegimeData .fiduciaryExpansion) = some 17 ∧
    fiveProjectCustomerRevenuePlan .householdTransfer = some 30 ∧
    fiveProjectExecutedCustomerRevenue?
      (fiveProjectRegimeData .householdTransfer) = some 30 := by
  decide

/-- Supplier receipts, household proceeds, and customer expenditures are the
money balances generated by the matched transfer sequence in each regime. -/
theorem fiveProject_three_regime_executed_money_balances :
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .baseline)
      fiveProjectFactorSupplier = some 4 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .baseline) 6 = some 23 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      fiveProjectFactorSupplier = some 8 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion) 6 = some 23 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectFactorSupplier = some 6 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectHousehold = some 2 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer) 6 = some 10 := by
  decide

end Praxeology

end
