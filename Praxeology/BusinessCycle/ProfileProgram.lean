/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.FactorExecution
public import Praxeology.FiniteEconomy.ProfileSchedule
public import Praxeology.FiniteEconomy.ProgramActionFrame

/-!
# Recursive physical program for the five-project scenario

The fuel-bounded instruction generator uses a finite cursor and the current
physical state to stage note issuance, the household cash-transfer leg, loan
clearing, advances, household factor use, factor clearing and purchases,
completion, customer purchases, and repayment attempts. Loan capacity is
cleared from the bank's actual money when that round is reached; factor
clearing uses actually matched advances and currently offered factor stock.
Each clearing result is retained after assignment, while later rounds are
computed from the state reached on that branch. A failed transfer consumes its
cursor position and is not retried. The generic profile-schedule compiler
remains available as the fixed-schedule specialization. Every physical
transition uses the existing inventory interpreter.

The household's stated consumption alternative is included only when it is
feasible in the current state. Early-input production and its conversion into
capital remain unresolved. The program does not derive purposeful household
saving, purposeful investment, or foreclosure from its physical transitions.
Menu availability does not establish choice; preferences remain explicit
inputs to the ActionFrame adapter. Projected eligibility, physical affordability,
purposeful choice, and contextual regret are separate claims.
-/

@[expose] public section

namespace Praxeology

/-- Generic bilateral offer and acceptance profile used by the scenario's
existing matched-transfer interpreter. -/
def fiveProjectScheduledTransferProfile
    (seller buyer : FiveProjectPhysicalAgent) (quantity : ℕ)
    (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = seller then
      .offer seller buyer quantity good payment moneyGood
    else if actor = buyer then
      .accept buyer seller quantity good payment moneyGood
    else .idle

theorem fiveProjectScheduledTransferProfile_wellFormed
    (seller buyer : FiveProjectPhysicalAgent) (hne : seller ≠ buyer)
    (quantity : ℕ) (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) :
    ∀ actor, EconomyAction.WellFormed actor
      (fiveProjectScheduledTransferProfile seller buyer quantity good payment moneyGood actor) := by
  intro actor
  by_cases hs : actor = seller
  · subst actor
    simp [fiveProjectScheduledTransferProfile, EconomyAction.WellFormed, hne]
  · by_cases hb : actor = buyer
    · subst actor
      simp [fiveProjectScheduledTransferProfile, EconomyAction.WellFormed, hs]
    · simp [fiveProjectScheduledTransferProfile, hs, hb,
        EconomyAction.WellFormed]

/-- Package one scheduled bilateral transfer as a well-formed profile step. -/
def fiveProjectTransferInstruction
    (seller buyer : FiveProjectPhysicalAgent) (hne : seller ≠ buyer)
    (quantity : ℕ) (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  ⟨fiveProjectScheduledTransferProfile seller buyer quantity good payment moneyGood,
    fiveProjectScheduledTransferProfile_wellFormed seller buyer hne
      quantity good payment moneyGood,
    fun _ => ∅,
    by intro actor action h; simp at h⟩

/-- Every entrepreneur is distinct from the final customer. -/
theorem fiveProjectBorrower_ne_customer (project : Fin 5) :
    fiveProjectPhysicalBorrower project ≠ (6 : FiveProjectPhysicalAgent) := by
  intro h
  have hval := congrArg Fin.val h
  simp [fiveProjectPhysicalBorrower] at hval
  omega

/-- Profile instruction for the regime-specified bank note issue. -/
def fiveProjectIssueNotesInstruction (D : FiveProjectRegimeData) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile actor :=
    if actor = fiveProjectBank then
      .operate (.issueFiduciaryNotes D.fiduciaryNotesIssued)
    else .idle
  wellFormed := by
    intro actor
    by_cases hbank : actor = fiveProjectBank <;>
      simp [hbank, EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by
    intro actor action h
    simp at h

/-- Profile instruction for the household-to-bank cash-transfer leg. It does
not enact or evidence a deposit liability. -/
def fiveProjectHouseholdCashTransferInstruction (D : FiveProjectRegimeData) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction fiveProjectHousehold fiveProjectBank
    (by decide) D.householdMoneyTransferred fiveProjectMoneyGood 0 fiveProjectMoneyGood

/-- Profile instruction for one funded principal advance. -/
def fiveProjectAdvanceInstruction (bid : LoanReservationBid) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction fiveProjectBank
    (fiveProjectPhysicalBorrower bid.borrower)
    (by
      intro h
      have hval := congrArg Fin.val h
      simp [fiveProjectBank, fiveProjectPhysicalBorrower] at hval
      omega)
    fiveProjectLoanMarket.principal fiveProjectMoneyGood 0 fiveProjectMoneyGood

/-- Profile instruction for the household's stated factor consumption. -/
def fiveProjectHouseholdConsumptionInstruction (D : FiveProjectRegimeData) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile actor :=
    if actor = fiveProjectHousehold then
      if D.householdFactorsConsumed = 0 then .idle
      else .operate (.consumeHouseholdFactors D.householdFactorsConsumed)
    else .idle
  wellFormed := by
    intro actor
    by_cases hhousehold : actor = fiveProjectHousehold
    · subst actor
      by_cases hconsume : D.householdFactorsConsumed = 0 <;>
        simp [hconsume, EconomyAction.WellFormed]
    · simp [hhousehold, EconomyAction.WellFormed]
  alternatives := fun actor =>
    if hhousehold : actor = fiveProjectHousehold then
      if 0 < D.householdFactorEndowment then
        {.operate (.consumeHouseholdFactors D.householdFactorEndowment)}
      else ∅
    else ∅
  alternatives_wellFormed := by
    intro actor action h
    by_cases hhousehold : actor = fiveProjectHousehold
    · subst actor
      by_cases hpositive : 0 < D.householdFactorEndowment
      · have haction : action =
            .operate (.consumeHouseholdFactors D.householdFactorEndowment) := by
            simpa [hpositive] using h
        rw [haction]
        simp [EconomyAction.WellFormed]
      · simp [hpositive] at h
    · simp [hhousehold] at h

/-- For regime data with a positive household factor endowment, consumption
remains an explicit feasible alternative whenever the stated stock is
present. The alternative uses the existing consumption operation; it does
not assert that idling or the household cash transfer is purposeful. -/
theorem fiveProject_household_consumption_is_affordable_alternative
    (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (hpositive : 0 < D.householdFactorEndowment)
    (hstock : D.householdFactorEndowment ≤
      state.stock fiveProjectHousehold fiveProjectCompletionGood) :
    EconomyAction.operate (.consumeHouseholdFactors D.householdFactorEndowment) ∈
      (fiveProjectHouseholdConsumptionInstruction D).affordableAlternatives
        fiveProjectPhysicalOperations state fiveProjectHousehold := by
  let action : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .operate (.consumeHouseholdFactors D.householdFactorEndowment)
  have hlisted : action ∈
      (fiveProjectHouseholdConsumptionInstruction D).alternatives fiveProjectHousehold := by
    simp [fiveProjectHouseholdConsumptionInstruction, action, hpositive]
  have haffordable : actionAffordable fiveProjectPhysicalOperations state
      fiveProjectHousehold action := by
    intro good
    by_cases hgood : good = fiveProjectCompletionGood
    · subst good
      simpa [action, rawActionUse, fiveProjectPhysicalOperations] using hstock
    · simp [action, rawActionUse, fiveProjectPhysicalOperations, hgood]
  exact Finset.mem_filter.mpr ⟨hlisted, haffordable⟩

/-- The feasible alternative is retained in the household's stage menu. -/
theorem fiveProject_household_consumption_is_available
    (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (hpositive : 0 < D.householdFactorEndowment)
    (hstock : D.householdFactorEndowment ≤
      state.stock fiveProjectHousehold fiveProjectCompletionGood) :
    EconomyAction.operate (.consumeHouseholdFactors D.householdFactorEndowment) ∈
      ((fiveProjectHouseholdConsumptionInstruction D).stage
        fiveProjectPhysicalOperations state).choices.menu fiveProjectHousehold := by
  have halternative := fiveProject_household_consumption_is_affordable_alternative
    D state hpositive hstock
  change EconomyAction.operate
      (.consumeHouseholdFactors D.householdFactorEndowment) ∈
    (fiveProjectHouseholdConsumptionInstruction D).stageMenu
      fiveProjectPhysicalOperations state fiveProjectHousehold
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem halternative)

/-- The household can enact the available consumption alternative by itself,
with every other agent idle, at its consumption decision. -/
theorem fiveProject_household_consumption_unilateral_branch
    (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (hpositive : 0 < D.householdFactorEndowment)
    (hstock : D.householdFactorEndowment ≤
      state.stock fiveProjectHousehold fiveProjectCompletionGood) :
    ∃ profile ∈
      ((fiveProjectHouseholdConsumptionInstruction D).stage
        fiveProjectPhysicalOperations state).choices.profiles,
      profile.1 fiveProjectHousehold =
        .operate (.consumeHouseholdFactors D.householdFactorEndowment) ∧
      ∀ other, other ≠ fiveProjectHousehold →
        profile.1 other = EconomyAction.idle := by
  exact PhysicalProfileInstruction.stage_has_unilateral_alternative_branch
    fiveProjectPhysicalOperations state
    (fiveProjectHouseholdConsumptionInstruction D) fiveProjectHousehold _
    (fiveProject_household_consumption_is_affordable_alternative D state
      hpositive hstock)

/-- After the household's cash has entered the named transfer schedule and the
loan advances have executed, the household still has its two stated factors.
The compiled consumption stage therefore contains a unilateral consume
branch. This witness establishes menu availability and physical feasibility;
it does not establish a purposeful choice. The generated program reaches its
factor-clearing round later and computes that round from the resulting branch
state. -/
theorem fiveProject_household_transfer_schedule_retains_consumption_branch :
    ∃ state,
      fiveProjectFundedStateFor (fiveProjectRegimeData .householdTransfer) =
        some state ∧
      ∃ profile ∈
        ((fiveProjectHouseholdConsumptionInstruction
          (fiveProjectRegimeData .householdTransfer)).stage
            fiveProjectPhysicalOperations state).choices.profiles,
        profile.1 fiveProjectHousehold =
            .operate (.consumeHouseholdFactors 2) ∧
          ∀ other, other ≠ fiveProjectHousehold →
            profile.1 other = EconomyAction.idle := by
  let D := fiveProjectRegimeData .householdTransfer
  have hfunded : (fiveProjectFundedStateFor D).isSome = true := by
    decide
  cases hstate : fiveProjectFundedStateFor D with
  | none => simp [hstate] at hfunded
  | some state =>
      refine ⟨state, ?_, ?_⟩
      · simp
      · have hstockMap : (fiveProjectFundedStateFor D).map
            (fun current => current.stock fiveProjectHousehold
              fiveProjectCompletionGood) = some 2 := by
          decide
        rw [hstate] at hstockMap
        have hstock : D.householdFactorEndowment ≤
            state.stock fiveProjectHousehold fiveProjectCompletionGood := by
          have heq : state.stock fiveProjectHousehold
              fiveProjectCompletionGood = 2 := by
            simpa using hstockMap
          rw [heq]
          decide
        exact fiveProject_household_consumption_unilateral_branch D state
          (by decide) hstock

/-- Profile instruction for one completion-factor purchase. -/
def fiveProjectFactorPurchaseInstruction (project : Fin 5)
    (seller : FiveProjectPhysicalAgent) (price : ℕ)
    (hne : seller ≠ fiveProjectPhysicalBorrower project) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction seller (fiveProjectPhysicalBorrower project) hne
    1 fiveProjectCompletionGood price fiveProjectMoneyGood

/-- Profile instruction for the completion operations in the market's
factor-demand list. -/
def fiveProjectCompletionInstruction (projects : List LoanReservationBid) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile := fiveProjectCompletionProfile projects
  wellFormed := by
    intro actor
    unfold fiveProjectCompletionProfile
    split <;> simp [EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by
    intro actor action h
    simp at h

/-- Profile instruction for one market-assigned customer purchase. -/
def fiveProjectCustomerPurchaseInstruction (project : Fin 5) (quantity : ℕ) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction (fiveProjectPhysicalBorrower project) 6
    (fiveProjectBorrower_ne_customer project) quantity fiveProjectOutputGood
    quantity fiveProjectMoneyGood

/-- Profile instruction for one completed project's promised repayment. -/
def fiveProjectRepaymentInstruction (contract : FundedLoanTerms) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction (fiveProjectPhysicalBorrower contract.borrower)
    fiveProjectBank
    (by
      intro h
      have hval := congrArg Fin.val h
      simp [fiveProjectBank, fiveProjectPhysicalBorrower] at hval
      omega)
    contract.promisedRepayment fiveProjectMoneyGood
    0 fiveProjectMoneyGood

/-- Construct one factor-purchase instruction for each project in the market
list, preserving the supplier-first rule already used by physical execution. -/
def fiveProjectFactorPurchaseInstructions (supplierStock price : ℕ) :
    List LoanReservationBid →
      List (PhysicalProfileInstruction FiveProjectPhysicalAgent
        FiveProjectPhysicalGood FiveProjectPhysicalOperation)
  | [] => []
  | bid :: rest =>
      let seller := if 0 < supplierStock then fiveProjectFactorSupplier
        else fiveProjectHousehold
      fiveProjectFactorPurchaseInstruction bid.borrower seller price (by
        intro h
        have hval := congrArg Fin.val h
        by_cases hs : 0 < supplierStock
        · simp [seller, hs, fiveProjectPhysicalBorrower,
            fiveProjectFactorSupplier] at hval
        · simp [seller, hs, fiveProjectPhysicalBorrower,
            fiveProjectHousehold] at hval
          omega) ::
        fiveProjectFactorPurchaseInstructions (supplierStock - 1) price rest

/-- A passive instruction occupies an absent or already exhausted cursor
slot. The slot still advances, preventing an automatic retry. -/
def fiveProjectPassiveInstruction :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile := fun _ => .idle
  wellFormed := by intro actor; simp [EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by intro actor action h; simp at h

/-- The finite cursor stores market terms when each clearing round is
reached and records transfers only when the physical interpreter's offer and
acceptance match. -/
inductive FiveProjectPhysicalPhase where
  | noteIssuance
  | householdCashTransfer
  | loanClearing
  | loanAcceptance (project : Fin 5)
  | householdConsumption
  | factorClearing
  | factorPurchase (slot : Fin 5)
  | completion
  | customerSale (project : Fin 5)
  | loanSettlement (project : Fin 5)
  deriving DecidableEq, Repr

/-- The current finite settlement schedule. Project-specific phases carry
their project index, so inserting an earlier phase does not silently change
the identity of a later transaction. -/
def fiveProjectPhysicalPhases : List FiveProjectPhysicalPhase :=
  [.noteIssuance, .householdCashTransfer, .loanClearing,
   .loanAcceptance 0, .loanAcceptance 1, .loanAcceptance 2,
   .loanAcceptance 3, .loanAcceptance 4, .householdConsumption,
   .factorClearing, .factorPurchase 0, .factorPurchase 1,
   .factorPurchase 2, .factorPurchase 3, .factorPurchase 4,
   .completion, .customerSale 0, .customerSale 1, .customerSale 2,
   .customerSale 3, .customerSale 4, .loanSettlement 0,
   .loanSettlement 1, .loanSettlement 2, .loanSettlement 3,
   .loanSettlement 4]

def fiveProjectPhysicalFuel : ℕ := fiveProjectPhysicalPhases.length

abbrev FiveProjectPhysicalProfile :=
  ActionProfile (Agent := FiveProjectPhysicalAgent)
    (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation)

/-- Evidence attached to a physical transfer event. The event retains the
profile that enacted it and proofs that the seller's offer and buyer's
acceptance agree in every transaction field. -/
structure FiveProjectMatchedTransfer where
  profile : FiveProjectPhysicalProfile
  seller : FiveProjectPhysicalAgent
  buyer : FiveProjectPhysicalAgent
  quantity : ℕ
  good : FiveProjectPhysicalGood
  payment : ℕ
  moneyGood : FiveProjectPhysicalGood
  offerEnacted : profile seller =
    .offer seller buyer quantity good payment moneyGood
  acceptanceEnacted : profile buyer =
    .accept buyer seller quantity good payment moneyGood

/-- A transition emits only enacted operations and exactly matched transfers.
The physical inventory transition remains the interpreter's responsibility;
these records identify its resulting contractual and market events. -/
inductive FiveProjectPhysicalEvent where
  | notesIssued (profile : FiveProjectPhysicalProfile) (quantity : ℕ)
      (enacted : profile fiveProjectBank =
        .operate (.issueFiduciaryNotes quantity))
  | householdCashTransferred (quantity : ℕ)
      (transfer : FiveProjectMatchedTransfer)
  | advanceMatched (bid : LoanReservationBid)
      (transfer : FiveProjectMatchedTransfer)
  | factorPurchaseMatched (bid : LoanReservationBid)
      (seller : FiveProjectPhysicalAgent)
      (transfer : FiveProjectMatchedTransfer)
  | projectCompleted (profile : FiveProjectPhysicalProfile)
      (bid : LoanReservationBid)
      (enacted : profile (fiveProjectPhysicalBorrower bid.borrower) =
        .operate (.completeProject bid.borrower))
  | customerOutputSold (project : Fin 5) (quantity : ℕ)
      (transfer : FiveProjectMatchedTransfer)
  | loanRepaid (bid : LoanReservationBid)
      (transfer : FiveProjectMatchedTransfer)

structure FiveProjectPhysicalCursor where
  remainingPhases : List FiveProjectPhysicalPhase := fiveProjectPhysicalPhases
  events : List FiveProjectPhysicalEvent := []
  loanQuote : Option ℕ := none
  plannedAdvances : List LoanReservationBid := []
  factorClearing : Option (ℕ × List LoanReservationBid) := none
  householdOfferLimit : ℕ := 0

/-- Transaction summaries are views over the event trace, so the stored
cursor cannot disagree with its recorded physical events. -/
def FiveProjectPhysicalCursor.actualNotesIssued
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  (cursor.events.filterMap fun
    | .notesIssued _ quantity _ => some quantity
    | _ => none).sum

def FiveProjectPhysicalCursor.actualHouseholdMoneyTransferred
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  (cursor.events.filterMap fun
    | .householdCashTransferred quantity _ => some quantity
    | _ => none).sum

def FiveProjectPhysicalCursor.actualAdvances
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .advanceMatched bid _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.actualFactorPurchases
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .factorPurchaseMatched bid _ _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.completedProjects
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .projectCompleted _ bid _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.actualCustomerSales
    (cursor : FiveProjectPhysicalCursor) : List (Fin 5 × ℕ) :=
  cursor.events.filterMap fun
    | .customerOutputSold project quantity _ => some (project, quantity)
    | _ => none

def FiveProjectPhysicalCursor.actualRepayments
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .loanRepaid bid _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.householdOfferRemaining
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  cursor.householdOfferLimit -
    (cursor.events.filter fun
      | .factorPurchaseMatched _ seller _ => decide (seller = fiveProjectHousehold)
      | _ => false).length

def fiveProjectInitialCursor (D : FiveProjectRegimeData) : FiveProjectPhysicalCursor :=
  { householdOfferLimit := D.householdFactorsOffered }

/-- Exact bilateral matching test shared by cursor event recording. -/
def fiveProjectTransferMatched
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (seller buyer : FiveProjectPhysicalAgent) (quantity : ℕ)
    (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) : Bool :=
  decide (profile seller = .offer seller buyer quantity good payment moneyGood ∧
    profile buyer = .accept buyer seller quantity good payment moneyGood)

def fiveProjectMatchedTransfer?
    (profile : FiveProjectPhysicalProfile)
    (seller buyer : FiveProjectPhysicalAgent) (quantity : ℕ)
    (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) : Option FiveProjectMatchedTransfer :=
  if h : profile seller = .offer seller buyer quantity good payment moneyGood ∧
      profile buyer = .accept buyer seller quantity good payment moneyGood then
    some ⟨profile, seller, buyer, quantity, good, payment, moneyGood, h.1, h.2⟩
  else none

/-- Supplier stock plus only the household stock it explicitly offers,
capped by the quantity remaining and the household's current holdings. -/
def fiveProjectAvailableFactorSupply (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) : ℕ :=
  state.stock fiveProjectFactorSupplier fiveProjectCompletionGood +
    min D.householdFactorsOffered
      (min cursor.householdOfferRemaining
        (state.stock fiveProjectHousehold fiveProjectCompletionGood))

/-- At factor clearing, reuse the existing ascending clock and eligibility
test, with actual advances and currently offered physical factors. The existing
initial-buffer participation condition remains in force; each selected trade
is checked separately against current holdings by the physical interpreter.
An absent loan quote or absent clearing price remains `none`. -/
def fiveProjectDynamicFactorClearing (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    Option (ℕ × List LoanReservationBid) :=
  cursor.loanQuote.bind fun quote =>
    (ascendingCompletionFactorPrice? cursor.actualAdvances quote 1
      (fiveProjectAvailableFactorSupply D cursor state) 3).map fun price =>
        (price, factorDemandingProjectsAt cursor.actualAdvances quote price)

/-- Supplier-first seller selection for an already assigned factor purchase.
Household inventory participates only up to its stated remaining offer. -/
def fiveProjectCurrentFactorSeller? (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    Option FiveProjectPhysicalAgent :=
  if 0 < state.stock fiveProjectFactorSupplier fiveProjectCompletionGood then
    some fiveProjectFactorSupplier
  else if 0 < min cursor.householdOfferRemaining
      (state.stock fiveProjectHousehold fiveProjectCompletionGood) then
    some fiveProjectHousehold
  else none

/-- Neither fixed factor seller is one of the five borrowing agents. -/
theorem fiveProjectFactorSeller_ne_borrower (project : Fin 5) :
    fiveProjectFactorSupplier ≠ fiveProjectPhysicalBorrower project ∧
      fiveProjectHousehold ≠ fiveProjectPhysicalBorrower project := by
  constructor
  · intro heq
    have hval := congrArg Fin.val heq
    fin_cases project <;>
      norm_num [fiveProjectFactorSupplier, fiveProjectPhysicalBorrower] at hval
  · intro heq
    have hval := congrArg Fin.val heq
    fin_cases project <;>
      norm_num [fiveProjectHousehold, fiveProjectPhysicalBorrower] at hval

/-- Construct the next factor purchase from current offered stock. An empty
offer produces an idle instruction at this consumed cursor position. -/
def fiveProjectDynamicFactorPurchaseInstruction
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (project : Fin 5) (price : ℕ) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  if 0 < state.stock fiveProjectFactorSupplier fiveProjectCompletionGood then
    fiveProjectFactorPurchaseInstruction project fiveProjectFactorSupplier price
      (fiveProjectFactorSeller_ne_borrower project).1
  else if 0 < min cursor.householdOfferRemaining
      (state.stock fiveProjectHousehold fiveProjectCompletionGood) then
    fiveProjectFactorPurchaseInstruction project fiveProjectHousehold price
      (fiveProjectFactorSeller_ne_borrower project).2
  else fiveProjectPassiveInstruction

/-- Offer output using the quantity physically held and the customer's
remaining money, at the existing one-money-unit price. -/
def fiveProjectDynamicCustomerInstruction
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (project : Fin 5) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  let quantity := min
    (state.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood)
    (state.stock 6 fiveProjectMoneyGood)
  if 0 < quantity then fiveProjectCustomerPurchaseInstruction project quantity
  else fiveProjectPassiveInstruction

/-- Append one certified event to the physical trace. All transaction
projections are computed from this trace. -/
def fiveProjectApplyEvent (cursor : FiveProjectPhysicalCursor)
    (event : FiveProjectPhysicalEvent) : FiveProjectPhysicalCursor :=
  { cursor with events := cursor.events ++ [event] }

def fiveProjectApplyEvents (cursor : FiveProjectPhysicalCursor)
    (events : List FiveProjectPhysicalEvent) : FiveProjectPhysicalCursor :=
  events.foldl fiveProjectApplyEvent cursor

/-- Extract the transition's event list from its named phase, selected
profile, and pre-transition physical state. Every transfer constructor is
created from a `FiveProjectMatchedTransfer` proof, so unmatched proposals do
not enter the trace. -/
def fiveProjectTransitionEvents (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (profile : FiveProjectPhysicalProfile) : List FiveProjectPhysicalEvent :=
  match cursor.remainingPhases with
  | .noteIssuance :: _ =>
      if h : profile fiveProjectBank =
          .operate (.issueFiduciaryNotes D.fiduciaryNotesIssued) then
        [.notesIssued profile D.fiduciaryNotesIssued h]
      else []
  | .householdCashTransfer :: _ =>
      match fiveProjectMatchedTransfer? profile fiveProjectHousehold fiveProjectBank
          D.householdMoneyTransferred fiveProjectMoneyGood 0 fiveProjectMoneyGood with
      | none => []
      | some transfer => [.householdCashTransferred D.householdMoneyTransferred transfer]
  | .loanClearing :: _ => []
  | .loanAcceptance project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => []
      | some bid =>
          match fiveProjectMatchedTransfer? profile fiveProjectBank
              (fiveProjectPhysicalBorrower bid.borrower)
              fiveProjectLoanMarket.principal fiveProjectMoneyGood 0
              fiveProjectMoneyGood with
          | none => []
          | some transfer => [.advanceMatched bid transfer]
  | .householdConsumption :: _ => []
  | .factorClearing :: _ => []
  | .factorPurchase slot :: _ =>
      match cursor.factorClearing with
      | none => []
      | some (price, projects) =>
          match projects[slot.val]?, fiveProjectCurrentFactorSeller? cursor state with
          | some bid, some seller =>
              match fiveProjectMatchedTransfer? profile seller
                  (fiveProjectPhysicalBorrower bid.borrower) 1
                  fiveProjectCompletionGood price fiveProjectMoneyGood with
              | none => []
              | some transfer => [.factorPurchaseMatched bid seller transfer]
          | _, _ => []
  | .completion :: _ =>
      cursor.actualFactorPurchases.filterMap fun bid =>
        if h : profile (fiveProjectPhysicalBorrower bid.borrower) =
            .operate (.completeProject bid.borrower) then
          some (.projectCompleted profile bid h)
        else none
  | .customerSale project :: _ =>
      let quantity := min
        (state.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood)
        (state.stock 6 fiveProjectMoneyGood)
      if 0 < quantity then
        match fiveProjectMatchedTransfer? profile
            (fiveProjectPhysicalBorrower project) 6 quantity
            fiveProjectOutputGood quantity fiveProjectMoneyGood with
        | none => []
        | some transfer => [.customerOutputSold project quantity transfer]
      else []
  | .loanSettlement project :: _ =>
      match cursor.loanQuote, cursor.plannedAdvances[project.val]? with
      | some repayment, some bid =>
          if cursor.actualAdvances.contains bid then
            match fiveProjectMatchedTransfer? profile
                (fiveProjectPhysicalBorrower bid.borrower) fiveProjectBank repayment
                fiveProjectMoneyGood 0 fiveProjectMoneyGood with
            | none => []
            | some transfer => [.loanRepaid bid transfer]
          else []
      | _, _ => []
  | [] => []

/-- A borrowing project is a different physical actor from the bank. -/
theorem fiveProjectBorrower_ne_bank (project : Fin 5) :
    fiveProjectBank ≠ fiveProjectPhysicalBorrower project := by
  intro heq
  have hval := congrArg Fin.val heq
  fin_cases project <;>
    norm_num [fiveProjectBank, fiveProjectPhysicalBorrower] at hval

/-- A loan-offer stage contains a unilateral refusal profile: the bank keeps
its scheduled offer, the borrower idles, and every other actor keeps the
stage's idle action. Since offer and acceptance do not match, no advance event
is recorded. -/
theorem fiveProject_unilateral_loan_refusal
    (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (bid : LoanReservationBid)
    (hOffer : (fiveProjectAdvanceInstruction bid).affordableProfile
        fiveProjectPhysicalOperations state fiveProjectBank =
      .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
        fiveProjectLoanMarket.principal fiveProjectMoneyGood 0 fiveProjectMoneyGood) :
    let instruction := fiveProjectAdvanceInstruction bid
    let stage := instruction.stage fiveProjectPhysicalOperations state
    ∃ profile : stage.choices.Profile,
      profile.1 fiveProjectBank =
        .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
          fiveProjectLoanMarket.principal fiveProjectMoneyGood 0 fiveProjectMoneyGood ∧
      profile.1 (fiveProjectPhysicalBorrower bid.borrower) = .idle ∧
      (∀ peer, peer ≠ fiveProjectBank →
        peer ≠ fiveProjectPhysicalBorrower bid.borrower →
        profile.1 peer = instruction.profile peer) ∧
      fiveProjectTransitionEvents D
        { remainingPhases := [.loanAcceptance 0], plannedAdvances := [bid] }
        state profile.1 = [] := by
  let instruction := fiveProjectAdvanceInstruction bid
  let stage := instruction.stage fiveProjectPhysicalOperations state
  let offer : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
      fiveProjectLoanMarket.principal fiveProjectMoneyGood 0 fiveProjectMoneyGood
  have hmenu : offer ∈ stage.choices.menu fiveProjectBank := by
    change (EconomyAction.offer fiveProjectBank
        (fiveProjectPhysicalBorrower bid.borrower)
        fiveProjectLoanMarket.principal fiveProjectMoneyGood 0 fiveProjectMoneyGood) ∈
      insert EconomyAction.idle
        (insert ((fiveProjectAdvanceInstruction bid).affordableProfile
          fiveProjectPhysicalOperations state fiveProjectBank)
          ((fiveProjectAdvanceInstruction bid).affordableAlternatives
            fiveProjectPhysicalOperations state fiveProjectBank))
    rw [← hOffer]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  let profile := stage.choices.unilateralProfile fiveProjectBank offer hmenu
  have hbank : profile.1 fiveProjectBank = offer := by
    exact stage.choices.unilateralProfile_self fiveProjectBank offer hmenu
  have hborrower : profile.1 (fiveProjectPhysicalBorrower bid.borrower) = .idle := by
    exact stage.choices.unilateralProfile_other fiveProjectBank
      (fiveProjectPhysicalBorrower bid.borrower) offer hmenu
      (fiveProjectBorrower_ne_bank bid.borrower).symm
  refine ⟨profile, hbank, hborrower, ?_, ?_⟩
  · intro peer hpeerBank hpeerBorrower
    rw [stage.choices.unilateralProfile_other fiveProjectBank peer offer hmenu hpeerBank]
    simp [fiveProjectAdvanceInstruction, fiveProjectTransferInstruction,
      fiveProjectScheduledTransferProfile, hpeerBank, hpeerBorrower]
  · simp [fiveProjectTransitionEvents, offer, fiveProjectMatchedTransfer?,
      hbank, hborrower]

/-- Generate a branch's next proposal from its cursor and current inventory.
Clearing results already stored in the cursor remain fixed; later transfer
quantities and seller availability are read from the actual state. -/
def fiveProjectPhysicalInstruction (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  match cursor.remainingPhases with
  | .noteIssuance :: _ => fiveProjectIssueNotesInstruction D
  | .householdCashTransfer :: _ => fiveProjectHouseholdCashTransferInstruction D
  | .loanClearing :: _ => fiveProjectPassiveInstruction
  | .loanAcceptance project :: _ =>
      (cursor.plannedAdvances[project.val]?).elim
        fiveProjectPassiveInstruction fiveProjectAdvanceInstruction
  | .householdConsumption :: _ => fiveProjectHouseholdConsumptionInstruction D
  | .factorClearing :: _ => fiveProjectPassiveInstruction
  | .factorPurchase slot :: _ =>
      match cursor.factorClearing with
      | none => fiveProjectPassiveInstruction
      | some (price, projects) =>
          (projects[slot.val]?).elim fiveProjectPassiveInstruction fun bid =>
            fiveProjectDynamicFactorPurchaseInstruction cursor state bid.borrower price
  | .completion :: _ => fiveProjectCompletionInstruction cursor.actualFactorPurchases
  | .customerSale project :: _ => fiveProjectDynamicCustomerInstruction state project
  | .loanSettlement project :: _ =>
      match cursor.loanQuote, cursor.plannedAdvances[project.val]? with
      | some repayment, some bid =>
          if cursor.actualAdvances.contains bid then
            fiveProjectRepaymentInstruction
              { borrower := bid.borrower
                principal := fiveProjectLoanMarket.principal
                principal_positive := fiveProjectLoanMarket.principal_positive
                promisedRepayment := repayment }
          else fiveProjectPassiveInstruction
      | _, _ => fiveProjectPassiveInstruction
  | [] => fiveProjectPassiveInstruction

/-- Advance the finite cursor after interpreting the selected profile. Every
position is consumed; only exact matched transfers and enacted production are
added to the corresponding event records. -/
def fiveProjectNextCursor (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (state' : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    FiveProjectPhysicalCursor :=
  let next := { cursor with remainingPhases := cursor.remainingPhases.drop 1 }
  match cursor.remainingPhases with
  | .loanClearing :: _ =>
      let clearing := clearLoanMarket fiveProjectLoanMarket
          (state'.stock fiveProjectBank fiveProjectMoneyGood)
      let nextWithQuote := { next with loanQuote := clearing.quotedRepayment }
      { nextWithQuote with plannedAdvances := clearing.funded }
  | .factorClearing :: _ =>
      { next with factorClearing := fiveProjectDynamicFactorClearing D cursor state' }
  | _ => fiveProjectApplyEvents next
      (fiveProjectTransitionEvents D cursor state profile)

def fiveProjectPhysicalRegimeGenerator (D : FiveProjectRegimeData) :
    PhysicalProfileGenerator FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Unit FiveProjectPhysicalCursor where
  instruction := fiveProjectPhysicalInstruction D
  nextCursor := fiveProjectNextCursor D

/-- One concrete history prefix for regression witnesses. `true` selects the
instruction generator's affordable scheduled profile; `false` selects the
stage's all-idle profile. Each transition uses the same stage interpreter and
cursor update as the compiled program. -/
structure FiveProjectPhysicalRun where
  cursor : FiveProjectPhysicalCursor
  state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit

def fiveProjectInitialRun (D : FiveProjectRegimeData) : FiveProjectPhysicalRun :=
  { cursor := fiveProjectInitialCursor D
    state := fiveProjectFactorInitialState D }

def fiveProjectRunStep (D : FiveProjectRegimeData) (enactScheduled : Bool)
    (run : FiveProjectPhysicalRun) : FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let profile : stage.choices.Profile :=
    if enactScheduled then instruction.selectedProfile fiveProjectPhysicalOperations run.state
    else FiniteEconomyProgram.ProgramHistory.idleProfile stage.choices
  let state' := stage.advance profile
  exact { cursor := fiveProjectNextCursor D run.cursor run.state profile.1 state'
          state := state' }

/-- Execute one explicitly selected feasible profile at the generated stage.
This exposes unilateral menu branches to regression witnesses while retaining
the same physical interpreter and cursor update as scheduled execution. -/
def fiveProjectRunStepWithProfile (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun)
    (profile : ((fiveProjectPhysicalInstruction D run.cursor run.state).stage
      fiveProjectPhysicalOperations run.state).choices.Profile) :
    FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let state' := stage.advance profile
  exact { cursor := fiveProjectNextCursor D run.cursor run.state profile.1 state'
          state := state' }

/-- At the household-consumption cursor, enact the listed unilateral
consumption alternative when the specified stock is present. -/
def fiveProjectRunHouseholdConsumption (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun)
    (hphase : run.cursor.remainingPhases.head? = some .householdConsumption)
    (hpositive : 0 < D.householdFactorEndowment)
    (hstock : D.householdFactorEndowment ≤
      run.state.stock fiveProjectHousehold fiveProjectCompletionGood) :
    FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  have hinstruction : instruction = fiveProjectHouseholdConsumptionInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
      cases phase <;> simp_all [instruction, fiveProjectPhysicalInstruction]
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let consume : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .operate (.consumeHouseholdFactors D.householdFactorEndowment)
  have hmenu : consume ∈ stage.choices.menu fiveProjectHousehold := by
    change consume ∈ (instruction.stage fiveProjectPhysicalOperations run.state).choices.menu
      fiveProjectHousehold
    rw [hinstruction]
    exact fiveProject_household_consumption_is_available D run.state hpositive hstock
  let profile := stage.choices.unilateralProfile fiveProjectHousehold consume hmenu
  exact fiveProjectRunStepWithProfile D run profile

def fiveProjectRunChoices (D : FiveProjectRegimeData) :
    List Bool → FiveProjectPhysicalRun → FiveProjectPhysicalRun
  | [], run => run
  | enact :: rest, run =>
      fiveProjectRunChoices D rest (fiveProjectRunStep D enact run)

/-- Execute the first three named phases so issuance and household cash
transfer have either matched or been refused before loan capacity is read. -/
def fiveProjectFundingPrefix (D : FiveProjectRegimeData)
    (enactNotes enactHouseholdTransfer : Bool) : FiveProjectPhysicalRun :=
  fiveProjectRunChoices D [enactNotes, enactHouseholdTransfer, false]
    (fiveProjectInitialRun D)

/-- Refusing fiduciary note issuance leaves the bank with its original two
money units, so the subsequent loan clearing funds two instead of four loans.
The loan quote is computed from the actual post-branch bank balance. -/
theorem fiveProject_refused_issuance_changes_loan_capacity :
    let refused := fiveProjectFundingPrefix
      (fiveProjectRegimeData .fiduciaryExpansion) false true
    let enacted := fiveProjectFundingPrefix
      (fiveProjectRegimeData .fiduciaryExpansion) true true
    refused.cursor.actualNotesIssued = 0 ∧
    refused.cursor.plannedAdvances.length = 2 ∧
    refused.cursor.loanQuote = some 6 ∧
    enacted.cursor.actualNotesIssued = 2 ∧
    enacted.cursor.plannedAdvances.length = 4 ∧
    enacted.cursor.loanQuote = some 4 := by
  decide

/-- Refusing the household cash transfer leaves its money at home and lowers
the later bank clearing capacity. This conclusion concerns the transfer and
physical cash balances; it does not classify the transfer as purposeful
saving. -/
theorem fiveProject_refused_household_transfer_changes_loan_capacity :
    let refused := fiveProjectFundingPrefix
      (fiveProjectRegimeData .householdTransfer) true false
    let enacted := fiveProjectFundingPrefix
      (fiveProjectRegimeData .householdTransfer) true true
    refused.state.stock fiveProjectHousehold fiveProjectMoneyGood = 2 ∧
    refused.state.stock fiveProjectBank fiveProjectMoneyGood = 2 ∧
    refused.cursor.plannedAdvances.length = 2 ∧
    refused.cursor.loanQuote = some 6 ∧
    enacted.state.stock fiveProjectHousehold fiveProjectMoneyGood = 0 ∧
    enacted.state.stock fiveProjectBank fiveProjectMoneyGood = 4 ∧
    enacted.cursor.plannedAdvances.length = 4 ∧
    enacted.cursor.loanQuote = some 4 := by
  decide

/-- Reach factor clearing after the note and transfer branches, with one
choice variable for the first proposed advance. A refused advance is recorded
as absent from `actualAdvances`; the later market reads that list. -/
def fiveProjectFiduciaryFactorClearingRun (enactFirstAdvance : Bool) :
    FiveProjectPhysicalRun :=
  fiveProjectRunChoices (fiveProjectRegimeData .fiduciaryExpansion)
    [true, true, false, enactFirstAdvance, true, true, true, true, true, false]
    (fiveProjectInitialRun (fiveProjectRegimeData .fiduciaryExpansion))

/-- Refusing the first proposed advance changes the later factor-market input:
the clearing round sees three matched advances rather than the four planned
offers. The remaining offered factor supply and quoted loan terms are shared. -/
theorem fiveProject_refused_advance_changes_later_factor_input :
    let refused := fiveProjectFiduciaryFactorClearingRun false
    let enacted := fiveProjectFiduciaryFactorClearingRun true
    refused.cursor.plannedAdvances.length = 4 ∧
    refused.cursor.actualAdvances.length = 3 ∧
    enacted.cursor.actualAdvances.length = 4 ∧
    refused.cursor.loanQuote = some 4 ∧ enacted.cursor.loanQuote = some 4 ∧
    fiveProjectAvailableFactorSupply
      (fiveProjectRegimeData .fiduciaryExpansion) refused.cursor refused.state = 2 ∧
    fiveProjectAvailableFactorSupply
      (fiveProjectRegimeData .fiduciaryExpansion) enacted.cursor enacted.state = 2 ∧
    refused.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (2, [1]) ∧
    enacted.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (2, [0, 1]) := by
  decide

/-- Consume the household's stated factor endowment at its named phase, using
the existing unilateral branch in the generated choice stage. -/
def fiveProjectHouseholdConsumedBeforeFactorClearing : FiveProjectPhysicalRun := by
  let D := fiveProjectRegimeData .householdTransfer
  let before := fiveProjectRunChoices D (List.replicate 8 true)
    (fiveProjectInitialRun D)
  exact fiveProjectRunHouseholdConsumption D before (by decide) (by decide)
    (by decide)

def fiveProjectHouseholdRetainedBeforeFactorClearing : FiveProjectPhysicalRun :=
  fiveProjectRunChoices (fiveProjectRegimeData .householdTransfer)
    (List.replicate 9 true)
    (fiveProjectInitialRun (fiveProjectRegimeData .householdTransfer))

def fiveProjectHouseholdConsumedFactorClearing : FiveProjectPhysicalRun :=
  fiveProjectRunStep (fiveProjectRegimeData .householdTransfer) false
    fiveProjectHouseholdConsumedBeforeFactorClearing

def fiveProjectHouseholdRetainedFactorClearing : FiveProjectPhysicalRun :=
  fiveProjectRunStep (fiveProjectRegimeData .householdTransfer) false
    fiveProjectHouseholdRetainedBeforeFactorClearing

/-- The offered physical input entering the household-transfer regime's later
factor market falls from four units to two when the separately available
household consumption branch is enacted. Cash and advance counts do not create
the consumed physical units. -/
theorem fiveProject_household_consumption_changes_later_factor_input :
    let D := fiveProjectRegimeData .householdTransfer
    let before := fiveProjectRunChoices D (List.replicate 8 true)
      (fiveProjectInitialRun D)
    before.cursor.remainingPhases.head? = some .householdConsumption ∧
    before.state.stock fiveProjectHousehold fiveProjectCompletionGood = 2 ∧
    fiveProjectAvailableFactorSupply D before.cursor before.state = 4 ∧
    fiveProjectHouseholdConsumedBeforeFactorClearing.cursor.remainingPhases.head? =
      some .factorClearing ∧
    fiveProjectHouseholdConsumedBeforeFactorClearing.state.stock
      fiveProjectHousehold fiveProjectCompletionGood = 0 ∧
    fiveProjectAvailableFactorSupply D
      fiveProjectHouseholdConsumedBeforeFactorClearing.cursor
      fiveProjectHouseholdConsumedBeforeFactorClearing.state = 2 ∧
    fiveProjectHouseholdRetainedFactorClearing.cursor.factorClearing.map
      (fun clearing =>
        (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (1, [0, 1, 2, 3]) ∧
    fiveProjectHouseholdConsumedFactorClearing.cursor.factorClearing.map
      (fun clearing =>
        (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (2, [0, 1]) := by
  decide

/-- Refusing the first market-assigned completion-factor purchase consumes
that cursor position without retry. Completion and customer-sale instructions
are then derived from the one actually matched purchase. -/
theorem fiveProject_refused_factor_purchase_prevents_completion_and_sale :
    let D := fiveProjectRegimeData .fiduciaryExpansion
    let beforeRefusal := fiveProjectRunChoices D (List.replicate 10 true)
      (fiveProjectInitialRun D)
    let afterRefusal := fiveProjectRunChoices D [false] beforeRefusal
    let afterFactorSlots := fiveProjectRunChoices D (List.replicate 4 true) afterRefusal
    let afterCompletion := fiveProjectRunChoices D [true] afterFactorSlots
    let afterCustomerSales := fiveProjectRunChoices D (List.replicate 5 true) afterCompletion
    beforeRefusal.cursor.factorClearing.map
      (fun clearing => clearing.2.map LoanReservationBid.borrower) = some [0, 1] ∧
    afterRefusal.cursor.remainingPhases.head? = some (.factorPurchase 1) ∧
    afterRefusal.cursor.actualFactorPurchases = [] ∧
    afterFactorSlots.cursor.actualFactorPurchases.all
      (fun bid => decide (bid.borrower ≠ 0)) = true ∧
    afterCompletion.cursor.completedProjects.all
      (fun bid => decide (bid.borrower ≠ 0)) = true ∧
    afterCustomerSales.state.stock (fiveProjectPhysicalBorrower 0)
      fiveProjectOutputGood = 0 ∧
    afterCustomerSales.cursor.actualCustomerSales.all
      (fun sale => decide (sale.1 ≠ 0)) = true := by
  decide

/-- A contemplated factor offer with no matching acceptance is affordable
from supplier stock but has no physical effect under the shared inventory
interpreter. -/
def fiveProjectUnmatchedFactorOffer :
    ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation) :=
  fun actor =>
    if actor = fiveProjectFactorSupplier then
      .offer fiveProjectFactorSupplier (fiveProjectPhysicalBorrower 0) 1
        fiveProjectCompletionGood 1 fiveProjectMoneyGood
    else .idle

theorem fiveProject_unmatched_factor_offer_leaves_inventory_unchanged :
    ∀ agent good,
      (advanceIfAffordable fiveProjectPhysicalOperations
        (fiveProjectFactorInitialState (fiveProjectRegimeData .fiduciaryExpansion))
        fiveProjectUnmatchedFactorOffer).map (fun next => next.stock agent good) =
      some ((fiveProjectFactorInitialState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock agent good) := by
  intro agent good
  let state := fiveProjectFactorInitialState
    (fiveProjectRegimeData .fiduciaryExpansion)
  let profile := fiveProjectUnmatchedFactorOffer
  have hAffordable : profileAffordable? fiveProjectPhysicalOperations state profile = true := by
    decide
  let next := advanceState fiveProjectPhysicalOperations state profile
    (SolventProfile.ofAffordable fiveProjectPhysicalOperations state profile
      (profileAffordable_of_true fiveProjectPhysicalOperations state profile hAffordable))
  have hstep : advanceIfAffordable fiveProjectPhysicalOperations state profile = some next := by
    simp [advanceIfAffordable, hAffordable, next]
  have hbalance := advanceIfAffordable_sound fiveProjectPhysicalOperations
    state next profile hstep agent good
  have huse : effectiveUse fiveProjectPhysicalOperations profile agent good = 0 := by
    by_cases hs : agent = fiveProjectFactorSupplier
    · subst agent
      simp [profile, fiveProjectUnmatchedFactorOffer, effectiveUse,
        fiveProjectPhysicalBorrower, fiveProjectFactorSupplier]
    · simp [profile, fiveProjectUnmatchedFactorOffer, effectiveUse, hs]
  have hyield : effectiveYield fiveProjectPhysicalOperations profile agent good = 0 := by
    by_cases hs : agent = fiveProjectFactorSupplier
    · subst agent
      simp [profile, fiveProjectUnmatchedFactorOffer, effectiveYield,
        fiveProjectPhysicalBorrower, fiveProjectFactorSupplier]
    · simp [profile, fiveProjectUnmatchedFactorOffer, effectiveYield, hs]
  have hstock : next.stock agent good = state.stock agent good := by
    omega
  simp [hstep, hstock, state, profile]

/-- The named regime compiled into a bounded state-dependent physical
program. Each market is cleared when its cursor position is reached from the
actual branch inventory and previously matched events. -/
def fiveProjectPhysicalRegimeProgram (D : FiveProjectRegimeData) :=
  compilePhysicalProfileGenerator fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialState D)

/-- The generated history enacts each affordable scheduled profile through
the same state-dependent cursor and physical interpreter. -/
def fiveProjectPhysicalRegimeHistory (D : FiveProjectRegimeData) :=
  physicalProfileGeneratorHistory fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialState D)

/-- Final inventory state on the selected schedule history. -/
def fiveProjectPhysicalRegimeTerminalState (D : FiveProjectRegimeData) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit :=
  (fiveProjectPhysicalRegimeHistory D).terminalState

/-- Run the generated instruction sequence by enacting each affordable
scheduled profile. This is a convenience for checking the selected named
path; branch alternatives remain available through `fiveProjectRunStepWithProfile`.
-/
def fiveProjectNamedProgramRun (D : FiveProjectRegimeData) : FiveProjectPhysicalRun :=
  fiveProjectRunChoices D (List.replicate fiveProjectPhysicalFuel true)
    (fiveProjectInitialRun D)

/-- The direct selected-path runner and the compiled program's history have
the same interpreter-derived inventory at every agent and physical good. -/
theorem fiveProject_named_run_matches_compiled_history :
    ∀ regime agent good,
      (fiveProjectNamedProgramRun (fiveProjectRegimeData regime)).state.stock
          agent good =
        (fiveProjectPhysicalRegimeTerminalState
          (fiveProjectRegimeData regime)).stock agent good := by
  intro regime agent good
  cases regime <;> fin_cases agent <;> fin_cases good <;> decide

/-- The three selected paths record only matched funding, factor purchases,
customer sales, and repayments. Their clearing prices use the existing
initial-buffer rule, while each transfer is checked against the branch's
current physical holdings. -/
theorem fiveProject_named_program_records_cleared_and_matched_events :
    let baseline := fiveProjectNamedProgramRun (fiveProjectRegimeData .baseline)
    let fiduciary :=
      fiveProjectNamedProgramRun (fiveProjectRegimeData .fiduciaryExpansion)
    let household :=
      fiveProjectNamedProgramRun (fiveProjectRegimeData .householdTransfer)
    baseline.cursor.plannedAdvances.map LoanReservationBid.borrower = [0, 1] ∧
    baseline.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1] ∧
    baseline.cursor.loanQuote = some 6 ∧
    baseline.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (1, [0, 1]) ∧
    baseline.cursor.actualFactorPurchases.map LoanReservationBid.borrower = [0, 1] ∧
    baseline.cursor.actualCustomerSales = [(0, 9), (1, 8)] ∧
    baseline.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1] ∧
    fiduciary.cursor.actualNotesIssued = 2 ∧
    fiduciary.cursor.plannedAdvances.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    fiduciary.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    fiduciary.cursor.loanQuote = some 4 ∧
    fiduciary.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (2, [0, 1]) ∧
    fiduciary.cursor.actualFactorPurchases.map LoanReservationBid.borrower = [0, 1] ∧
    fiduciary.cursor.actualCustomerSales = [(0, 9), (1, 8)] ∧
    fiduciary.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1] ∧
    household.cursor.actualHouseholdMoneyTransferred = 2 ∧
    household.cursor.actualAdvances.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    household.cursor.loanQuote = some 4 ∧
    household.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (1, [0, 1, 2, 3]) ∧
    household.cursor.actualFactorPurchases.map LoanReservationBid.borrower =
      [0, 1, 2, 3] ∧
    household.cursor.actualCustomerSales = [(0, 9), (1, 8), (2, 7), (3, 6)] ∧
    household.cursor.actualRepayments.map LoanReservationBid.borrower =
      [0, 1, 2, 3] := by
  decide

/-- The scheduled cycle program satisfies the generic stable-operation
condition required to adapt it to `ActionFrame`. -/
theorem fiveProjectPhysicalRegimeProgram_stable (D : FiveProjectRegimeData) :
    (fiveProjectPhysicalRegimeProgram D).HasStableOperationSemantics
      fiveProjectPhysicalOperations :=
  compilePhysicalProfileGenerator_stable fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialState D)

/-- Add the supplied program-level beliefs and preferences to the physical
cycle program through the existing generic ActionFrame adapter. Cycle-wide
comparisons use each selected branch's terminal settlement inventory. -/
@[instance_reducible] noncomputable def fiveProjectPhysicalRegimeFrame (D : FiveProjectRegimeData)
    (behavior : (fiveProjectPhysicalRegimeProgram D).ActionFrameBehavior) : ActionFrame :=
  (fiveProjectPhysicalRegimeProgram D).toActionFrame fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeProgram_stable D)
    (behavior.withEvaluationHorizon (fun _ _ _ => .terminalSettlement))

/-- The compiled schedule's selected histories reproduce the named
market-calculation balances for the lender and funded borrowers. In the
fiduciary regime the marginal borrowers retain their two money units and
cannot transfer the promised four. This records an unpaid repayment attempt;
it does not classify that event as default. -/
theorem fiveProject_named_program_settlement_balances :
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        fiveProjectBank fiveProjectMoneyGood = 12 ∧
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 6 ∧
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 5 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        fiveProjectBank fiveProjectMoneyGood = 8 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 7 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 6 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood = 2 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood = 2 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        fiveProjectBank fiveProjectMoneyGood = 16 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 8 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 7 := by
  decide

end Praxeology
