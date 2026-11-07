/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.FactorExecution
public import Praxeology.Catallactics.Credit
public import Praxeology.FiniteEconomy.ProfileSchedule
public import Praxeology.FiniteEconomy.ProgramActionFrame

/-!
# Recursive physical program for the five-project scenario

The fuel-bounded instruction generator uses a finite cursor and the current
physical state to stage household-plan selection, note issuance, the household
deposit exchange, loan clearing and advances, early-input purchases, capital
formation, household consumption, factor clearing and purchases, completion,
customer purchases, repayments, and contractual settlement. Loan capacity is
cleared from the bank's actual money when that round is reached; factor
clearing uses actually matched advances, current holdings, and explicitly
offered factor stock. Each clearing result is retained after assignment, while
later rounds are computed from the state reached on that branch. A failed
transfer consumes its cursor position and is not retried. The generic
profile-schedule compiler remains available as the fixed-schedule
specialization. Every physical transition uses the existing inventory
interpreter.

The household plan menu independently varies an affordable deposit, consumed
factors, and offered factors subject to its initial factor stock. Unoffered
factors remain in inventory. Consumption service and matched contract events
are recorded separately from physical holdings. The program does not derive
purposeful household saving, purposeful investment, or foreclosure from its
physical transitions. Menu availability does not establish choice; projected
eligibility, physical affordability, purposeful choice, and contextual regret
remain separate claims.
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

/-- A passive instruction occupies an absent or already exhausted cursor
slot. The slot still advances, preventing an automatic retry. -/
def fiveProjectPassiveInstruction :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile := fun _ => .idle
  wellFormed := by intro actor; simp [EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by intro actor action h; simp at h

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

/-- Complete finite choices for the household's initial plan: no deposit or
the stated affordable deposit principal, every consumption quantity from zero
through current factor holdings, and every offer quantity that does not exceed
the factors left after consumption. Unoffered factors remain household property.
-/
def fiveProjectHouseholdPlanChoices (D : FiveProjectRegimeData) :
    Finset FiveProjectHouseholdPlan :=
  let depositChoices : Finset ℕ :=
    if fiveProjectHouseholdDepositTerms.principal ≤ D.householdMoneyEndowment then
      {0, fiveProjectHouseholdDepositTerms.principal}
    else {0}
  let rawChoices :=
    (depositChoices.product (Finset.range (D.householdFactorEndowment + 1))).product
      (Finset.range (D.householdFactorEndowment + 1))
  (rawChoices.filter fun choices =>
    choices.1.2 + choices.2 ≤ D.householdFactorEndowment).image fun choices =>
      { deposit := choices.1.1
        consumedFactors := choices.1.2
        offeredFactors := choices.2 }

/-- Every plan in the household menu respects its initial factor endowment.
The bound is a filter condition on the generated plan set, not an extra
economic premise. -/
theorem fiveProjectHouseholdPlanChoices_within_factor_endowment
    (D : FiveProjectRegimeData) (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices D) :
    plan.consumedFactors + plan.offeredFactors ≤ D.householdFactorEndowment := by
  rcases Finset.mem_image.mp hplan with ⟨choices, hchoices, rfl⟩
  exact (Finset.mem_filter.mp hchoices).2

/-- In the household-transfer regime the full menu has both affordable deposit
choices and all twelve factor plans (six consumption/offer pairs for each
deposit choice). -/
theorem fiveProject_household_transfer_menu_cardinality :
    (fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)).card = 12 := by
  decide

/-- The menu contains the no-deposit/consume-two and the deposit-two/offer-two
plans. These witnesses keep consumption and market offering as separate
choices. -/
theorem fiveProject_household_transfer_menu_key_plans :
    let D := fiveProjectRegimeData .householdTransfer
    ({ deposit := 0, consumedFactors := 2, offeredFactors := 0 } :
        FiveProjectHouseholdPlan) ∈ fiveProjectHouseholdPlanChoices D ∧
    ({ deposit := 2, consumedFactors := 0, offeredFactors := 2 } :
        FiveProjectHouseholdPlan) ∈ fiveProjectHouseholdPlanChoices D := by
  decide

/-- The household's finite plan-action alternatives. The action records a
plan in the generator cursor; it does not create money or goods. -/
def fiveProjectHouseholdPlanChoiceActions (D : FiveProjectRegimeData) :
    Finset (EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation) :=
  (fiveProjectHouseholdPlanChoices D).image fun plan =>
    .operate (.chooseHouseholdPlan plan)

/-- Initial plan instruction. Its scheduled profile preserves the named
regime's plan as the selected path, while the finite menu exposes every
affordable deposit, consumption, and offer combination. -/
def fiveProjectHouseholdPlanInstruction (D : FiveProjectRegimeData) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile actor :=
    if actor = fiveProjectHousehold then
      .operate (.chooseHouseholdPlan (fiveProjectHouseholdPlanOf D))
    else .idle
  wellFormed := by
    intro actor
    by_cases hhousehold : actor = fiveProjectHousehold <;>
      simp [hhousehold, EconomyAction.WellFormed]
  alternatives actor :=
    if actor = fiveProjectHousehold then fiveProjectHouseholdPlanChoiceActions D else ∅
  alternatives_wellFormed := by
    intro actor action h
    by_cases hhousehold : actor = fiveProjectHousehold
    · subst actor
      rcases Finset.mem_image.mp h with ⟨plan, _, haction⟩
      rw [← haction]
      simp [EconomyAction.WellFormed]
    · simp [hhousehold] at h

/-- Profile instruction for the household source leg. The named saving branch
exchanges the two-unit principal for the deposit claim; other named regimes
have no deposit claim to transfer. -/
def fiveProjectHouseholdCashTransferInstruction (plan : FiveProjectHouseholdPlan) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  if plan.deposit = fiveProjectHouseholdDepositTerms.principal then
    fiveProjectTransferInstruction fiveProjectHouseholdDepositTerms.holder
      fiveProjectHouseholdDepositTerms.issuer
      fiveProjectHouseholdDepositTerms.holder_ne_issuer
      fiveProjectHouseholdDepositTerms.principal
      fiveProjectHouseholdDepositTerms.moneyGood
      fiveProjectHouseholdDepositTerms.claimQuantity
      fiveProjectHouseholdDepositTerms.claimGood
  else fiveProjectPassiveInstruction

/-- A missing plan means the household idled at its planning stage; later
household transfer and consumption stages are consequently passive. -/
def fiveProjectHouseholdCashTransferInstruction? (plan : Option FiveProjectHouseholdPlan) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  plan.elim fiveProjectPassiveInstruction fiveProjectHouseholdCashTransferInstruction

/-- Execute the consumption quantity selected in the initial household plan.
Its physical effect is interpreted later from the current stock. -/
def fiveProjectPlannedHouseholdConsumptionInstruction
    (plan : Option FiveProjectHouseholdPlan) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  match plan with
  | none => fiveProjectPassiveInstruction
  | some plan =>
      { profile actor :=
          if actor = fiveProjectHousehold then
            if plan.consumedFactors = 0 then .idle
            else .operate (.consumeHouseholdFactors plan.consumedFactors)
          else .idle
        wellFormed := by
          intro actor
          by_cases hhousehold : actor = fiveProjectHousehold
          · subst actor
            by_cases hconsume : plan.consumedFactors = 0 <;>
              simp [hconsume, EconomyAction.WellFormed]
          · simp [hhousehold, EconomyAction.WellFormed]
        alternatives := fun _ => ∅
        alternatives_wellFormed := by
          intro actor action h
          simp at h }

/-- Redemption is a separate matched exchange. The bank's cash balance is
checked by the stage's physical interpreter at this later cursor position. -/
def fiveProjectDepositRedemptionInstruction (terms : FiveProjectDepositTerms) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction terms.holder terms.issuer
    terms.holder_ne_issuer terms.claimQuantity terms.claimGood
    terms.promisedRepayment terms.moneyGood

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
    fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
    (fiveProjectCollateralGood bid.borrower)

/-- An accepted borrower purchases one early input for one unit of money.
Whether the transfer occurs is determined by the matched physical actions. -/
def fiveProjectEarlyInputPurchaseInstruction (bid : LoanReservationBid) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  fiveProjectTransferInstruction fiveProjectFactorSupplier
    (fiveProjectPhysicalBorrower bid.borrower)
    (by
      intro h
      have hval := congrArg Fin.val h
      simp [fiveProjectFactorSupplier, fiveProjectPhysicalBorrower] at hval
      )
    1 fiveProjectEarlyInputGood 1 fiveProjectMoneyGood

/-- Convert one purchased early input into one unit of project capital through
the existing operation interpreter. Missing inputs make the scheduled action
unaffordable and its selected profile idles. -/
def fiveProjectCapitalConversionInstruction (bid : LoanReservationBid) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation where
  profile actor :=
    if actor = fiveProjectPhysicalBorrower bid.borrower then
      .operate (.convertEarlyInputToCapital bid.borrower)
    else .idle
  wellFormed := by
    intro actor
    by_cases hborrower : actor = fiveProjectPhysicalBorrower bid.borrower
    · subst actor
      simp [EconomyAction.WellFormed]
    · simp [hborrower, EconomyAction.WellFormed]
  alternatives := fun _ => ∅
  alternatives_wellFormed := by
    intro actor action h
    simp at h

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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
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
    1 (fiveProjectCollateralGood contract.borrower)

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

/-- The current finite settlement schedule. Project-specific phases carry
their project index, so inserting an earlier phase does not silently change
the identity of a later transaction. -/
def fiveProjectPhysicalPhases : List FiveProjectPhysicalPhase :=
  [.chooseHouseholdPlan, .noteIssuance, .householdCashTransfer, .loanClearing,
   .loanAcceptance 0, .loanAcceptance 1, .loanAcceptance 2,
   .loanAcceptance 3, .loanAcceptance 4,
   .earlyInputPurchase 0, .capitalConversion 0,
   .earlyInputPurchase 1, .capitalConversion 1,
   .earlyInputPurchase 2, .capitalConversion 2,
   .earlyInputPurchase 3, .capitalConversion 3,
   .earlyInputPurchase 4, .capitalConversion 4, .householdConsumption,
   .factorClearing, .factorPurchase 0, .factorPurchase 1,
   .factorPurchase 2, .factorPurchase 3, .factorPurchase 4,
   .completion 0, .completion 1, .completion 2, .completion 3, .completion 4,
   .customerSale 0, .customerSale 1, .customerSale 2,
   .customerSale 3, .customerSale 4, .loanSettlement 0,
   .loanSettlement 1, .loanSettlement 2, .loanSettlement 3,
   .loanSettlement 4, .loanMaturitySettlement 0,
   .loanMaturitySettlement 1, .loanMaturitySettlement 2,
   .loanMaturitySettlement 3, .loanMaturitySettlement 4,
   .depositSettlement]

def fiveProjectPhysicalFuel : ℕ := fiveProjectPhysicalPhases.length

/-- The phase schedule names every physical stage once. -/
theorem fiveProjectPhysicalPhases_nodup :
    fiveProjectPhysicalPhases.Nodup := by
  decide

abbrev FiveProjectPhysicalProfile :=
  ActionProfile (Agent := FiveProjectPhysicalAgent)
    (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation)

/-- Evidence attached to a physical transfer event. Besides exact bilateral
matching, it retains the typed interpreter step that executed those actions.
Thus an event record carries its before-state and exact transition evidence. -/
structure FiveProjectMatchedTransfer where
  before : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat
  step : PhysicalProfileStep fiveProjectPhysicalOperations before
  seller : FiveProjectPhysicalAgent
  buyer : FiveProjectPhysicalAgent
  quantity : ℕ
  good : FiveProjectPhysicalGood
  payment : ℕ
  moneyGood : FiveProjectPhysicalGood
  offerEnacted : step.profile.1 seller =
    .offer seller buyer quantity good payment moneyGood
  acceptanceEnacted : step.profile.1 buyer =
    .accept buyer seller quantity good payment moneyGood

namespace FiveProjectMatchedTransfer

def profile (transfer : FiveProjectMatchedTransfer) : FiveProjectPhysicalProfile :=
  transfer.step.profile.1

def after (transfer : FiveProjectMatchedTransfer) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat :=
  (transfer.step.instruction.stage fiveProjectPhysicalOperations transfer.before).advance
    transfer.step.profile

/-- The interpreter's post-state satisfies the matched seller and buyer
inventory equations for every good. -/
theorem bilateral_balance (transfer : FiveProjectMatchedTransfer) :
    (∀ good, transfer.after.stock transfer.seller good +
      (if good = transfer.good then transfer.quantity else 0) =
      transfer.before.stock transfer.seller good +
      (if good = transfer.moneyGood then transfer.payment else 0)) ∧
    (∀ good, transfer.after.stock transfer.buyer good +
      (if good = transfer.moneyGood then transfer.payment else 0) =
      transfer.before.stock transfer.buyer good +
      (if good = transfer.good then transfer.quantity else 0)) := by
  constructor
  · intro good
    have hbalance := transfer.step.after_balance transfer.seller good
    simpa [after, effectiveUse, effectiveYield, transfer.offerEnacted,
      transfer.acceptanceEnacted] using hbalance
  · intro good
    have hbalance := transfer.step.after_balance transfer.buyer good
    simpa [after, effectiveUse, effectiveYield, transfer.offerEnacted,
      transfer.acceptanceEnacted] using hbalance

/-- A recorded matched transfer conserves the pair's combined stock of every
good, including when the two exchanged goods coincide. -/
theorem pair_conservation (transfer : FiveProjectMatchedTransfer) :
    ∀ good, transfer.after.stock transfer.seller good +
        transfer.after.stock transfer.buyer good =
      transfer.before.stock transfer.seller good +
        transfer.before.stock transfer.buyer good := by
  obtain ⟨hseller, hbuyer⟩ := transfer.bilateral_balance
  intro good
  have hs := hseller good
  have hb := hbuyer good
  omega

end FiveProjectMatchedTransfer

/-- A transition emits only enacted operations and exactly matched transfers.
The physical inventory transition remains the interpreter's responsibility;
these records identify its resulting contractual and market events. -/
inductive FiveProjectPhysicalEvent where
  | householdPlanSelected (profile : FiveProjectPhysicalProfile)
      (plan : FiveProjectHouseholdPlan)
      (enacted : profile fiveProjectHousehold =
        .operate (.chooseHouseholdPlan plan))
  | householdConsumptionDelivered (profile : FiveProjectPhysicalProfile)
      (quantity : ℕ)
      (enacted : profile fiveProjectHousehold =
        .operate (.consumeHouseholdFactors quantity))
  | notesIssued (profile : FiveProjectPhysicalProfile) (quantity : ℕ)
      (enacted : profile fiveProjectBank =
        .operate (.issueFiduciaryNotes quantity))
  | depositOpened (terms : FiveProjectDepositTerms)
      (transfer : FiveProjectMatchedTransfer)
  | depositRedeemed (terms : FiveProjectDepositTerms)
      (transfer : FiveProjectMatchedTransfer)
  | advanceMatched (bid : LoanReservationBid)
      (agreement : FiveProjectPawnAgreement)
      (transfer : FiveProjectMatchedTransfer)
      (transition : CreditTransition .unadvanced .advance .outstanding)
  | earlyInputPurchased (bid : LoanReservationBid)
      (transfer : FiveProjectMatchedTransfer)
  | capitalFormed (profile : FiveProjectPhysicalProfile)
      (bid : LoanReservationBid)
      (enacted : profile (fiveProjectPhysicalBorrower bid.borrower) =
        .operate (.convertEarlyInputToCapital bid.borrower))
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
      (transition : CreditTransition .outstanding .repayment .repaid)
  | contractualDefaultSettled (bid : LoanReservationBid)
      (agreement : FiveProjectPawnAgreement)
      (maturityState : PhysicalState FiveProjectPhysicalAgent
        FiveProjectPhysicalGood Nat)
      (profile : FiveProjectPhysicalProfile)
      (bankRetainsCollateral : maturityState.stock fiveProjectBank
        (fiveProjectCollateralGood bid.borrower) = 1)
      (transition : CreditTransition .outstanding .unpaidMaturity .defaulted)

/-- The completion instruction is generated only from the cursor's previously
matched factor purchases. The operation interpreter checks those acquired
factor units and the project's capital as inputs before it enacts completion. -/
def fiveProjectCompletionEvents (projects : List LoanReservationBid)
    (profile : FiveProjectPhysicalProfile) : List FiveProjectPhysicalEvent :=
  projects.filterMap fun bid =>
    if h : profile (fiveProjectPhysicalBorrower bid.borrower) =
        .operate (.completeProject bid.borrower) then
      some (.projectCompleted profile bid h)
    else none

/-- Any event emitted by the completion stage names a project previously
recorded as having purchased a completion factor. -/
theorem fiveProjectCompletionEvents_from_recorded_purchases
    (projects : List LoanReservationBid) (profile : FiveProjectPhysicalProfile)
    (event : FiveProjectPhysicalEvent)
    (hevent : event ∈ fiveProjectCompletionEvents projects profile) :
    ∃ bid ∈ projects, ∃ enacted,
      event = .projectCompleted profile bid enacted := by
  rcases List.mem_filterMap.mp hevent with ⟨bid, hbid, hmap⟩
  by_cases henacted : profile (fiveProjectPhysicalBorrower bid.borrower) =
      .operate (.completeProject bid.borrower)
  · simp only [dite_eq_left henacted] at hmap
    cases hmap
    exact ⟨bid, hbid, henacted, rfl⟩
  · simp only [dite_eq_right henacted] at hmap
    cases hmap

/-- Completion-event generation emits at most one record per previously
matched factor purchase. Together with the interpreter's one-factor input law,
this prevents a single acquired unit from generating repeated completions. -/
private theorem list_length_filterMap_le {α β : Type} (f : α → Option β)
    (xs : List α) : (xs.filterMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      cases h : f x with
      | none =>
          simpa [List.filterMap, h] using
            (le_trans ih (Nat.le_succ rest.length))
      | some y =>
          simpa [List.filterMap, h] using Nat.succ_le_succ ih

theorem fiveProjectCompletionEvents_length_le_projects
    (projects : List LoanReservationBid)
    (profile : FiveProjectPhysicalProfile) :
    (fiveProjectCompletionEvents projects profile).length ≤ projects.length := by
  exact list_length_filterMap_le _ projects

/-- An enacted completion consumes exactly the acquired completion factor and
one unit of project capital through the declared operation semantics. -/
theorem fiveProject_completed_project_consumes_inputs
    (profile : FiveProjectPhysicalProfile) (bid : LoanReservationBid)
    (henacted : profile (fiveProjectPhysicalBorrower bid.borrower) =
      .operate (.completeProject bid.borrower)) :
    effectiveUse fiveProjectPhysicalOperations profile
        (fiveProjectPhysicalBorrower bid.borrower) fiveProjectCompletionGood = 1 ∧
    effectiveUse fiveProjectPhysicalOperations profile
        (fiveProjectPhysicalBorrower bid.borrower) fiveProjectCapitalGood = 1 := by
  simp [effectiveUse, henacted, fiveProjectPhysicalOperations,
    fiveProjectCompletionGood, fiveProjectCapitalGood]

/-- A recorded household consumption action delivers the same service
quantity specified by the existing operation semantics. -/
theorem fiveProject_household_consumption_delivers_recorded_service
    (profile : FiveProjectPhysicalProfile) (quantity : ℕ)
    (henacted : profile fiveProjectHousehold =
      .operate (.consumeHouseholdFactors quantity)) :
    effectiveServiceYield fiveProjectPhysicalOperations profile
      fiveProjectHousehold fiveProjectConsumptionService = quantity := by
  simp [effectiveServiceYield, henacted, fiveProjectPhysicalOperations,
    fiveProjectConsumptionService]

/-- The profile that enacted an event. Transfer events refer to the profile
stored in their exact matching evidence. -/
def FiveProjectPhysicalEvent.profile : FiveProjectPhysicalEvent →
    FiveProjectPhysicalProfile
  | .householdPlanSelected profile _ _ => profile
  | .householdConsumptionDelivered profile _ _ => profile
  | .notesIssued profile _ _ => profile
  | .depositOpened _ transfer => transfer.profile
  | .depositRedeemed _ transfer => transfer.profile
  | .advanceMatched _ _ transfer _ => transfer.profile
  | .earlyInputPurchased _ transfer => transfer.profile
  | .capitalFormed profile _ _ => profile
  | .factorPurchaseMatched _ _ transfer => transfer.profile
  | .projectCompleted profile _ _ => profile
  | .customerOutputSold _ _ transfer => transfer.profile
  | .loanRepaid _ transfer _ => transfer.profile
  | .contractualDefaultSettled _ _ _ profile _ _ => profile

/-- An event record keeps the named schedule position that generated it.
This provenance comes from the cursor head at the interpreted transition; it
does not infer a phase from the economic content of the event afterward. -/
structure FiveProjectPhysicalEventRecord where
  phase : FiveProjectPhysicalPhase
  event : FiveProjectPhysicalEvent

/-- Tag every event produced by a transition with the phase it consumes. -/
def fiveProjectRecordTransitionEvents (phases : List FiveProjectPhysicalPhase)
    (events : List FiveProjectPhysicalEvent) : List FiveProjectPhysicalEventRecord :=
  match phases with
  | [] => []
  | phase :: _ => events.map fun event => ⟨phase, event⟩

/-- The phase attached to each record is the current schedule head. -/
theorem fiveProjectRecordTransitionEvents_phase (phase : FiveProjectPhysicalPhase)
    (rest : List FiveProjectPhysicalPhase) (events : List FiveProjectPhysicalEvent)
    (record : FiveProjectPhysicalEventRecord)
    (hrecord : record ∈ fiveProjectRecordTransitionEvents (phase :: rest) events) :
    record.phase = phase := by
  rcases List.mem_map.mp hrecord with ⟨event, _, heq⟩
  cases heq
  rfl

/-- If a transition emits at most one event, its recorded phase list is a
sublist of the singleton list containing its schedule head. -/
theorem fiveProjectRecordTransitionEvents_phases_sublist
    (phase : FiveProjectPhysicalPhase) (rest : List FiveProjectPhysicalPhase)
    (events : List FiveProjectPhysicalEvent) (hlength : events.length ≤ 1) :
    List.Sublist
      ((fiveProjectRecordTransitionEvents (phase :: rest) events).map
        FiveProjectPhysicalEventRecord.phase) [phase] := by
  cases events with
  | nil => simp [fiveProjectRecordTransitionEvents]
  | cons event tail =>
      cases tail with
      | nil => simp [fiveProjectRecordTransitionEvents]
      | cons next rest =>
          simp at hlength

structure FiveProjectPhysicalCursor where
  remainingPhases : List FiveProjectPhysicalPhase := fiveProjectPhysicalPhases
  consumedPhases : List FiveProjectPhysicalPhase := []
  eventTrace : List FiveProjectPhysicalEventRecord := []
  loanQuote : Option ℕ := none
  plannedAdvances : List LoanReservationBid := []
  factorClearing : Option (ℕ × List LoanReservationBid) := none
  householdOfferLimit : ℕ := 0
  householdPlan : Option FiveProjectHouseholdPlan := none

def FiveProjectPhysicalCursor.events (cursor : FiveProjectPhysicalCursor) :
    List FiveProjectPhysicalEvent :=
  cursor.eventTrace.map FiveProjectPhysicalEventRecord.event

/-- The consumed prefix followed by the unconsumed suffix is the original
named schedule. This predicate is maintained even when an action is refused. -/
def FiveProjectPhysicalCursor.preservesSchedule (cursor : FiveProjectPhysicalCursor) : Prop :=
  cursor.consumedPhases ++ cursor.remainingPhases = fiveProjectPhysicalPhases

/-- The event phases in the trace are a sublist of the phases actually
consumed. This is the trace provenance invariant used to establish uniqueness
of recorded schedule positions. -/
def FiveProjectPhysicalCursor.tracePhaseSublist (cursor : FiveProjectPhysicalCursor) : Prop :=
  List.Sublist (cursor.eventTrace.map FiveProjectPhysicalEventRecord.phase)
    cursor.consumedPhases

/-- Any cursor whose consumed and remaining phases reconstruct the initial
schedule has no duplicate consumed phase. -/
theorem FiveProjectPhysicalCursor.consumedPhases_nodup
    (cursor : FiveProjectPhysicalCursor) (hcursor : cursor.preservesSchedule) :
    cursor.consumedPhases.Nodup := by
  have hnodup : (cursor.consumedPhases ++ cursor.remainingPhases).Nodup := by
    rw [hcursor]
    exact fiveProjectPhysicalPhases_nodup
  exact List.Nodup.of_append_left hnodup

/-- Transaction summaries are views over event records. Those records are
appended only by `fiveProjectNextCursor` from the selected interpreter step. -/
def FiveProjectPhysicalCursor.actualNotesIssued
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  (cursor.events.filterMap fun
    | .notesIssued _ quantity _ => some quantity
    | _ => none).sum

def FiveProjectPhysicalCursor.actualHouseholdMoneyTransferred
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  (cursor.events.filterMap fun
    | .depositOpened terms _ => some terms.principal
    | _ => none).sum

def FiveProjectPhysicalCursor.actualHouseholdPlans
    (cursor : FiveProjectPhysicalCursor) : List FiveProjectHouseholdPlan :=
  cursor.events.filterMap fun
    | .householdPlanSelected _ plan _ => some plan
    | _ => none

def FiveProjectPhysicalCursor.actualHouseholdConsumptionServices
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  (cursor.events.filterMap fun
    | .householdConsumptionDelivered _ quantity _ => some quantity
    | _ => none).sum

def FiveProjectPhysicalCursor.actualDepositContract
    (cursor : FiveProjectPhysicalCursor) : Option FiveProjectDepositTerms :=
  (cursor.events.filterMap fun
    | .depositOpened terms _ => some terms
    | _ => none).head?

def FiveProjectPhysicalCursor.actualDepositRedemptions
    (cursor : FiveProjectPhysicalCursor) : List FiveProjectDepositTerms :=
  cursor.events.filterMap fun
    | .depositRedeemed terms _ => some terms
    | _ => none

def FiveProjectPhysicalCursor.actualAdvances
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .advanceMatched bid _ _ _ => some bid
    | _ => none

/-- Contractual terms become active only with the matched origination event.
Later default settlement retrieves these same terms rather than constructing
new debt conditions at maturity. -/
def FiveProjectPhysicalCursor.actualPawnAgreements
    (cursor : FiveProjectPhysicalCursor) : List FiveProjectPawnAgreement :=
  cursor.events.filterMap fun
    | .advanceMatched _ agreement _ _ => some agreement
    | _ => none

def FiveProjectPhysicalCursor.pawnAgreement?
    (cursor : FiveProjectPhysicalCursor) (bid : LoanReservationBid) :
    Option FiveProjectPawnAgreement :=
  cursor.actualPawnAgreements.find? fun agreement => decide (agreement.bid = bid)

theorem FiveProjectPhysicalCursor.pawnAgreement?_bid
    (cursor : FiveProjectPhysicalCursor) (bid : LoanReservationBid)
    (agreement : FiveProjectPawnAgreement)
    (hfound : cursor.pawnAgreement? bid = some agreement) : agreement.bid = bid := by
  unfold FiveProjectPhysicalCursor.pawnAgreement? at hfound
  have hmatch := List.find?_some
    (p := fun (candidate : FiveProjectPawnAgreement) =>
      decide (candidate.bid = bid)) hfound
  exact of_decide_eq_true hmatch

def FiveProjectPhysicalCursor.actualFactorPurchases
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .factorPurchaseMatched bid _ _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.actualEarlyInputPurchases
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .earlyInputPurchased bid _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.capitalFormations
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .capitalFormed _ bid _ => some bid
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
    | .loanRepaid bid _ _ => some bid
    | _ => none

def FiveProjectPhysicalCursor.actualDefaults
    (cursor : FiveProjectPhysicalCursor) : List LoanReservationBid :=
  cursor.events.filterMap fun
    | .contractualDefaultSettled bid _ _ _ _ _ => some bid
    | _ => none

abbrev FiveProjectLoanStatus := CreditStatus

/-- Contract status is read from recorded physical events, not from a
behavioral repayment certificate. -/
def FiveProjectPhysicalCursor.loanStatus
    (cursor : FiveProjectPhysicalCursor) (bid : LoanReservationBid) :
    FiveProjectLoanStatus :=
  if cursor.actualDefaults.contains bid then .defaulted
  else if cursor.actualRepayments.contains bid then .repaid
  else if cursor.actualAdvances.contains bid then .outstanding
  else .unadvanced

def FiveProjectPhysicalCursor.householdOfferRemaining
    (cursor : FiveProjectPhysicalCursor) : ℕ :=
  cursor.householdOfferLimit -
    (cursor.events.filter fun
      | .factorPurchaseMatched _ seller _ => decide (seller = fiveProjectHousehold)
      | _ => false).length

def fiveProjectInitialCursor (D : FiveProjectRegimeData) : FiveProjectPhysicalCursor :=
  { householdOfferLimit := D.householdFactorsOffered
    householdPlan := some (fiveProjectHouseholdPlanOf D) }

theorem fiveProjectInitialCursor_preserves_schedule (D : FiveProjectRegimeData) :
    (fiveProjectInitialCursor D).preservesSchedule := by
  simp [FiveProjectPhysicalCursor.preservesSchedule, fiveProjectInitialCursor]

theorem fiveProjectInitialCursor_tracePhaseSublist (D : FiveProjectRegimeData) :
    (fiveProjectInitialCursor D).tracePhaseSublist := by
  simp [FiveProjectPhysicalCursor.tracePhaseSublist, fiveProjectInitialCursor]

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
    (before : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations before)
    (seller buyer : FiveProjectPhysicalAgent) (quantity : ℕ)
    (good : FiveProjectPhysicalGood) (payment : ℕ)
    (moneyGood : FiveProjectPhysicalGood) : Option FiveProjectMatchedTransfer :=
  if h : step.profile.1 seller = .offer seller buyer quantity good payment moneyGood ∧
      step.profile.1 buyer = .accept buyer seller quantity good payment moneyGood then
    some (FiveProjectMatchedTransfer.mk before step seller buyer quantity good payment
      moneyGood h.1 h.2)
  else none

/-- Supplier stock plus only the household stock it explicitly offers,
capped by the quantity remaining and the household's current holdings. -/
def fiveProjectAvailableFactorSupply (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) : ℕ :=
  state.stock fiveProjectFactorSupplier fiveProjectCompletionGood +
    min D.householdFactorEndowment
      (min cursor.householdOfferRemaining
        (state.stock fiveProjectHousehold fiveProjectCompletionGood))

/-- At factor clearing, reuse the ascending clock with actual advances, each
borrower's current cash, projected output, and currently offered factors.
Physical affordability is still checked by the interpreter when a transfer is
selected. An absent quote or price remains `none`. -/
def fiveProjectDynamicFactorClearing (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    Option (ℕ × List LoanReservationBid) :=
  cursor.loanQuote.bind fun quote =>
    fiveProjectClearFactorMarketAtState cursor.actualAdvances quote
      (fiveProjectAvailableFactorSupply D cursor state) state

/-- Re-clearing the factor market at any reached state respects the physical
quantity offered there. Thus changing cash buffers can change the clock's
price and eligible bids, but it cannot make this auction allocate more units
than the current offered stock. -/
theorem fiveProjectDynamicFactorClearing_projects_le_available_supply
    (D : FiveProjectRegimeData) (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (price : ℕ) (projects : List LoanReservationBid)
    (hclear : fiveProjectDynamicFactorClearing D cursor state = some (price, projects)) :
    projects.length ≤ fiveProjectAvailableFactorSupply D cursor state := by
  unfold fiveProjectDynamicFactorClearing at hclear
  rcases Option.bind_eq_some_iff.mp hclear with ⟨quote, _, hmarket⟩
  exact fiveProjectClearFactorMarketAtState_projects_le_supply
    cursor.actualAdvances quote (fiveProjectAvailableFactorSupply D cursor state)
    state price projects hmarket

/-- Supplier-first seller selection for an already assigned factor purchase.
Household inventory participates only up to its stated remaining offer. -/
def fiveProjectCurrentFactorSeller? (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (project : Fin 5) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  let quantity := min
    (state.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood)
    (state.stock 6 fiveProjectMoneyGood)
  if 0 < quantity then fiveProjectCustomerPurchaseInstruction project quantity
  else fiveProjectPassiveInstruction

/-- Extract at most one event from a named phase, selected profile, and
pre-transition physical state. Transfer events carry matching evidence. -/
def fiveProjectTransitionEvent? (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    Option FiveProjectPhysicalEvent :=
  let profile := step.profile.1
  match cursor.remainingPhases with
  | .chooseHouseholdPlan :: _ =>
      match haction : profile fiveProjectHousehold with
      | .operate (.chooseHouseholdPlan plan) =>
          some (.householdPlanSelected profile plan haction)
      | _ => none
  | .householdConsumption :: _ =>
      match haction : profile fiveProjectHousehold with
      | .operate (.consumeHouseholdFactors quantity) =>
          some (.householdConsumptionDelivered profile quantity haction)
      | _ => none
  | .noteIssuance :: _ =>
      if h : profile fiveProjectBank =
          .operate (.issueFiduciaryNotes D.fiduciaryNotesIssued) then
        some (.notesIssued profile D.fiduciaryNotesIssued h)
      else none
  | .householdCashTransfer :: _ =>
      if cursor.householdPlan.map FiveProjectHouseholdPlan.deposit =
          some fiveProjectHouseholdDepositTerms.principal then
        match fiveProjectMatchedTransfer? state step
            fiveProjectHouseholdDepositTerms.holder
            fiveProjectHouseholdDepositTerms.issuer
            fiveProjectHouseholdDepositTerms.principal
            fiveProjectHouseholdDepositTerms.moneyGood
            fiveProjectHouseholdDepositTerms.claimQuantity
            fiveProjectHouseholdDepositTerms.claimGood with
        | none => none
        | some transfer => some (.depositOpened fiveProjectHouseholdDepositTerms transfer)
      else none
  | .loanClearing :: _ => none
  | .loanAcceptance project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => none
      | some bid =>
        match cursor.loanQuote with
        | none => none
        | some repayment =>
          match fiveProjectMatchedTransfer? state step fiveProjectBank
              (fiveProjectPhysicalBorrower bid.borrower)
              fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
              (fiveProjectCollateralGood bid.borrower) with
          | none => none
          | some transfer =>
              some (.advanceMatched bid (fiveProjectPawnAgreement bid repayment)
                transfer credit_advance_opens_obligation)
  | .earlyInputPurchase project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => none
      | some bid =>
          if cursor.actualAdvances.contains bid then
            match fiveProjectMatchedTransfer? state step fiveProjectFactorSupplier
                (fiveProjectPhysicalBorrower bid.borrower) 1
                fiveProjectEarlyInputGood 1 fiveProjectMoneyGood with
            | none => none
            | some transfer => some (.earlyInputPurchased bid transfer)
          else none
  | .capitalConversion project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => none
      | some bid =>
          if cursor.actualEarlyInputPurchases.contains bid then
            if h : profile (fiveProjectPhysicalBorrower bid.borrower) =
                .operate (.convertEarlyInputToCapital bid.borrower) then
              some (.capitalFormed profile bid h)
            else none
          else none
  | .factorClearing :: _ => none
  | .factorPurchase slot :: _ =>
      match cursor.factorClearing with
      | none => none
      | some (price, projects) =>
          match projects[slot.val]?, fiveProjectCurrentFactorSeller? cursor state with
          | some bid, some seller =>
              match fiveProjectMatchedTransfer? state step seller
                  (fiveProjectPhysicalBorrower bid.borrower) 1
                  fiveProjectCompletionGood price fiveProjectMoneyGood with
              | none => none
              | some transfer => some (.factorPurchaseMatched bid seller transfer)
          | _, _ => none
  | .completion project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => none
      | some bid =>
          if cursor.actualFactorPurchases.contains bid then
            match haction : profile (fiveProjectPhysicalBorrower bid.borrower) with
            | .operate (.completeProject borrower) =>
                if hborrower : borrower = bid.borrower then
                  some (.projectCompleted profile bid (by
                    simpa [hborrower] using haction))
                else none
            | _ => none
          else none
  | .customerSale project :: _ =>
      let quantity := min
        (state.stock (fiveProjectPhysicalBorrower project) fiveProjectOutputGood)
        (state.stock 6 fiveProjectMoneyGood)
      if 0 < quantity then
        match fiveProjectMatchedTransfer? state step
            (fiveProjectPhysicalBorrower project) 6 quantity
            fiveProjectOutputGood quantity fiveProjectMoneyGood with
        | none => none
        | some transfer => some (.customerOutputSold project quantity transfer)
      else none
  | .loanSettlement project :: _ =>
      match cursor.loanQuote, cursor.plannedAdvances[project.val]? with
      | some repayment, some bid =>
          if cursor.actualAdvances.contains bid then
            match fiveProjectMatchedTransfer? state step
                (fiveProjectPhysicalBorrower bid.borrower) fiveProjectBank repayment
                fiveProjectMoneyGood 1 (fiveProjectCollateralGood bid.borrower) with
            | none => none
            | some transfer =>
                some (.loanRepaid bid transfer credit_repayment_discharges_obligation)
          else none
      | _, _ => none
  | .loanMaturitySettlement project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | some bid =>
        match hfound : cursor.pawnAgreement? bid with
        | none => none
        | some agreement =>
          if cursor.actualAdvances.contains bid &&
              !cursor.actualRepayments.contains bid then
            let collateral := agreement.collateral
            if h : state.stock fiveProjectBank collateral = 1 then
              have hbid := cursor.pawnAgreement?_bid bid agreement hfound
              have hcollateral : agreement.collateral =
                  fiveProjectCollateralGood bid.borrower := by
                rw [agreement.collateral_is_pledged_good, hbid]
              have hpledged : state.stock fiveProjectBank
                  (fiveProjectCollateralGood bid.borrower) = 1 := by
                rw [← hcollateral]
                exact h
              some (.contractualDefaultSettled bid agreement state profile hpledged
                  credit_unpaid_maturity_defaults)
            else none
          else none
      | none => none
  | .depositSettlement :: _ =>
      match cursor.actualDepositContract with
      | none => none
      | some terms =>
          if terms.redemptionPhase = .depositSettlement then
            match fiveProjectMatchedTransfer? state step terms.holder terms.issuer
                terms.claimQuantity terms.claimGood terms.promisedRepayment
                terms.moneyGood with
            | none => none
            | some transfer => some (.depositRedeemed terms transfer)
          else none
  | [] => none

/-- Convert the option-valued single-event extractor to the existing event-list
interface at the cursor trace boundary. -/
def fiveProjectTransitionEvents (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    List FiveProjectPhysicalEvent :=
  (fiveProjectTransitionEvent? D cursor state step).toList

/-- One named phase records at most one physical event. In particular, a
single completion phase cannot append a batch of project completions. -/
theorem fiveProjectTransitionEvents_length_le_one (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectTransitionEvents D cursor state step).length ≤ 1 := by
  exact Option.length_toList_le

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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (bid : LoanReservationBid)
    (hOffer : (fiveProjectAdvanceInstruction bid).affordableProfile
        fiveProjectPhysicalOperations state fiveProjectBank =
      .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
          fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
          (fiveProjectCollateralGood bid.borrower)) :
    let instruction := fiveProjectAdvanceInstruction bid
    let stage := instruction.stage fiveProjectPhysicalOperations state
    ∃ profile : stage.choices.Profile,
      profile.1 fiveProjectBank =
        .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
          fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
          (fiveProjectCollateralGood bid.borrower) ∧
      profile.1 (fiveProjectPhysicalBorrower bid.borrower) = .idle ∧
      (∀ peer, peer ≠ fiveProjectBank →
        peer ≠ fiveProjectPhysicalBorrower bid.borrower →
        profile.1 peer = instruction.profile peer) ∧
      fiveProjectTransitionEvents D
        { remainingPhases := [.loanAcceptance 0], plannedAdvances := [bid] }
        state ⟨instruction, profile⟩ = [] := by
  let instruction := fiveProjectAdvanceInstruction bid
  let stage := instruction.stage fiveProjectPhysicalOperations state
  let offer : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
      fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
      (fiveProjectCollateralGood bid.borrower)
  have hmenu : offer ∈ stage.choices.menu fiveProjectBank := by
    change (EconomyAction.offer fiveProjectBank
        (fiveProjectPhysicalBorrower bid.borrower)
        fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
        (fiveProjectCollateralGood bid.borrower)) ∈
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
  · simp [fiveProjectTransitionEvents, fiveProjectTransitionEvent?]

/-- Generate a branch's next proposal from its cursor and current inventory.
Clearing results already stored in the cursor remain fixed; later transfer
quantities and seller availability are read from the actual state. -/
def fiveProjectPhysicalInstruction (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    PhysicalProfileInstruction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
  match cursor.remainingPhases with
  | .chooseHouseholdPlan :: _ => fiveProjectHouseholdPlanInstruction D
  | .noteIssuance :: _ => fiveProjectIssueNotesInstruction D
  | .householdCashTransfer :: _ =>
      fiveProjectHouseholdCashTransferInstruction? cursor.householdPlan
  | .loanClearing :: _ => fiveProjectPassiveInstruction
  | .loanAcceptance project :: _ =>
      (cursor.plannedAdvances[project.val]?).elim
        fiveProjectPassiveInstruction fiveProjectAdvanceInstruction
  | .earlyInputPurchase project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => fiveProjectPassiveInstruction
      | some bid =>
          if cursor.actualAdvances.contains bid then
            fiveProjectEarlyInputPurchaseInstruction bid
          else fiveProjectPassiveInstruction
  | .capitalConversion project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => fiveProjectPassiveInstruction
      | some bid =>
          if cursor.actualEarlyInputPurchases.contains bid then
            fiveProjectCapitalConversionInstruction bid
          else fiveProjectPassiveInstruction
  | .householdConsumption :: _ =>
      fiveProjectPlannedHouseholdConsumptionInstruction cursor.householdPlan
  | .factorClearing :: _ => fiveProjectPassiveInstruction
  | .factorPurchase slot :: _ =>
      match cursor.factorClearing with
      | none => fiveProjectPassiveInstruction
      | some (price, projects) =>
          (projects[slot.val]?).elim fiveProjectPassiveInstruction fun bid =>
            fiveProjectDynamicFactorPurchaseInstruction cursor state bid.borrower price
  | .completion project :: _ =>
      match cursor.plannedAdvances[project.val]? with
      | none => fiveProjectPassiveInstruction
      | some bid =>
          if cursor.actualFactorPurchases.contains bid then
            fiveProjectCompletionInstruction [bid]
          else fiveProjectPassiveInstruction
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
  | .loanMaturitySettlement _ :: _ => fiveProjectPassiveInstruction
  | .depositSettlement :: _ =>
      cursor.actualDepositContract.elim fiveProjectPassiveInstruction fun terms =>
        if terms.redemptionPhase = .depositSettlement then
          fiveProjectDepositRedemptionInstruction terms
        else fiveProjectPassiveInstruction
  | [] => fiveProjectPassiveInstruction

/-- A factor-purchase profile can refuse unilaterally: the purchaser idles
while the currently selected seller keeps its scheduled offer. Peer actions
are preserved exactly, and the unmatched offer creates no purchase event.
The premises identify an actual assigned purchase instruction and its
scheduled matched offer/acceptance; they add no supply, credit, or preference
assumptions. -/
theorem fiveProject_unilateral_factor_purchase_refusal
    (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (slot : Fin 5) (bid : LoanReservationBid)
    (price : ℕ) (projects : List LoanReservationBid)
    (seller : FiveProjectPhysicalAgent)
    (hphase : cursor.remainingPhases.head? = some (.factorPurchase slot))
    (hclearing : cursor.factorClearing = some (price, projects))
    (hbid : projects[slot.val]? = some bid)
    (hseller : fiveProjectCurrentFactorSeller? cursor state = some seller)
    (hoff : ((fiveProjectDynamicFactorPurchaseInstruction cursor state
        bid.borrower price).selectedProfile fiveProjectPhysicalOperations state).1 seller =
      .offer seller (fiveProjectPhysicalBorrower bid.borrower) 1
        fiveProjectCompletionGood price fiveProjectMoneyGood) :
    let instruction := fiveProjectDynamicFactorPurchaseInstruction cursor state
      bid.borrower price
    let stage := instruction.stage fiveProjectPhysicalOperations state
    ∃ profile : stage.choices.Profile,
      profile.1 seller = .offer seller (fiveProjectPhysicalBorrower bid.borrower) 1
        fiveProjectCompletionGood price fiveProjectMoneyGood ∧
      profile.1 (fiveProjectPhysicalBorrower bid.borrower) = .idle ∧
      (∀ peer, peer ≠ seller → peer ≠ fiveProjectPhysicalBorrower bid.borrower →
        profile.1 peer =
          (instruction.selectedProfile fiveProjectPhysicalOperations state).1 peer) ∧
      fiveProjectTransitionEvents D cursor state ⟨instruction, profile⟩ = [] := by
  classical
  let instruction := fiveProjectDynamicFactorPurchaseInstruction cursor state
    bid.borrower price
  let stage := instruction.stage fiveProjectPhysicalOperations state
  let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
  let buyer := fiveProjectPhysicalBorrower bid.borrower
  let refusalAction : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation := .idle
  have hbuyer_ne_seller : buyer ≠ seller := by
    by_cases hstock : 0 < state.stock fiveProjectFactorSupplier
        fiveProjectCompletionGood
    · change (if 0 < state.stock fiveProjectFactorSupplier fiveProjectCompletionGood then
          some fiveProjectFactorSupplier else
          if 0 < min cursor.householdOfferRemaining
              (state.stock fiveProjectHousehold fiveProjectCompletionGood) then
            some fiveProjectHousehold else none) = some seller at hseller
      rw [ite_eq_left hstock] at hseller
      have hs : seller = fiveProjectFactorSupplier :=
        (Option.some.inj hseller).symm
      subst seller
      exact (fiveProjectFactorSeller_ne_borrower bid.borrower).1.symm
    · change (if 0 < state.stock fiveProjectFactorSupplier fiveProjectCompletionGood then
          some fiveProjectFactorSupplier else
          if 0 < min cursor.householdOfferRemaining
              (state.stock fiveProjectHousehold fiveProjectCompletionGood) then
            some fiveProjectHousehold else none) = some seller at hseller
      rw [ite_eq_right hstock] at hseller
      by_cases hhousehold : 0 < min cursor.householdOfferRemaining
          (state.stock fiveProjectHousehold fiveProjectCompletionGood)
      · rw [ite_eq_left hhousehold] at hseller
        have hs : seller = fiveProjectHousehold :=
          (Option.some.inj hseller).symm
        subst seller
        exact (fiveProjectFactorSeller_ne_borrower bid.borrower).2.symm
      · rw [ite_eq_right hhousehold] at hseller
        cases hseller
  let hprofile := stage.choices.replaceProfile scheduled buyer refusalAction
    (stage.choices.idle_mem buyer)
  refine ⟨hprofile, ?_, ?_, ?_, ?_⟩
  · have hkeep := stage.choices.replaceProfile_other scheduled
      (i := buyer) (j := seller) refusalAction (stage.choices.idle_mem buyer)
      (Ne.symm hbuyer_ne_seller)
    simpa [hprofile, instruction, scheduled, buyer] using hkeep.trans hoff
  · simp [hprofile, buyer, refusalAction]
  · intro peer hpeerSeller hpeerBuyer
    by_cases hpeer : peer = buyer
    · subst peer
      exact (hpeerBuyer rfl).elim
    · simpa [hprofile, buyer, refusalAction] using
        stage.choices.replaceProfile_other scheduled
          (i := buyer) (j := peer) refusalAction (stage.choices.idle_mem buyer) hpeer
  · cases hremaining : cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
      have htarget : phase = .factorPurchase slot := by
        simpa [hremaining] using hphase
      subst phase
      simp [fiveProjectTransitionEvents, fiveProjectTransitionEvent?,
        hremaining, hclearing, hbid, hseller, fiveProjectMatchedTransfer?, hprofile,
        buyer, refusalAction, FiniteChoiceStage.replaceProfile, Function.update]

/-- Advance the finite cursor after interpreting the selected typed profile.
Every position is consumed. Only events extracted from that selected profile
are appended; the compiled program history retains the stage-membership proof
and its interpreter-derived state transition. -/
def fiveProjectNextCursor (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    FiveProjectPhysicalCursor :=
  let state' := (step.instruction.stage fiveProjectPhysicalOperations state).advance step.profile
  let next := { cursor with
    remainingPhases := cursor.remainingPhases.drop 1
    consumedPhases := cursor.consumedPhases ++ cursor.remainingPhases.take 1
    eventTrace := cursor.eventTrace ++ fiveProjectRecordTransitionEvents
      cursor.remainingPhases (fiveProjectTransitionEvents D cursor state step) }
  match cursor.remainingPhases with
  | .chooseHouseholdPlan :: _ =>
      match step.profile.1 fiveProjectHousehold with
      | .operate (.chooseHouseholdPlan plan) =>
          { next with householdPlan := some plan, householdOfferLimit := plan.offeredFactors }
      | _ => { next with householdPlan := none, householdOfferLimit := 0 }
  | .loanClearing :: _ =>
      let clearing := clearLoanMarket fiveProjectLoanMarket
          (state'.stock fiveProjectBank fiveProjectMoneyGood)
      let nextWithQuote := { next with loanQuote := clearing.quotedRepayment }
      { nextWithQuote with plannedAdvances := clearing.funded }
  | .factorClearing :: _ =>
      { next with factorClearing := fiveProjectDynamicFactorClearing D cursor state' }
  | _ => next

/-- Every interpreted step consumes exactly its current phase, including a
refused or unmatched proposal. The schedule therefore cannot retry a failed
transaction by regenerating the same instruction. -/
theorem fiveProjectNextCursor_consumes_one_phase (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectNextCursor D cursor state step).remainingPhases =
      cursor.remainingPhases.drop 1 := by
  cases hphase : cursor.remainingPhases with
  | nil => simp [fiveProjectNextCursor, hphase]
  | cons phase rest =>
      cases phase <;> simp [fiveProjectNextCursor, hphase]
      all_goals split <;> rfl

/-- Every cursor transition preserves the decomposition of the named
schedule into its consumed prefix and remaining suffix. -/
theorem fiveProjectNextCursor_consumedPhases (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectNextCursor D cursor state step).consumedPhases =
      cursor.consumedPhases ++ cursor.remainingPhases.take 1 := by
  cases hphase : cursor.remainingPhases with
  | nil => simp [fiveProjectNextCursor, hphase]
  | cons phase rest =>
      cases phase <;> simp [fiveProjectNextCursor, hphase]
      all_goals split <;> rfl

theorem fiveProjectNextCursor_remainingPhases (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectNextCursor D cursor state step).remainingPhases =
      cursor.remainingPhases.drop 1 :=
  fiveProjectNextCursor_consumes_one_phase D cursor state step

theorem fiveProjectNextCursor_preserves_schedule (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state)
    (hcursor : cursor.preservesSchedule) :
    (fiveProjectNextCursor D cursor state step).preservesSchedule := by
  change (fiveProjectNextCursor D cursor state step).consumedPhases ++
      (fiveProjectNextCursor D cursor state step).remainingPhases =
    fiveProjectPhysicalPhases
  rw [fiveProjectNextCursor_consumedPhases,
    fiveProjectNextCursor_consumes_one_phase]
  unfold FiveProjectPhysicalCursor.preservesSchedule at hcursor
  cases hphase : cursor.remainingPhases with
  | nil => simpa [hphase] using hcursor
  | cons phase rest => simpa [hphase, List.take] using hcursor

/-- The event trace stores exactly the events extracted at this transition,
tagged with the transition's consumed named phase. -/
theorem fiveProjectNextCursor_event_trace_append (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectNextCursor D cursor state step).eventTrace =
      cursor.eventTrace ++ fiveProjectRecordTransitionEvents cursor.remainingPhases
        (fiveProjectTransitionEvents D cursor state step) := by
  cases hphase : cursor.remainingPhases with
  | nil => simp [fiveProjectNextCursor, hphase]
  | cons phase rest =>
      cases phase <;> simp [fiveProjectNextCursor, hphase,
        fiveProjectRecordTransitionEvents]
      all_goals split <;> rfl

/-- Event views are append-only projections of the trace. The event list
appended at a step is exactly the list extracted from that step's typed
profile, whose transfer events include matching offer/acceptance proofs. -/
theorem fiveProjectNextCursor_events_append (D : FiveProjectRegimeData)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state) :
    (fiveProjectNextCursor D cursor state step).events =
      cursor.events ++ fiveProjectTransitionEvents D cursor state step := by
  change List.map FiveProjectPhysicalEventRecord.event
      (fiveProjectNextCursor D cursor state step).eventTrace = _
  rw [fiveProjectNextCursor_event_trace_append]
  simp only [FiveProjectPhysicalCursor.events, List.map_append]
  change cursor.events ++
      List.map FiveProjectPhysicalEventRecord.event
        (fiveProjectRecordTransitionEvents cursor.remainingPhases
          (fiveProjectTransitionEvents D cursor state step)) =
    cursor.events ++ fiveProjectTransitionEvents D cursor state step
  apply congrArg (fun events => cursor.events ++ events)
  cases hphase : cursor.remainingPhases with
  | nil => simp [fiveProjectRecordTransitionEvents, fiveProjectTransitionEvents,
      fiveProjectTransitionEvent?, hphase]
  | cons phase rest =>
      simp only [fiveProjectRecordTransitionEvents, List.map_map]
      change List.map (fun event : FiveProjectPhysicalEvent =>
        (⟨phase, event⟩ : FiveProjectPhysicalEventRecord).event)
        (fiveProjectTransitionEvents D cursor state step) = _
      have hmap (events : List FiveProjectPhysicalEvent) :
          List.map (fun event : FiveProjectPhysicalEvent =>
            (⟨phase, event⟩ : FiveProjectPhysicalEventRecord).event) events = events := by
        induction events with
        | nil => rfl
        | cons event rest ih => simp [ih]
      exact hmap _

/-- Event-phase provenance is preserved across every interpreted transition.
Refused and unmatched stages consume their phase but append no event. -/
theorem fiveProjectNextCursor_preserves_trace_phase_sublist
    (D : FiveProjectRegimeData) (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state)
    (hcursor : cursor.tracePhaseSublist) :
    (fiveProjectNextCursor D cursor state step).tracePhaseSublist := by
  unfold FiveProjectPhysicalCursor.tracePhaseSublist at hcursor ⊢
  rw [fiveProjectNextCursor_event_trace_append, List.map_append,
    fiveProjectNextCursor_consumedPhases]
  cases hphase : cursor.remainingPhases with
  | nil =>
      simpa [fiveProjectRecordTransitionEvents, fiveProjectTransitionEvents,
        fiveProjectTransitionEvent?] using hcursor
  | cons phase rest =>
      apply List.Sublist.append hcursor
      exact fiveProjectRecordTransitionEvents_phases_sublist phase rest
        (fiveProjectTransitionEvents D cursor state step)
        (fiveProjectTransitionEvents_length_le_one D cursor state step)

/-- A transition from a cursor satisfying the schedule and trace invariants
cannot record the same physical phase twice. The result follows from the
phase partition and one-event-per-phase evidence, not a conclusion assumed on
the cursor. -/
theorem fiveProjectNextCursor_event_phases_nodup
    (D : FiveProjectRegimeData) (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state)
    (hschedule : cursor.preservesSchedule)
    (htrace : cursor.tracePhaseSublist) :
    ((fiveProjectNextCursor D cursor state step).eventTrace.map
      FiveProjectPhysicalEventRecord.phase).Nodup := by
  have hschedule' := fiveProjectNextCursor_preserves_schedule
    D cursor state step hschedule
  have htrace' := fiveProjectNextCursor_preserves_trace_phase_sublist
    D cursor state step htrace
  exact List.Nodup.sublist htrace'
    ((fiveProjectNextCursor D cursor state step).consumedPhases_nodup hschedule')

def fiveProjectPhysicalRegimeGenerator (D : FiveProjectRegimeData) :
    PhysicalProfileGenerator FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Nat FiveProjectPhysicalCursor
      fiveProjectPhysicalOperations where
  instruction := fiveProjectPhysicalInstruction D
  nextCursor := fiveProjectNextCursor D

/-- One concrete history prefix for regression witnesses. `true` selects the
instruction generator's affordable scheduled profile; `false` selects the
stage's all-idle profile. Each transition uses the same stage interpreter and
cursor update as the compiled program. -/
structure FiveProjectPhysicalRun where
  cursor : FiveProjectPhysicalCursor
  state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat

/-- The household's checked terminal bundle for plan comparison retains three
separate features: terminal money, services actually recorded on the trace,
and total physical holdings. The deposit liability is reported separately in
the cursor's contract events. -/
structure FiveProjectHouseholdOutcome where
  terminalMoney : Nat
  deliveredServices : Nat
  totalPhysicalHoldings : Nat
  deriving DecidableEq, Repr

/-- The fixed ordinal comparison used for the household illustration: first
whether terminal money reaches the five-unit reserve threshold, then delivered
consumption services, terminal money, and finally total physical holdings. -/
def fiveProjectHouseholdPreferenceRank
    (outcome : FiveProjectHouseholdOutcome) : ℕ × ℕ × ℕ × ℕ :=
  (if 5 ≤ outcome.terminalMoney then 1 else 0,
    outcome.deliveredServices, outcome.terminalMoney,
    outcome.totalPhysicalHoldings)

/-- Strict lexicographic household preference on computed outcomes. It is an
explicit preference input for this finite illustration; it does not assert
that the scheduled household plan is purposeful until the menu comparison is
proved below. -/
def fiveProjectHouseholdPrefers
    (preferred other : FiveProjectHouseholdOutcome) : Prop :=
  let left := fiveProjectHouseholdPreferenceRank preferred
  let right := fiveProjectHouseholdPreferenceRank other
  left.1 > right.1 ∨
    (left.1 = right.1 ∧
      (left.2.1 > right.2.1 ∨
        (left.2.1 = right.2.1 ∧
          (left.2.2.1 > right.2.2.1 ∨
            (left.2.2.1 = right.2.2.1 ∧
              left.2.2.2 > right.2.2.2)))))

theorem fiveProjectHouseholdPrefers_irrefl
    (outcome : FiveProjectHouseholdOutcome) :
    ¬ fiveProjectHouseholdPrefers outcome outcome := by
  simp only [fiveProjectHouseholdPrefers]
  omega

theorem fiveProjectHouseholdPrefers_asymmetric
    (preferred other : FiveProjectHouseholdOutcome)
    (h : fiveProjectHouseholdPrefers preferred other) :
    ¬ fiveProjectHouseholdPrefers other preferred := by
  simp only [fiveProjectHouseholdPrefers] at h ⊢
  omega

def FiveProjectPhysicalRun.householdOutcome
    (run : FiveProjectPhysicalRun) : FiveProjectHouseholdOutcome :=
  { terminalMoney := run.state.stock fiveProjectHousehold fiveProjectMoneyGood
    deliveredServices := run.state.services fiveProjectHousehold
      fiveProjectConsumptionService
    totalPhysicalHoldings := Finset.univ.sum fun good =>
      run.state.stock fiveProjectHousehold good }

def fiveProjectInitialRun (D : FiveProjectRegimeData) : FiveProjectPhysicalRun :=
  { cursor := fiveProjectInitialCursor D
    state := fiveProjectFactorInitialState D }

/-- Initial run for a comparative resource case with an explicitly supplied
entrepreneur cash-buffer vector. All non-cash stocks remain those in the
scenario's named initial state. -/
def fiveProjectInitialRunWithCashBuffers (D : FiveProjectRegimeData)
    (cashBuffer : Fin 5 → ℕ) : FiveProjectPhysicalRun :=
  { cursor := fiveProjectInitialCursor D
    state := fiveProjectFactorInitialStateWithCashBuffers D cashBuffer }

def fiveProjectRunStep (D : FiveProjectRegimeData) (enactScheduled : Bool)
    (run : FiveProjectPhysicalRun) : FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let profile : stage.choices.Profile :=
    if enactScheduled then instruction.selectedProfile fiveProjectPhysicalOperations run.state
    else FiniteEconomyProgram.ProgramHistory.idleProfile stage.choices
  let state' := stage.advance profile
  exact { cursor := fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩
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
  exact { cursor := fiveProjectNextCursor D run.cursor run.state ⟨instruction, profile⟩
          state := state' }

/-- Reachability follows the actual state-dependent instruction generator.
Each transition consumes one generated stage profile and uses the same
interpreter and cursor update as the direct runner and compiled program. -/
inductive FiveProjectPhysicalExecutionReachable (D : FiveProjectRegimeData) :
    FiveProjectPhysicalCursor →
      PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat → Prop where
  | initial : FiveProjectPhysicalExecutionReachable D
      (fiveProjectInitialCursor D) (fiveProjectFactorInitialState D)
  | initialWithCashBuffers (cashBuffer : Fin 5 → ℕ) :
      FiveProjectPhysicalExecutionReachable D (fiveProjectInitialCursor D)
        (fiveProjectFactorInitialStateWithCashBuffers D cashBuffer)
  | advance {cursor : FiveProjectPhysicalCursor}
      {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
      (reachable : FiveProjectPhysicalExecutionReachable D cursor state)
      (profile : ((fiveProjectPhysicalInstruction D cursor state).stage
        fiveProjectPhysicalOperations state).choices.Profile) :
      FiveProjectPhysicalExecutionReachable D
        (fiveProjectNextCursor D cursor state
          ⟨fiveProjectPhysicalInstruction D cursor state, profile⟩)
        (((fiveProjectPhysicalInstruction D cursor state).stage
          fiveProjectPhysicalOperations state).advance profile)

/-- Every reachable physical cursor retains the original schedule partition
and its recorded events are phase-tagged within the consumed prefix. -/
theorem FiveProjectPhysicalExecutionReachable.cursor_invariants
    {D : FiveProjectRegimeData} {cursor : FiveProjectPhysicalCursor}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (reachable : FiveProjectPhysicalExecutionReachable D cursor state) :
    cursor.preservesSchedule ∧ cursor.tracePhaseSublist := by
  induction reachable with
  | initial =>
      exact ⟨fiveProjectInitialCursor_preserves_schedule _,
        fiveProjectInitialCursor_tracePhaseSublist _⟩
  | initialWithCashBuffers cashBuffer =>
      exact ⟨fiveProjectInitialCursor_preserves_schedule _,
        fiveProjectInitialCursor_tracePhaseSublist _⟩
  | advance reachable profile ih =>
      exact ⟨fiveProjectNextCursor_preserves_schedule _ _ _ _ ih.1,
        fiveProjectNextCursor_preserves_trace_phase_sublist _ _ _ _ ih.2⟩

/-- A reachable run's trace has no repeated phase. The schedule is `Nodup`,
each transition consumes one position, and each position emits at most one
event. -/
theorem FiveProjectPhysicalExecutionReachable.event_phases_nodup
    {D : FiveProjectRegimeData} {cursor : FiveProjectPhysicalCursor}
    {state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat}
    (reachable : FiveProjectPhysicalExecutionReachable D cursor state) :
    (cursor.eventTrace.map FiveProjectPhysicalEventRecord.phase).Nodup := by
  obtain ⟨hschedule, htrace⟩ := reachable.cursor_invariants
  exact List.Nodup.sublist htrace (cursor.consumedPhases_nodup hschedule)

/-- Selecting any generated menu profile preserves the physical trace
invariants, so unilateral refusals remain within the checked execution model. -/
theorem fiveProjectRunStepWithProfile_preserves_reachability
    (D : FiveProjectRegimeData) (run : FiveProjectPhysicalRun)
    (reachable : FiveProjectPhysicalExecutionReachable D run.cursor run.state)
    (profile : ((fiveProjectPhysicalInstruction D run.cursor run.state).stage
      fiveProjectPhysicalOperations run.state).choices.Profile) :
    FiveProjectPhysicalExecutionReachable D
      (fiveProjectRunStepWithProfile D run profile).cursor
      (fiveProjectRunStepWithProfile D run profile).state := by
  exact .advance reachable profile

/-- Replay a selected household plan at the initial choice stage while all
other actors retain their stage-selected actions. Subsequent execution uses
the plan recorded by the cursor. -/
def fiveProjectRunSelectedHouseholdPlan (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun) (plan : FiveProjectHouseholdPlan)
    (hphase : run.cursor.remainingPhases.head? = some .chooseHouseholdPlan)
    (hchoice : plan ∈ fiveProjectHouseholdPlanChoices D) :
    FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  have hinstruction : instruction = fiveProjectHouseholdPlanInstruction D := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
      cases phase <;> simp_all [instruction, fiveProjectPhysicalInstruction]
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let choose : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .operate (.chooseHouseholdPlan plan)
  have halternative : choose ∈ instruction.affordableAlternatives
      fiveProjectPhysicalOperations run.state fiveProjectHousehold := by
    rw [hinstruction]
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨plan, hchoice, rfl⟩
    · intro good
      simp [rawActionUse, choose, fiveProjectPhysicalOperations]
  have hmenu : choose ∈ stage.choices.menu fiveProjectHousehold := by
    change choose ∈ instruction.stageMenu fiveProjectPhysicalOperations run.state
      fiveProjectHousehold
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem halternative)
  let profile : stage.choices.Profile :=
    stage.choices.replaceProfile
      (instruction.selectedProfile fiveProjectPhysicalOperations run.state)
      fiveProjectHousehold choose hmenu
  exact fiveProjectRunStepWithProfile D run profile

def fiveProjectRunChoices (D : FiveProjectRegimeData) :
    List Bool → FiveProjectPhysicalRun → FiveProjectPhysicalRun
  | [], run => run
  | enact :: rest, run =>
      fiveProjectRunChoices D rest (fiveProjectRunStep D enact run)

/-- Execute selected profiles until the named phase reaches the cursor head.
The fuel is derived from the remaining phase list, so inserting a named stage
does not silently retarget a regression run. -/
def fiveProjectRunUntilPhaseFuel (D : FiveProjectRegimeData)
    (target : FiveProjectPhysicalPhase) :
    ℕ → FiveProjectPhysicalRun → FiveProjectPhysicalRun
  | 0, run => run
  | fuel + 1, run =>
      match run.cursor.remainingPhases with
      | [] => run
      | phase :: _ =>
          if phase = target then run
          else fiveProjectRunUntilPhaseFuel D target fuel
            (fiveProjectRunStep D true run)

def fiveProjectRunUntilPhase (D : FiveProjectRegimeData)
    (target : FiveProjectPhysicalPhase) (run : FiveProjectPhysicalRun) :
    FiveProjectPhysicalRun :=
  fiveProjectRunUntilPhaseFuel D target run.cursor.remainingPhases.length run

/-- Profile choices for the named physical generator. -/
abbrev FiveProjectPhysicalProfileSelector (D : FiveProjectRegimeData) :=
  ∀ (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat),
    ((fiveProjectPhysicalInstruction D cursor state).stage
      fiveProjectPhysicalOperations state).choices.Profile

/-- Run a finite number of generated physical stages using an explicit
state-dependent profile selector. -/
def fiveProjectRunUsingProfileSelector (D : FiveProjectRegimeData)
    (selectProfile : FiveProjectPhysicalProfileSelector D) :
    ℕ → FiveProjectPhysicalRun → FiveProjectPhysicalRun
  | 0, run => run
  | fuel + 1, run =>
      let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
      let stage := instruction.stage fiveProjectPhysicalOperations run.state
      let profile := selectProfile run.cursor run.state
      fiveProjectRunUsingProfileSelector D selectProfile fuel
        { cursor := fiveProjectNextCursor D run.cursor run.state
            ⟨instruction, profile⟩
          state := stage.advance profile }

/-- At one named phase, choose idle for one actor while keeping the selected
profile of every peer. All later stages continue from the actual state and the
cursor updated by that unilateral profile. -/
def fiveProjectProfileSelectorWithUnilateralIdle (D : FiveProjectRegimeData)
    (targetPhase : FiveProjectPhysicalPhase) (actor : FiveProjectPhysicalAgent) :
    FiveProjectPhysicalProfileSelector D :=
  fun cursor state =>
    let instruction := fiveProjectPhysicalInstruction D cursor state
    let stage := instruction.stage fiveProjectPhysicalOperations state
    let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
    if cursor.remainingPhases.head? = some targetPhase then
      stage.choices.replaceProfile scheduled actor EconomyAction.idle
        (stage.choices.idle_mem actor)
    else scheduled

/-- The cautious post-publication path keeps the assigned quote and every
scheduled peer action, while projects two and three choose idling at their
acceptance nodes. Later stages still read the cursor and state produced by
those choices. -/
def fiveProjectCautiousAcceptanceSelector (D : FiveProjectRegimeData) :
    FiveProjectPhysicalProfileSelector D :=
  fun cursor state =>
    let instruction := fiveProjectPhysicalInstruction D cursor state
    let stage := instruction.stage fiveProjectPhysicalOperations state
    let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
    let afterProjectTwo :=
      if cursor.remainingPhases.head? = some (.loanAcceptance 2) then
        stage.choices.replaceProfile scheduled (fiveProjectPhysicalBorrower 2)
          EconomyAction.idle (stage.choices.idle_mem (fiveProjectPhysicalBorrower 2))
      else scheduled
    if cursor.remainingPhases.head? = some (.loanAcceptance 3) then
      stage.choices.replaceProfile afterProjectTwo (fiveProjectPhysicalBorrower 3)
        EconomyAction.idle (stage.choices.idle_mem (fiveProjectPhysicalBorrower 3))
    else afterProjectTwo

/-- Unilateral entry into a cautious path restores one marginal borrower's
published acceptance while preserving the other marginal borrower's refusal
and every peer's scheduled action. -/
def fiveProjectCautiousEntrySelector (D : FiveProjectRegimeData)
    (entrant : Fin 5) : FiveProjectPhysicalProfileSelector D :=
  fun cursor state =>
    let instruction := fiveProjectPhysicalInstruction D cursor state
    let stage := instruction.stage fiveProjectPhysicalOperations state
    let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
    let cautious := fiveProjectCautiousAcceptanceSelector D cursor state
    if cursor.remainingPhases.head? = some (.loanAcceptance entrant) then
      stage.choices.replaceProfile cautious
        (fiveProjectPhysicalBorrower entrant)
        (scheduled.1 (fiveProjectPhysicalBorrower entrant))
        (scheduled.2 (fiveProjectPhysicalBorrower entrant))
    else cautious

/-- A unilateral idle selector changes exactly the selected actor at its
named phase; every peer retains its scheduled action. -/
theorem fiveProjectProfileSelectorWithUnilateralIdle_actions
    (D : FiveProjectRegimeData) (targetPhase : FiveProjectPhysicalPhase)
    (actor : FiveProjectPhysicalAgent)
    (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (hphase : cursor.remainingPhases.head? = some targetPhase) :
    (fiveProjectProfileSelectorWithUnilateralIdle D targetPhase actor cursor state).1 actor =
        EconomyAction.idle ∧
      ∀ peer, peer ≠ actor →
        (fiveProjectProfileSelectorWithUnilateralIdle D targetPhase actor cursor state).1 peer =
          ((fiveProjectPhysicalInstruction D cursor state).selectedProfile
            fiveProjectPhysicalOperations state).1 peer := by
  let instruction := fiveProjectPhysicalInstruction D cursor state
  let stage := instruction.stage fiveProjectPhysicalOperations state
  let scheduled := instruction.selectedProfile fiveProjectPhysicalOperations state
  refine ⟨?_, ?_⟩
  · simp [fiveProjectProfileSelectorWithUnilateralIdle, hphase,
      FiniteChoiceStage.replaceProfile_self]
  · intro peer hpeer
    simp [fiveProjectProfileSelectorWithUnilateralIdle, hphase,
      FiniteChoiceStage.replaceProfile_other, hpeer]

/-- A direct selected-profile run and its policy-selected compiled history
have the same terminal inventory. -/
theorem fiveProjectRunUsingProfileSelector_matches_compiled_history
    (D : FiveProjectRegimeData)
    (selectProfile : FiveProjectPhysicalProfileSelector D)
    (fuel : ℕ) (run : FiveProjectPhysicalRun) :
    (fiveProjectRunUsingProfileSelector D selectProfile fuel run).state =
      (physicalProfileGeneratorHistoryWithPolicy fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator D) selectProfile fuel
        run.cursor run.state).terminalState := by
  induction fuel generalizing run with
  | zero => rfl
  | succ fuel ih =>
      simp only [fiveProjectRunUsingProfileSelector,
        physicalProfileGeneratorHistoryWithPolicy,
        FiniteEconomyProgram.ProgramHistory.terminalState]
      exact ih _

/-- Compile a named unilateral-idle intervention using the same branch policy
as the direct physical runner. -/
def fiveProjectPhysicalHistoryWithUnilateralIdle (D : FiveProjectRegimeData)
    (targetPhase : FiveProjectPhysicalPhase) (actor : FiveProjectPhysicalAgent)
    (fuel : ℕ) (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat) :
    FinitePhysicalEconomyProgram.History
      (compilePhysicalProfileGenerator fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator D) fuel cursor state) :=
  physicalProfileGeneratorHistoryWithPolicy fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D)
    (fiveProjectProfileSelectorWithUnilateralIdle D targetPhase actor)
    fuel cursor state

/-- The direct run after a unilateral idle intervention and its compiled
history have identical terminal inventories. -/
theorem fiveProjectRunWithUnilateralIdle_matches_compiled_history
    (D : FiveProjectRegimeData) (targetPhase : FiveProjectPhysicalPhase)
    (actor : FiveProjectPhysicalAgent) (fuel : ℕ)
    (run : FiveProjectPhysicalRun) :
    (fiveProjectRunUsingProfileSelector D
      (fiveProjectProfileSelectorWithUnilateralIdle D targetPhase actor) fuel run).state =
    (fiveProjectPhysicalHistoryWithUnilateralIdle D targetPhase actor fuel
      run.cursor run.state).terminalState :=
  fiveProjectRunUsingProfileSelector_matches_compiled_history D
    (fiveProjectProfileSelectorWithUnilateralIdle D targetPhase actor) fuel run

/-- Selected direct execution after a cautious forecast is disclosed between
quote publication and borrower acceptance. The published terms remain fixed;
only marginal acceptance decisions change. -/
def fiveProjectCautiousFiduciaryRun : FiveProjectPhysicalRun :=
  fiveProjectRunUsingProfileSelector
    (fiveProjectRegimeData .fiduciaryExpansion)
    (fiveProjectCautiousAcceptanceSelector
      (fiveProjectRegimeData .fiduciaryExpansion))
    fiveProjectPhysicalFuel
    (fiveProjectInitialRun (fiveProjectRegimeData .fiduciaryExpansion))

/-- A marginal borrower's unilateral entry into the cautious selected path,
holding the already published repayment quote and project three's refusal
fixed. -/
def fiveProjectCautiousProjectTwoEntryRun : FiveProjectPhysicalRun :=
  fiveProjectRunUsingProfileSelector
    (fiveProjectRegimeData .fiduciaryExpansion)
    (fiveProjectCautiousEntrySelector
      (fiveProjectRegimeData .fiduciaryExpansion) 2)
    fiveProjectPhysicalFuel
    (fiveProjectInitialRun (fiveProjectRegimeData .fiduciaryExpansion))

set_option maxRecDepth 4096 in
/-- After disclosure, only the two incumbent advances match. The already
published quote remains four and, with the two incumbents supplying the
entire two-unit factor demand, the actual factor price is one. -/
theorem fiveProject_cautious_selected_path_replays_after_publication :
    fiveProjectCautiousFiduciaryRun.cursor.loanQuote = some 4 ∧
    fiveProjectCautiousFiduciaryRun.cursor.actualAdvances.map
      LoanReservationBid.borrower = [0, 1] ∧
    fiveProjectCautiousFiduciaryRun.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (1, [0, 1]) ∧
    fiveProjectCautiousFiduciaryRun.cursor.actualFactorPurchases.map
      LoanReservationBid.borrower = [0, 1] ∧
    fiveProjectCautiousFiduciaryRun.cursor.actualDefaults = [] := by
  decide

set_option maxRecDepth 4096 in
/-- Replaying project two's unilateral entry at the fixed published quote
raises the recomputed factor price to two. The borrower has one unit of cash
after its early-input purchase, so its factor purchase does not match and the
unpaid-maturity event is generated by the later physical settlement stage. -/
theorem fiveProject_cautious_project_two_entry_replays_price_and_default :
    fiveProjectCautiousProjectTwoEntryRun.cursor.loanQuote = some 4 ∧
    fiveProjectCautiousProjectTwoEntryRun.cursor.actualAdvances.map
      LoanReservationBid.borrower = [0, 1, 2] ∧
    fiveProjectCautiousProjectTwoEntryRun.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (2, [0, 1]) ∧
    fiveProjectCautiousProjectTwoEntryRun.state.stock
      (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood = 1 ∧
    fiveProjectCautiousProjectTwoEntryRun.cursor.actualFactorPurchases.map
      LoanReservationBid.borrower = [0, 1] ∧
    fiveProjectCautiousProjectTwoEntryRun.cursor.actualDefaults.map
      LoanReservationBid.borrower = [2] := by
  decide

/-- Apply an explicitly witnessed unilateral refusal at the borrower's
scheduled loan-acceptance node. The lender keeps its affordable offer; all
other actors retain their stage-selected actions. -/
def fiveProjectRunUnilateralLoanRefusalStep (D : FiveProjectRegimeData)
    (run : FiveProjectPhysicalRun) (bid : LoanReservationBid)
    (hphase : run.cursor.remainingPhases.head? =
      some (.loanAcceptance bid.borrower))
    (hplanned : run.cursor.plannedAdvances[bid.borrower.val]? = some bid)
    (hOffer : (fiveProjectAdvanceInstruction bid).affordableProfile
        fiveProjectPhysicalOperations run.state fiveProjectBank =
      .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
        fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
        (fiveProjectCollateralGood bid.borrower)) :
    FiveProjectPhysicalRun := by
  let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
  have hinstruction : instruction = fiveProjectAdvanceInstruction bid := by
    cases hremaining : run.cursor.remainingPhases with
    | nil => simp [hremaining] at hphase
    | cons phase rest =>
        cases phase <;>
          simp_all [instruction, fiveProjectPhysicalInstruction]
  let stage := instruction.stage fiveProjectPhysicalOperations run.state
  let offer : EconomyAction FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation :=
    .offer fiveProjectBank (fiveProjectPhysicalBorrower bid.borrower)
      fiveProjectLoanMarket.principal fiveProjectMoneyGood 1
      (fiveProjectCollateralGood bid.borrower)
  have hmenu : offer ∈ stage.choices.menu fiveProjectBank := by
    change offer ∈ insert EconomyAction.idle
      (insert (instruction.affordableProfile fiveProjectPhysicalOperations
        run.state fiveProjectBank)
        (instruction.affordableAlternatives fiveProjectPhysicalOperations
          run.state fiveProjectBank))
    rw [hinstruction, hOffer]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  let profile : stage.choices.Profile :=
    ⟨fun actor => if actor = fiveProjectBank then offer else .idle,
      by
        intro actor
        by_cases hactor : actor = fiveProjectBank
        · subst actor
          exact hmenu
        · simp [hactor, stage.choices.idle_mem actor]⟩
  exact fiveProjectRunStepWithProfile D run profile

set_option maxRecDepth 2048 in
/-- Replay the fiduciary cycle after declining project two's published loan.
The bank's affordable offer remains enacted at the entry node; only the
borrower changes to inaction, and subsequent markets use the resulting state. -/
def fiveProjectFiduciaryProjectTwoDeclineRun : FiveProjectPhysicalRun := by
  let D := fiveProjectRegimeData .fiduciaryExpansion
  exact fiveProjectRunUsingProfileSelector D
    (fiveProjectProfileSelectorWithUnilateralIdle D
      (.loanAcceptance (2 : Fin 5)) (fiveProjectPhysicalBorrower 2))
    fiveProjectPhysicalFuel (fiveProjectInitialRun D)

set_option maxRecDepth 2048 in
/-- Replay the fiduciary cycle after declining project three's published loan.
The quote stays fixed from the preceding clearing round; all later execution
continues from the refusal branch. -/
def fiveProjectFiduciaryProjectThreeDeclineRun : FiveProjectPhysicalRun := by
  let D := fiveProjectRegimeData .fiduciaryExpansion
  exact fiveProjectRunUsingProfileSelector D
    (fiveProjectProfileSelectorWithUnilateralIdle D
      (.loanAcceptance (3 : Fin 5)) (fiveProjectPhysicalBorrower 3))
    fiveProjectPhysicalFuel (fiveProjectInitialRun D)

theorem fiveProject_list_filterMap_head_preserved_by_append
    {α β : Type} (project : α → Option β) (prior suffix : List α)
    (value : β)
    (hprior : (prior.filterMap project).head? = some value) :
    ((prior ++ suffix).filterMap project).head? = some value := by
  cases hfiltered : prior.filterMap project with
  | nil => simp [hfiltered] at hprior
  | cons first rest =>
      have hfirst : first = value := by
        simpa [hfiltered] using hprior
      subst first
      simp [List.filterMap_append, hfiltered]

/-- Appending events to a cursor cannot erase its first recorded household
plan. This trace property supports plan replay without reducing the remainder
of the physical schedule. -/
theorem fiveProjectNextCursor_preserves_householdPlanHead
    (D : FiveProjectRegimeData) (cursor : FiveProjectPhysicalCursor)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat)
    (step : PhysicalProfileStep fiveProjectPhysicalOperations state)
    (plan : FiveProjectHouseholdPlan)
    (hplan : cursor.actualHouseholdPlans.head? = some plan) :
    (fiveProjectNextCursor D cursor state step).actualHouseholdPlans.head? =
      some plan := by
  change ((fiveProjectNextCursor D cursor state step).events.filterMap
    (fun
      | .householdPlanSelected _ selected _ => some selected
      | _ => none)).head? = some plan
  rw [fiveProjectNextCursor_events_append]
  exact fiveProject_list_filterMap_head_preserved_by_append _ _ _ _ hplan

theorem fiveProjectRunChoices_preserves_householdPlanHead
    (D : FiveProjectRegimeData) (choices : List Bool)
    (run : FiveProjectPhysicalRun) (plan : FiveProjectHouseholdPlan)
    (hplan : run.cursor.actualHouseholdPlans.head? = some plan) :
    (fiveProjectRunChoices D choices run).cursor.actualHouseholdPlans.head? =
      some plan := by
  induction choices generalizing run with
  | nil => simpa [fiveProjectRunChoices] using hplan
  | cons enact rest ih =>
      apply ih
      let instruction := fiveProjectPhysicalInstruction D run.cursor run.state
      let stage := instruction.stage fiveProjectPhysicalOperations run.state
      let profile : stage.choices.Profile :=
        if enact then instruction.selectedProfile fiveProjectPhysicalOperations run.state
        else FiniteEconomyProgram.ProgramHistory.idleProfile stage.choices
      have hnext := fiveProjectNextCursor_preserves_householdPlanHead D
        run.cursor run.state ⟨instruction, profile⟩ plan hplan
      simpa [fiveProjectRunStep, instruction, stage, profile] using hnext

/-- Full selected-plan replay from any regime's initial resources. The initial
choice uses the same generated stage menu as the compiled program; every later
stage is executed by the ordinary state-dependent cursor. -/
def fiveProjectHouseholdPlanRunFor (D : FiveProjectRegimeData)
    (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices D) : FiveProjectPhysicalRun := by
  let initial := fiveProjectInitialRun D
  have hphase : initial.cursor.remainingPhases.head? =
      some .chooseHouseholdPlan := by
    simp [initial, fiveProjectInitialRun, fiveProjectInitialCursor,
      fiveProjectPhysicalPhases]
  let afterPlan := fiveProjectRunSelectedHouseholdPlan D initial plan
    hphase hplan
  exact fiveProjectRunChoices D (List.replicate (fiveProjectPhysicalFuel - 1) true)
    afterPlan

/-- Full menu replay specialized to the stated household-transfer regime. -/
def fiveProjectHouseholdPlanRun (plan : FiveProjectHouseholdPlan)
    (hplan : plan ∈ fiveProjectHouseholdPlanChoices
      (fiveProjectRegimeData .householdTransfer)) : FiveProjectPhysicalRun :=
  fiveProjectHouseholdPlanRunFor (fiveProjectRegimeData .householdTransfer) plan hplan

/-- Continuation after the household selects the idle action at the plan node.
The later fixed schedule still runs, but without a deposit, consumption, or
household factor offer selected by that actor. -/
def fiveProjectHouseholdIdleRunFor (D : FiveProjectRegimeData) :
    FiveProjectPhysicalRun := by
  let afterIdle := fiveProjectRunStep D false (fiveProjectInitialRun D)
  exact fiveProjectRunChoices D (List.replicate (fiveProjectPhysicalFuel - 1) true)
    afterIdle

def fiveProjectHouseholdIdleRun : FiveProjectPhysicalRun :=
  fiveProjectHouseholdIdleRunFor (fiveProjectRegimeData .householdTransfer)

/-- Total plan evaluator used by finite-menu comparisons. A plan outside the
generated menu falls back to the existing idle continuation; members of the
menu always run through their selected plan and the same downstream program.
-/
def fiveProjectHouseholdRunForPlan (D : FiveProjectRegimeData)
    (plan : FiveProjectHouseholdPlan) : FiveProjectPhysicalRun :=
  if h : plan ∈ fiveProjectHouseholdPlanChoices D then
    fiveProjectHouseholdPlanRunFor D plan h
  else fiveProjectHouseholdIdleRunFor D

/-- Execute plan selection, issuance, household transfer, and loan clearing so
loan capacity reads the bank's resulting branch balance. -/
def fiveProjectFundingPrefix (D : FiveProjectRegimeData)
    (enactNotes enactHouseholdTransfer : Bool) : FiveProjectPhysicalRun :=
  let afterPlan := fiveProjectRunStep D true (fiveProjectInitialRun D)
  let afterNotes := fiveProjectRunStep D enactNotes afterPlan
  let afterHouseholdTransfer := fiveProjectRunStep D enactHouseholdTransfer afterNotes
  fiveProjectRunStep D false afterHouseholdTransfer

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
    FiveProjectPhysicalRun := by
  let D := fiveProjectRegimeData .fiduciaryExpansion
  let initial := fiveProjectInitialRun D
  let beforeFirstAcceptance := fiveProjectRunUntilPhase D
    (.loanAcceptance (0 : Fin 5)) initial
  let afterFirstAcceptance := fiveProjectRunStep D enactFirstAdvance
    beforeFirstAcceptance
  let beforeFactorClearing := fiveProjectRunUntilPhase D .factorClearing
    afterFirstAcceptance
  exact fiveProjectRunStep D false beforeFactorClearing

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

/-- Select a plan that consumes both household factors and offers none, then
execute the remaining funding and production schedule. -/
def fiveProjectHouseholdConsumedBeforeFactorClearing : FiveProjectPhysicalRun := by
  let D := fiveProjectRegimeData .householdTransfer
  let plan : FiveProjectHouseholdPlan :=
    { deposit := fiveProjectHouseholdDepositTerms.principal
      consumedFactors := 2
      offeredFactors := 0 }
  let afterPlan := fiveProjectRunSelectedHouseholdPlan D
    (fiveProjectInitialRun D) plan (by decide) (by decide)
  let beforeConsumption := fiveProjectRunUntilPhase D .householdConsumption afterPlan
  exact fiveProjectRunStep D true beforeConsumption

def fiveProjectHouseholdRetainedBeforeFactorClearing : FiveProjectPhysicalRun :=
  fiveProjectRunUntilPhase (fiveProjectRegimeData .householdTransfer) .factorClearing
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
    let before := fiveProjectRunUntilPhase D .householdConsumption
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
    let beforeRefusal := fiveProjectRunUntilPhase D (.factorPurchase (0 : Fin 5))
      (fiveProjectInitialRun D)
    let afterRefusal := fiveProjectRunStep D false beforeRefusal
    let afterFactorSlots := fiveProjectRunUntilPhase D (.customerSale (0 : Fin 5))
      afterRefusal
    let afterCompletion := afterFactorSlots
    let afterCustomerSales := fiveProjectRunUntilPhase D (.loanSettlement (0 : Fin 5))
      afterCompletion
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

/-- Compile the same branch-responsive program from a separately specified
initial cash-buffer vector. Later loan and factor markets are still cleared
when their cursor phases are reached. -/
def fiveProjectPhysicalRegimeProgramWithCashBuffers (D : FiveProjectRegimeData)
    (cashBuffer : Fin 5 → ℕ) :=
  compilePhysicalProfileGenerator fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialStateWithCashBuffers D cashBuffer)

/-- The generated history enacts each affordable scheduled profile through
the same state-dependent cursor and physical interpreter. -/
def fiveProjectPhysicalRegimeHistory (D : FiveProjectRegimeData) :=
  physicalProfileGeneratorHistory fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialState D)

/-- Selected compiled history for an explicit cash-buffer scenario. -/
def fiveProjectPhysicalRegimeHistoryWithCashBuffers (D : FiveProjectRegimeData)
    (cashBuffer : Fin 5 → ℕ) :=
  physicalProfileGeneratorHistory fiveProjectPhysicalOperations
    (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
    (fiveProjectInitialCursor D)
    (fiveProjectFactorInitialStateWithCashBuffers D cashBuffer)

/-- The all-selected direct runner and the generator executor use the same
instruction, selected profile, interpreter, and cursor transition at each
step. This induction avoids re-evaluating the entire named run once per stock
coordinate. -/
theorem fiveProjectRunChoices_all_selected_state (D : FiveProjectRegimeData)
    (fuel : ℕ) (run : FiveProjectPhysicalRun) :
    (fiveProjectRunChoices D (List.replicate fuel true) run).state =
      executePhysicalProfileGenerator fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator D) fuel run.cursor run.state := by
  induction fuel generalizing run with
  | zero => rfl
  | succ fuel ih =>
      simp only [List.replicate_succ, fiveProjectRunChoices,
        executePhysicalProfileGenerator]
      rw [show fiveProjectRunStep D true run =
        { cursor := fiveProjectNextCursor D run.cursor run.state
            ⟨fiveProjectPhysicalInstruction D run.cursor run.state,
              (fiveProjectPhysicalInstruction D run.cursor run.state).selectedProfile
                fiveProjectPhysicalOperations run.state⟩
          state := ((fiveProjectPhysicalInstruction D run.cursor run.state).stage
            fiveProjectPhysicalOperations run.state).advance
              ((fiveProjectPhysicalInstruction D run.cursor run.state).selectedProfile
                fiveProjectPhysicalOperations run.state) } by rfl]
      exact ih _

/-- Final inventory state on the selected schedule history. -/
def fiveProjectPhysicalRegimeTerminalState (D : FiveProjectRegimeData) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat :=
  (fiveProjectPhysicalRegimeHistory D).terminalState

/-- Terminal inventory for the compiled program under an explicit cash-buffer
vector. Every downstream market is evaluated by the same state-dependent
generator from that altered initial state. -/
def fiveProjectPhysicalRegimeTerminalStateWithCashBuffers
    (D : FiveProjectRegimeData) (cashBuffer : Fin 5 → ℕ) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Nat :=
  (fiveProjectPhysicalRegimeHistoryWithCashBuffers D cashBuffer).terminalState

/-- Run the generated instruction sequence by enacting each affordable
scheduled profile. This is a convenience for checking the selected named
path; branch alternatives remain available through `fiveProjectRunStepWithProfile`.
-/
def fiveProjectNamedProgramRun (D : FiveProjectRegimeData) : FiveProjectPhysicalRun :=
  fiveProjectRunChoices D (List.replicate fiveProjectPhysicalFuel true)
    (fiveProjectInitialRun D)

/-- Direct selected path for an explicit initial cash-buffer vector. The
branch's later market terms are recomputed by the ordinary cursor generator. -/
def fiveProjectNamedProgramRunWithCashBuffers (D : FiveProjectRegimeData)
    (cashBuffer : Fin 5 → ℕ) : FiveProjectPhysicalRun :=
  fiveProjectRunChoices D (List.replicate fiveProjectPhysicalFuel true)
    (fiveProjectInitialRunWithCashBuffers D cashBuffer)

/-- The buffered direct runner uses the same selected instructions, profiles,
interpreter, and cursor transitions as its compiled history. -/
theorem fiveProject_buffered_named_run_matches_compiled_history
    (D : FiveProjectRegimeData) (cashBuffer : Fin 5 → ℕ) :
    ∀ agent good,
      (fiveProjectNamedProgramRunWithCashBuffers D cashBuffer).state.stock
          agent good =
        (fiveProjectPhysicalRegimeTerminalStateWithCashBuffers D cashBuffer).stock
          agent good := by
  intro agent good
  change (fiveProjectRunChoices D (List.replicate fiveProjectPhysicalFuel true)
      (fiveProjectInitialRunWithCashBuffers D cashBuffer)).state.stock agent good = _
  rw [fiveProjectRunChoices_all_selected_state]
  change (executePhysicalProfileGenerator fiveProjectPhysicalOperations
      (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
      (fiveProjectInitialCursor D)
      (fiveProjectFactorInitialStateWithCashBuffers D cashBuffer)).stock agent good =
    (physicalProfileGeneratorHistory fiveProjectPhysicalOperations
      (fiveProjectPhysicalRegimeGenerator D) fiveProjectPhysicalFuel
      (fiveProjectInitialCursor D)
      (fiveProjectFactorInitialStateWithCashBuffers D cashBuffer)).terminalState.stock
        agent good
  rw [← physicalProfileGeneratorHistory_terminalState]

/-- The direct selected-path runner and the compiled program's history have
the same interpreter-derived inventory at every agent and physical good. -/
theorem fiveProject_named_run_matches_compiled_history :
    ∀ regime agent good,
      (fiveProjectNamedProgramRun (fiveProjectRegimeData regime)).state.stock
          agent good =
        (fiveProjectPhysicalRegimeTerminalState
          (fiveProjectRegimeData regime)).stock agent good := by
  intro regime agent good
  cases regime <;>
    change (fiveProjectRunChoices _ (List.replicate fiveProjectPhysicalFuel true)
        (fiveProjectInitialRun _)).state.stock agent good = _
  all_goals
    rw [fiveProjectRunChoices_all_selected_state]
    change (executePhysicalProfileGenerator fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator
          (fiveProjectRegimeData _)) fiveProjectPhysicalFuel
        (fiveProjectInitialRun (fiveProjectRegimeData _)).cursor
        (fiveProjectInitialRun (fiveProjectRegimeData _)).state).stock agent good =
      (physicalProfileGeneratorHistory fiveProjectPhysicalOperations
        (fiveProjectPhysicalRegimeGenerator
          (fiveProjectRegimeData _)) fiveProjectPhysicalFuel
        (fiveProjectInitialRun (fiveProjectRegimeData _)).cursor
        (fiveProjectInitialRun (fiveProjectRegimeData _)).state).terminalState.stock
          agent good
    rw [← physicalProfileGeneratorHistory_terminalState]

set_option maxRecDepth 2048 in
/-- The three selected paths record matched funding, factor purchases,
customer sales, repayments, defaults, and the saving contract's redemption.
Each transaction is checked against current physical holdings. -/
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
    fiduciary.cursor.completedProjects.map LoanReservationBid.borrower = [0, 1] ∧
    fiduciary.cursor.completedProjects.length ≤ 2 ∧
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

/-- Funded projects purchase one early input and convert exactly one such
input into capital. The supplier begins with five; the two-project baseline
uses two, while each four-advance branch uses four. Unfunded project four has
no capital in any named path. -/
theorem fiveProject_named_baseline_early_purchases_are_matched :
    let run := fiveProjectNamedProgramRun (fiveProjectRegimeData .baseline)
    run.cursor.actualEarlyInputPurchases.map LoanReservationBid.borrower = [0, 1] := by
  decide

/-- Each baseline early-input purchase is followed by its enacted capital
conversion stage. -/
theorem fiveProject_named_baseline_capital_formations_are_recorded :
    let run := fiveProjectNamedProgramRun (fiveProjectRegimeData .baseline)
    run.cursor.capitalFormations.map LoanReservationBid.borrower = [0, 1] := by
  decide

set_option maxRecDepth 2048 in
/-- Four actually funded projects in the expansion branches each buy an
early input and form capital. The credit branch's two unfinished projects
retain capital; unfunded project four never receives any. -/
theorem fiveProject_named_expansion_inputs_form_capital_one_to_one :
    let credit := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)
    let household := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .householdTransfer)
    credit.cursor.actualEarlyInputPurchases.map LoanReservationBid.borrower =
      [0, 1, 2, 3] ∧
    credit.cursor.capitalFormations.map LoanReservationBid.borrower =
      [0, 1, 2, 3] ∧
    credit.state.stock fiveProjectFactorSupplier fiveProjectEarlyInputGood = 1 ∧
    credit.state.stock (fiveProjectPhysicalBorrower 2) fiveProjectCapitalGood = 1 ∧
    credit.state.stock (fiveProjectPhysicalBorrower 4) fiveProjectCapitalGood = 0 ∧
    household.cursor.actualEarlyInputPurchases.map LoanReservationBid.borrower =
      [0, 1, 2, 3] ∧
    household.cursor.capitalFormations.map LoanReservationBid.borrower =
      [0, 1, 2, 3] ∧
    household.state.stock fiveProjectFactorSupplier fiveProjectEarlyInputGood = 1 ∧
    household.state.stock (fiveProjectPhysicalBorrower 4) fiveProjectCapitalGood = 0 := by
  decide

/-- The credit expansion's factor eligibility reads cash remaining after each
funded project bought its early input. At price two the first two borrowers
can pay from current cash; projects two and three have projected proceeds
sufficient to cover factor cost and repayment but lack the current cash for
that purchase. The factor price remains two and allocation follows the
existing project order. -/
theorem fiveProject_credit_factor_market_uses_post_input_cash :
    let run := fiveProjectFiduciaryFactorClearingRun true
    run.state.stock (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 3 ∧
    run.state.stock (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 3 ∧
    run.state.stock (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood = 1 ∧
    run.state.stock (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood = 1 ∧
    projectPassesCurrentCashAndReturnTest 3 9 4 2 ∧
    projectPassesCurrentCashAndReturnTest 3 8 4 2 ∧
    ¬ projectPassesCurrentCashAndReturnTest 1 7 4 2 ∧
    ¬ projectPassesCurrentCashAndReturnTest 1 6 4 2 ∧
    4 + 2 < 7 ∧
    ¬ 4 + 2 < 6 ∧
    fiveProjectAvailableFactorSupply
      (fiveProjectRegimeData .fiduciaryExpansion) run.cursor run.state = 2 ∧
    run.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) = some (2, [0, 1]) := by
  decide

/-- In the named credit branch, each funded entrepreneur's unit advance is
spent on the unit early input, so current cash at factor clearing equals the
pre-existing cash buffer. -/
theorem fiveProject_credit_post_input_cash_equals_buffers :
    let run := fiveProjectFiduciaryFactorClearingRun true
    run.state.stock (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood =
        fiveProjectCashBuffer 0 ∧
      run.state.stock (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood =
        fiveProjectCashBuffer 1 ∧
      run.state.stock (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood =
        fiveProjectCashBuffer 2 ∧
      run.state.stock (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood =
        fiveProjectCashBuffer 3 := by
  decide

def fiveProjectFourUnitEntrepreneurBuffer : Fin 5 → ℕ := fun _ => 4

set_option maxRecDepth 2048 in
/-- Raising all five initial money buffers to four causes the factor clock to
recompute at price three. It funds no additional completion beyond projects
zero and one: the two marginal projects fail the projected return comparison
at that price. Those borrowers can nevertheless repay their four-unit terms
from their buffer, so their collateral returns even though they never produce
output. -/
theorem fiveProject_larger_cash_buffers_reprice_without_extra_completions :
    let D := fiveProjectRegimeData .fiduciaryExpansion
    let run := fiveProjectNamedProgramRunWithCashBuffers D
      fiveProjectFourUnitEntrepreneurBuffer
    run.cursor.loanQuote = some 4 ∧
    run.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (3, [0, 1]) ∧
    ¬ projectPassesCurrentCashAndReturnTest 4 7 4 3 ∧
    ¬ projectPassesCurrentCashAndReturnTest 4 6 4 3 ∧
    run.cursor.actualFactorPurchases.map LoanReservationBid.borrower = [0, 1] ∧
    run.cursor.completedProjects.map LoanReservationBid.borrower = [0, 1] ∧
    run.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    run.cursor.actualDefaults = [] ∧
    run.state.stock (fiveProjectPhysicalBorrower 2) fiveProjectOutputGood = 0 ∧
    run.state.stock (fiveProjectPhysicalBorrower 2)
      (fiveProjectCollateralGood 2) = 1 ∧
    run.state.stock fiveProjectBank (fiveProjectCollateralGood 2) = 0 ∧
    run.state.stock (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood = 0 ∧
    run.state.stock (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood = 0 := by
  decide

set_option maxRecDepth 2048 in
/-- With four completion factors supplied, the same four funded projects can
all purchase an input, complete, sell output, and repay. This separate
resource comparison shows that the previous completion bound came from the
physical factor stock rather than from the entrepreneurs' cash buffers. -/
theorem fiveProject_sufficient_factors_allow_all_four_projects :
    let D := (fiveProjectRegimeData .fiduciaryExpansion).withSupplierFactorStock 4
    let run := fiveProjectNamedProgramRun D
    run.cursor.factorClearing.map (fun clearing =>
      (clearing.1, clearing.2.map LoanReservationBid.borrower)) =
        some (1, [0, 1, 2, 3]) ∧
    run.cursor.actualFactorPurchases.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    run.cursor.completedProjects.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    run.cursor.actualCustomerSales = [(0, 9), (1, 8), (2, 7), (3, 6)] ∧
    run.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    run.cursor.actualDefaults = [] := by
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

set_option maxRecDepth 2048 in
/-- The compiled schedule's selected histories derive balances, repayment and
default events from matched transfers and maturity-state collateral custody.
The household redemption is separately matched against the bank's cash. -/
theorem fiveProject_named_program_settlement_balances :
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        fiveProjectBank fiveProjectMoneyGood = 12 ∧
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 5 ∧
    (fiveProjectPhysicalRegimeTerminalState (fiveProjectRegimeData .baseline)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 4 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        fiveProjectBank fiveProjectMoneyGood = 8 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 6 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 5 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 2) fiveProjectMoneyGood = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 3) fiveProjectMoneyGood = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        fiveProjectBank fiveProjectMoneyGood = 13 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        fiveProjectHousehold fiveProjectMoneyGood = 5 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        (fiveProjectPhysicalBorrower 0) fiveProjectMoneyGood = 7 ∧
    (fiveProjectPhysicalRegimeTerminalState
        (fiveProjectRegimeData .householdTransfer)).stock
        (fiveProjectPhysicalBorrower 1) fiveProjectMoneyGood = 6 := by
  decide

set_option maxRecDepth 2048 in
/-- Physical loan status and deposit liability are read from the selected
event trace. The two unfunded-at-completion marginal credit borrowers default
only after retaining their collateral through maturity; successful repayment
returns collateral, and successful deposit redemption returns its claim. -/
theorem fiveProject_named_contractual_lifecycle_events :
    let baseline := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .baseline)
    let credit := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .fiduciaryExpansion)
    let household := fiveProjectNamedProgramRun
      (fiveProjectRegimeData .householdTransfer)
    baseline.cursor.actualDefaults = [] ∧
    baseline.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1] ∧
    credit.cursor.actualDefaults.map LoanReservationBid.borrower = [2, 3] ∧
    credit.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1] ∧
    household.cursor.actualDefaults = [] ∧
    household.cursor.actualRepayments.map LoanReservationBid.borrower = [0, 1, 2, 3] ∧
    household.cursor.actualDepositContract = some fiveProjectHouseholdDepositTerms ∧
    household.cursor.actualDepositRedemptions = [fiveProjectHouseholdDepositTerms] ∧
    (fiveProjectPhysicalRegimeTerminalState
      (fiveProjectRegimeData .fiduciaryExpansion)).stock fiveProjectBank
        (fiveProjectCollateralGood 2) = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
      (fiveProjectRegimeData .fiduciaryExpansion)).stock fiveProjectBank
        (fiveProjectCollateralGood 3) = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
      (fiveProjectRegimeData .fiduciaryExpansion)).stock
        (fiveProjectPhysicalBorrower 0) (fiveProjectCollateralGood 0) = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
      (fiveProjectRegimeData .householdTransfer)).stock
        fiveProjectBank fiveProjectDepositClaimGood = 1 ∧
    (fiveProjectPhysicalRegimeTerminalState
      (fiveProjectRegimeData .householdTransfer)).stock
        fiveProjectHousehold fiveProjectDepositClaimGood = 0 := by
  decide

end Praxeology
