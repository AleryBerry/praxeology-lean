/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Regimes
public import Praxeology.FiniteEconomy.Compiler
public import Praxeology.FiniteEconomy.Physical

/-!
# Physical execution of completion-factor purchases

The Regimes factor-demand lists are projected calculations; this executor
clears again from each prepared branch's actual funded advances and offered
stocks. It preserves the initial-buffer participation rule, then checks each
transfer against current holdings through the physical interpreter. The
resulting purchases run as sequential bilateral transfers. The household's
stated consumption is run first; offered factors remain in its inventory until
a matched trade sells them. The existing output schedule then supplies the
completion operations, and customer purchases execute through matched trades.
Each factor-sale stage keeps idle and unilateral offer/accept profiles in its
finite menu; only the matched profile transfers inventory. Regime-specified
fiduciary notes, the household cash transfer, and standardized loan advances are also
executed through operation or matched-transfer stages. After sales, each
completed project's auction-quoted repayment is a separate matched transfer.
The household-to-bank transfer is only the cash leg: no deposit claim or bank
repayment obligation is represented. The earlier input and capital-production
stage remains unmodeled; projects excluded from completion are not adjudicated
as defaults, and legal foreclosure is outside this physical ledger.
-/

@[expose] public section

namespace Praxeology

abbrev FiveProjectPhysicalAgent := Fin 9
abbrev FiveProjectPhysicalGood := Fin 3

def fiveProjectFactorSupplier : FiveProjectPhysicalAgent := 0
def fiveProjectBank : FiveProjectPhysicalAgent := 7
def fiveProjectHousehold : FiveProjectPhysicalAgent := 8
def fiveProjectMoneyGood : FiveProjectPhysicalGood := 0
def fiveProjectCompletionGood : FiveProjectPhysicalGood := 1
def fiveProjectOutputGood : FiveProjectPhysicalGood := 2

/-- The customer's initial money endowment in the fixed physical witness. -/
def fiveProjectCustomerMoneyEndowment : ℕ := 40

def fiveProjectPhysicalBorrower (project : Fin 5) : FiveProjectPhysicalAgent :=
  ⟨project.val + 1, by omega⟩

inductive FiveProjectPhysicalOperation where
  | issueFiduciaryNotes (quantity : ℕ)
  | consumeHouseholdFactors (quantity : ℕ)
  | completeProject (project : Fin 5)
  deriving DecidableEq

def fiveProjectPhysicalOperations :
    OperationSemantics FiveProjectPhysicalOperation
      FiveProjectPhysicalGood Unit where
  input operation good :=
    match operation with
    | .issueFiduciaryNotes _ => 0
    | .consumeHouseholdFactors quantity =>
        if good = fiveProjectCompletionGood then quantity else 0
    | .completeProject _ =>
        if good = fiveProjectCompletionGood then 1 else 0
  output operation good :=
    match operation with
    | .issueFiduciaryNotes quantity =>
        if good = fiveProjectMoneyGood then quantity else 0
    | .consumeHouseholdFactors _ => 0
    | .completeProject project =>
        if good = fiveProjectOutputGood then fiveProjectOutput project else 0
  service _ _ := 0

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

/-- Apply one matched completion-factor purchase to the current inventory.
Insufficient seller stock or buyer money yields `none` under the existing
pre-transition affordability check. -/
def executeFiveProjectFactorPurchase
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectFactorPurchaseProfile seller buyer price)

/-- A successful factor purchase obeys the interpreter's exact bilateral
inventory balances: one completion unit and `price` money units move between
the two parties. No additional transfer rule is assumed here. -/
theorem executeFiveProjectFactorPurchase_balances
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (active : Finset FiveProjectPhysicalAgent)
    (profile_nonidle : ∀ agent, agent ∈ active → profile agent ≠ EconomyAction.idle)
    (profile_wellFormed : ∀ agent,
      EconomyAction.WellFormed agent (profile agent))
    (profile_affordable : ∀ agent,
      actionAffordable fiveProjectPhysicalOperations state agent (profile agent)) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Unit :=
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ)
    (hdistinct : sender ≠ recipient)
    (hfunded : quantity ≤ state.stock sender fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Unit := by
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

/-- The transfer stage contains both parties' unilateral choices and the
complete matched profile. Each unilateral profile leaves the other party idle. -/
theorem fiveProjectMoneyTransferChoiceStage_branches
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
      FiveProjectPhysicalGood FiveProjectPhysicalOperation Unit)
    (profile : ActionProfile (Agent := FiveProjectPhysicalAgent)
      (Means := FiveProjectPhysicalGood) (Operation := FiveProjectPhysicalOperation))
    (selected : ∀ agent, profile agent ∈ stage.choices.menu agent) :
    stage.choices.Profile :=
  ⟨profile, selected⟩

/-- A completion-factor purchase stage generated from the same action profile
that the physical interpreter executes. The menu includes the supplier's
unilateral offer and the borrower's unilateral acceptance alongside idling. -/
def fiveProjectFactorPurchaseChoiceStage
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (seller buyer : FiveProjectPhysicalAgent) (price : ℕ)
    (hdistinct : seller ≠ buyer)
    (hsupply : 1 ≤ state.stock seller fiveProjectCompletionGood)
    (hcash : price ≤ state.stock buyer fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Unit := by
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
def fiveProjectFactorInitialState (D : FiveProjectRegimeData) :
    PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit :=
  PhysicalState.zeroServices fun agent good =>
    match good.val with
    | 0 =>
        match agent.val with
        | 1 => fiveProjectCashBuffer 0
        | 2 => fiveProjectCashBuffer 1
        | 3 => fiveProjectCashBuffer 2
        | 4 => fiveProjectCashBuffer 3
        | 5 => fiveProjectCashBuffer 4
        | 6 => fiveProjectCustomerMoneyEndowment
        | 7 => D.bankMoney
        | 8 => D.householdMoneyEndowment
        | _ => 0
    | 1 =>
        if agent = fiveProjectFactorSupplier then D.supplierFactorStock
        else if agent = fiveProjectHousehold then D.householdFactorEndowment
        else 0
    | _ => 0

/-- Fiduciary notes specified by a regime are issued by the bank operation
before the loan auction's funded advances. The amount comes directly from the
regime's explicit note-issuance field. -/
def issueFiveProjectFiduciaryNotes (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (sender recipient : FiveProjectPhysicalAgent) (quantity : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  if quantity = 0 then some state
  else if sender = recipient then none
  else advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectMoneyTransferProfile sender recipient quantity)

/-- For a positive affordable transfer, the executable transition equals the
matched profile's branch in the choice stage that also contains the two
unilateral alternatives. -/
theorem fiveProjectMoneyTransfer_is_choiceStage_advance
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (agent : FiveProjectPhysicalAgent) (quantity : ℕ) (hquantity : 0 < quantity) :
    executeFiveProjectMoneyTransfer state agent agent quantity = none := by
  simp [executeFiveProjectMoneyTransfer, Nat.ne_of_gt hquantity]

/-- Execute the cash-transfer leg recorded in the household-transfer regime.
This is a matched zero-price money transfer; it does not issue a deposit claim
or record a bank obligation to repay the household. A zero transfer is the
identity transition. -/
def executeFiveProjectHouseholdCashTransfer (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  executeFiveProjectMoneyTransfer state fiveProjectHousehold fiveProjectBank
    D.householdMoneyTransferred

/-- Any household cash transfer recorded as affordable by the regime data
executes as a matched transfer from the initial physical cash balance. This
checks the funding source against the interpreter; it establishes neither a
deposit claim nor a purposeful saving choice. -/
theorem executeFiveProjectHouseholdCashTransfer_succeeds
    (D : FiveProjectRegimeData) :
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
    · simp [executeFiveProjectHouseholdCashTransfer, executeFiveProjectMoneyTransfer, hzero]
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
      simpa [executeFiveProjectHouseholdCashTransfer, stage, selected] using
        fiveProjectMoneyTransfer_is_choiceStage_advance
          (fiveProjectFactorInitialState D) fiveProjectHousehold fiveProjectBank
          D.householdMoneyTransferred hdistinct hpositive hfunded
    have hbalances := executeFiveProjectMoneyTransfer_balances
      (fiveProjectFactorInitialState D) (stage.advance selected)
      fiveProjectHousehold fiveProjectBank D.householdMoneyTransferred hdistinct
      (by simpa [executeFiveProjectHouseholdCashTransfer] using hstep)
    refine ⟨stage.advance selected, hstep, ?_, ?_⟩
    · have hhousehold := hbalances.1
      rw [hinitialHousehold] at hhousehold
      exact hhousehold
    · have hbank := hbalances.2
      rw [hinitialBank] at hbank
      exact hbank

/-- Execute the principal advances for the loan auction's funded prefix. The
fixed market has unit principal, and each advance is a separate matched
transfer from the bank to the named borrower. -/
def executeFiveProjectLoanAdvances
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
  | [] => some state
  | bid :: rest =>
      (executeFiveProjectMoneyTransfer state fiveProjectBank
        (fiveProjectPhysicalBorrower bid.borrower) fiveProjectLoanMarket.principal).bind
        fun next => executeFiveProjectLoanAdvances next rest

/-- Execute each scheduled loan transfer and return exactly the bids whose
matched transfer succeeded. -/
def executeFiveProjectLoanAdvancesWithTrace
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit ×
        List LoanReservationBid)
  | [] => some (state, [])
  | bid :: rest =>
      (executeFiveProjectMoneyTransfer state fiveProjectBank
        (fiveProjectPhysicalBorrower bid.borrower) fiveProjectLoanMarket.principal).bind
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
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit ×
      List LoanReservationBid) :=
  (issueFiveProjectFiduciaryNotes D (fiveProjectFactorInitialState D)).bind
    fun noted =>
      (executeFiveProjectHouseholdCashTransfer D noted).bind fun transferred =>
        (fiveProjectLoanOutcomeAfterSourcesFor D).bind fun outcome =>
          executeFiveProjectLoanAdvancesWithTrace transferred outcome.funded

def fiveProjectExecutedLoanAdvancesFor (D : FiveProjectRegimeData) :
    Option (List LoanReservationBid) :=
  (fiveProjectFundedTraceFor D).map Prod.snd

/-- Build the pre-production physical state by executing note issuance,
the household cash transfer, and the loan auction's actual funded advances in sequence.
The loan-auction source total and physical bank receipts are the same regime
data used to compute capacity. -/
def fiveProjectFundedStateFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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

/-- At the current modeled funding checkpoint, the two marginal fiduciary
borrowers each hold their one-unit buffer plus the one-unit loan advance. They
can therefore afford price two from current cash even though the projected
initial-buffer test rejects them at that price. The physical affordability
check is separate from this participation rule; earlier input production
remains absent. -/
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (price : ℕ) : List (Fin 5 × FiveProjectPhysicalAgent) →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
  | [] => some state
  | (project, seller) :: rest =>
      (executeFiveProjectFactorPurchase state seller
        (fiveProjectPhysicalBorrower project) price).bind fun next =>
          executeFiveProjectFactorPlan next price rest

/-- Execute ordinary household factor consumption before the factor market,
using the regime's explicit consumption quantity. -/
def prepareFiveProjectHouseholdFactors (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) : ℕ :=
  min D.supplierFactorStock (state.stock fiveProjectFactorSupplier
    fiveProjectCompletionGood)

def fiveProjectAvailableHouseholdFactors (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) : ℕ :=
  min D.householdFactorsOffered (state.stock fiveProjectHousehold
    fiveProjectCompletionGood)

/-- Clear the completion-factor market against currently available offered
stock and actual loan-source branch. Its existing initial-buffer test determines
participation; the resulting transfers still face the interpreter's separate
current-inventory affordability check. -/
def fiveProjectFactorMarketAtStateFor (D : FiveProjectRegimeData)
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    Option (ℕ × List LoanReservationBid) :=
  (fiveProjectLoanOutcomeAfterSourcesFor D).bind fun outcome =>
    outcome.quotedRepayment.bind fun quote =>
      (fiveProjectExecutedLoanAdvancesFor D).bind fun actualAdvances =>
        let supply := fiveProjectAvailableSupplierFactors D state +
          fiveProjectAvailableHouseholdFactors D state
        (ascendingCompletionFactorPrice? actualAdvances quote 1 supply 3).map
          fun price =>
            (price, factorDemandingProjectsAt actualAdvances quote price)

/-- State immediately before factor-market clearing, after the executed
funding branch and the household's stated factor-consumption operation. -/
def fiveProjectPreparedFactorStateFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  (fiveProjectFundedStateFor D).bind fun state =>
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
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (project : Fin 5) (quantity : ℕ)
    (houtput : quantity ≤ state.stock (fiveProjectPhysicalBorrower project)
      fiveProjectOutputGood)
    (hcash : quantity ≤ state.stock 6 fiveProjectMoneyGood) :
    FinitePhysicalChoiceStage FiveProjectPhysicalAgent FiveProjectPhysicalGood
      FiveProjectPhysicalOperation Unit := by
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
    (project : Fin 5) (quantity : ℕ) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  advanceIfAffordable fiveProjectPhysicalOperations state
    (fiveProjectCustomerPurchaseProfile project quantity)

/-- A successful customer purchase obeys the physical interpreter's exact
bilateral inventory balances. The customer's money outflow and the seller's
money inflow equal the output quantity scheduled for sale. -/
theorem executeFiveProjectCustomerPurchase_balances
    (state next : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    List (Fin 5 × ℕ) →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
  | [] => some state
  | (project, quantity) :: rest =>
      (executeFiveProjectCustomerPurchase state project quantity).bind fun next =>
        executeFiveProjectCustomerPlan next rest

/-- Generate each customer purchase from the completed project's current
output and the customer's remaining money, then continue from the resulting
inventory. The order is the actual factor-market funded order. -/
def executeFiveProjectCustomerPlanFromState
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    List LoanReservationBid →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
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
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
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
    (state : PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :
    List FundedLoanTerms →
      Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit)
  | [] => some state
  | contract :: rest =>
      (executeFiveProjectMoneyTransfer state
        (fiveProjectPhysicalBorrower contract.borrower)
        fiveProjectBank contract.promisedRepayment).bind fun next =>
          executeFiveProjectRepaymentPlan next rest

/-- Run completed-project repayments only after their production and customer
sales have executed. This is a physical settlement stage; it does not model
default adjudication, legal title, or foreclosure. -/
def fiveProjectLoanSettlementExecutionFor (D : FiveProjectRegimeData) :
    Option (PhysicalState FiveProjectPhysicalAgent FiveProjectPhysicalGood Unit) :=
  (fiveProjectCustomerSaleExecutionFor D).bind fun state =>
    (fiveProjectCompletedLoanTermsFor D).bind fun contracts =>
      executeFiveProjectRepaymentPlan state contracts

/-- Read a money balance after completed-project repayments. -/
def fiveProjectSettledMoneyBalance? (D : FiveProjectRegimeData)
    (agent : FiveProjectPhysicalAgent) : Option ℕ :=
  (fiveProjectLoanSettlementExecutionFor D).map fun state =>
    state.stock agent fiveProjectMoneyGood

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
      (fiveProjectPhysicalBorrower 0) = some 6 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .baseline)
      (fiveProjectPhysicalBorrower 1) = some 5 ∧
    (fiveProjectLoanSettlementExecutionFor
      (fiveProjectRegimeData .fiduciaryExpansion)).isSome = true ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      fiveProjectBank = some 8 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 0) = some 7 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      (fiveProjectPhysicalBorrower 1) = some 6 ∧
    (fiveProjectLoanSettlementExecutionFor
      (fiveProjectRegimeData .householdTransfer)).isSome = true ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectBank = some 16 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 0) = some 8 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 1) = some 7 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 2) = some 4 ∧
    fiveProjectSettledMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      (fiveProjectPhysicalBorrower 3) = some 3 := by
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

/-- Named factor markets use actual funded advances and offered stock while
preserving the existing initial-buffer participation rule. The two marginal
borrowers each have two units of current cash but fail that separate buffer
condition at price two. -/
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

/-- Under fiduciary expansion, the two projects that remain eligible under the
initial-buffer participation rule at price two acquire the supplier's two
factors; the excluded projects do not receive inventory. This is distinct
from the physical affordability check on each executed transfer. -/
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
      fiveProjectFactorSupplier = some 2 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .baseline) 6 = some 23 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion)
      fiveProjectFactorSupplier = some 4 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .fiduciaryExpansion) 6 = some 23 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectFactorSupplier = some 2 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer)
      fiveProjectHousehold = some 2 ∧
    fiveProjectExecutedMoneyBalance? (fiveProjectRegimeData .householdTransfer) 6 = some 10 := by
  decide

end Praxeology

end
