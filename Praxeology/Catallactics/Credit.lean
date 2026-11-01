/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Catallactics
public import Praxeology.Production

/-!
# Credit Contracts and Loan Events

Credit is represented by matched, purposeful exchange actions. A collateralized
advance transfers cash to the borrower and collateral into the lender's custody;
repayment reverses those flows. A custody run records the physical collateral
held through maturity. This module deliberately leaves legal title outside the
ActionFrame inventory vocabulary.
-/

@[expose] public section

namespace Praxeology

variable {W : ActionFrame}

/-- Terms of a cash advance secured by temporary transfer of collateral into
the lender's custody. -/
structure PawnLoanTerms (W : ActionFrame) where
  lender : W.Agent
  borrower : W.Agent
  money : W.Means
  collateral : W.Means
  principal : ℕ
  netRepaymentFactor : ℕ
  collateralQuantity : ℕ
  maturity : W.Moment
  distinctAgents : lender ≠ borrower
  distinctGoods : money ≠ collateral
  principalPositive : 0 < principal
  collateralPositive : 0 < collateralQuantity

/-- The contractual gross repayment factor. -/
def PawnLoanTerms.grossRepaymentFactor {W : ActionFrame} (T : PawnLoanTerms W) : ℕ :=
  T.netRepaymentFactor + 1

/-- Contractual repayment derived from principal and the net factor. -/
def PawnLoanTerms.repayment {W : ActionFrame} (T : PawnLoanTerms W) : ℕ :=
  T.principal * T.grossRepaymentFactor

/-- The nominal premium promised above principal, without assuming a valuation
or price index. -/
def PawnLoanTerms.nominalPremium {W : ActionFrame} (T : PawnLoanTerms W) : ℕ :=
  T.principal * T.netRepaymentFactor

/-- The loan identity determines the same gross repayment factor whenever
principal and repayment are fixed. Thus an equal rate is derived from the
contract's two cash quantities, not supplied as a separate rate assumption. -/
theorem PawnLoanTerms.same_grossRepaymentFactor_of_same_principal_and_repayment
    {W : ActionFrame} (T₁ T₂ : PawnLoanTerms W)
    (h_principal : T₁.principal = T₂.principal)
    (h_repayment : T₁.repayment = T₂.repayment) :
    T₁.grossRepaymentFactor = T₂.grossRepaymentFactor := by
  have h_products :
      T₁.principal * T₁.grossRepaymentFactor =
        T₁.principal * T₂.grossRepaymentFactor := by
    calc
      T₁.principal * T₁.grossRepaymentFactor = T₁.repayment := rfl
      _ = T₂.repayment := h_repayment
      _ = T₂.principal * T₂.grossRepaymentFactor := rfl
      _ = T₁.principal * T₂.grossRepaymentFactor := by rw [h_principal]
  exact (mul_left_cancel_iff_of_pos T₁.principalPositive).mp h_products

/-- Evidence that two loan rates are quotations from the same Catallactic
market. Here its good is a standardized one-period loan service, so the
clearing price is the gross repayment factor in the market's repayment-money
denomination. The rounds share a borrower and lender, and their common
reservation interval has a single admissible price. Each contract identifies
its gross repayment factor with that clearing price. -/
structure CatallacticCreditRateComparison {W : ActionFrame}
    (T_saving T_credit : PawnLoanTerms W) where
  market : MultilateralCohortMarket W.Agent W.Means
  savingRound : PurposefulFundedClearingRound market
  creditRound : PurposefulFundedClearingRound market
  sameBorrower : T_saving.borrower = T_credit.borrower
  sameLender : T_saving.lender = T_credit.lender
  savingBorrower_is_marketBuyer :
    T_saving.borrower = savingRound.base.clearing.buyer
  creditBorrower_is_marketBuyer :
    T_credit.borrower = creditRound.base.clearing.buyer
  savingLender_is_marketSeller :
    T_saving.lender = savingRound.base.clearing.seller
  creditLender_is_marketSeller :
    T_credit.lender = creditRound.base.clearing.seller
  savingMoney_is_marketMoney : T_saving.money = market.m_money
  creditMoney_is_marketMoney : T_credit.money = market.m_money
  unique_mutually_acceptable_rate :
    savingRound.reservation.sellerFloor =
      savingRound.reservation.buyerCeiling
  savingRate_is_clearing_price :
    T_saving.grossRepaymentFactor = savingRound.base.clearing.price
  creditRate_is_clearing_price :
    T_credit.grossRepaymentFactor = creditRound.base.clearing.price

namespace CatallacticCreditRateComparison

/-- A shared lender, borrower, and singleton reservation price make the two
clearing rounds charge the same market price. -/
theorem same_clearing_price {W : ActionFrame}
    {T_saving T_credit : PawnLoanTerms W}
    (Q : CatallacticCreditRateComparison T_saving T_credit) :
    Q.savingRound.base.clearing.price = Q.creditRound.base.clearing.price := by
  have h_buyer : Q.savingRound.base.clearing.buyer =
      Q.creditRound.base.clearing.buyer := by
    calc
      _ = T_saving.borrower := Q.savingBorrower_is_marketBuyer.symm
      _ = T_credit.borrower := Q.sameBorrower
      _ = _ := Q.creditBorrower_is_marketBuyer
  have h_seller : Q.savingRound.base.clearing.seller =
      Q.creditRound.base.clearing.seller := by
    calc
      _ = T_saving.lender := Q.savingLender_is_marketSeller.symm
      _ = T_credit.lender := Q.sameLender
      _ = _ := Q.creditLender_is_marketSeller
  exact PurposefulFundedClearingRound.same_price_of_singleton_reservation
    Q.savingRound Q.creditRound h_buyer h_seller
    Q.unique_mutually_acceptable_rate

/-- The two contractual gross repayment factors are derived equal from their
shared Catallactic market clearing price. -/
theorem same_gross_repayment_factor {W : ActionFrame}
    {T_saving T_credit : PawnLoanTerms W}
    (Q : CatallacticCreditRateComparison T_saving T_credit) :
    T_saving.grossRepaymentFactor = T_credit.grossRepaymentFactor := by
  calc
    T_saving.grossRepaymentFactor = Q.savingRound.base.clearing.price :=
      Q.savingRate_is_clearing_price
    _ = Q.creditRound.base.clearing.price := Q.same_clearing_price
    _ = T_credit.grossRepaymentFactor := Q.creditRate_is_clearing_price.symm

end CatallacticCreditRateComparison

theorem PawnLoanTerms.repayment_covers_principal {W : ActionFrame}
    (T : PawnLoanTerms W) : T.principal ≤ T.repayment := by
  dsimp [PawnLoanTerms.repayment, PawnLoanTerms.grossRepaymentFactor]
  nlinarith

theorem PawnLoanTerms.nominalPremium_nonnegative {W : ActionFrame}
    (T : PawnLoanTerms W) : 0 ≤ T.nominalPremium := Nat.zero_le _

theorem PawnLoanTerms.nominalPremium_eq_zero_iff {W : ActionFrame}
    (T : PawnLoanTerms W) : T.nominalPremium = 0 ↔ T.repayment = T.principal := by
  constructor
  · intro h
    dsimp [PawnLoanTerms.nominalPremium, PawnLoanTerms.repayment,
      PawnLoanTerms.grossRepaymentFactor] at *
    nlinarith [T.principalPositive]
  · intro h
    dsimp [PawnLoanTerms.nominalPremium, PawnLoanTerms.repayment,
      PawnLoanTerms.grossRepaymentFactor] at *
    nlinarith [T.principalPositive]

theorem PawnLoanTerms.principal_add_nominalPremium {W : ActionFrame}
    (T : PawnLoanTerms W) :
    T.principal + T.nominalPremium = T.repayment := by
  dsimp [PawnLoanTerms.nominalPremium, PawnLoanTerms.repayment,
    PawnLoanTerms.grossRepaymentFactor]
  ring

theorem PawnLoanTerms.nominalPremium_mono
    {W : ActionFrame} (T₁ T₂ : PawnLoanTerms W)
    (hprincipal : T₁.principal = T₂.principal)
    (hrepayment : T₁.repayment ≤ T₂.repayment) :
    T₁.nominalPremium ≤ T₂.nominalPremium := by
  have h₁ := T₁.principal_add_nominalPremium
  have h₂ := T₂.principal_add_nominalPremium
  rw [hprincipal] at h₁
  omega

/-- Event labels for the finite lifecycle of a credit contract. -/
inductive CreditEvent where
  | advance
  | repayment
  | unpaidMaturity
  deriving DecidableEq

/-- Contract status, kept distinct from the physical inventory ledger. -/
inductive CreditStatus where
  | unadvanced
  | outstanding
  | repaid
  | defaulted
  deriving DecidableEq

/-- The permissible lifecycle transitions for one loan. -/
inductive CreditTransition : CreditStatus → CreditEvent → CreditStatus → Prop where
  | advance : CreditTransition .unadvanced .advance .outstanding
  | repayment : CreditTransition .outstanding .repayment .repaid
  | unpaidMaturity : CreditTransition .outstanding .unpaidMaturity .defaulted

theorem credit_advance_opens_obligation :
    CreditTransition .unadvanced .advance .outstanding :=
  .advance

theorem credit_repayment_discharges_obligation :
    CreditTransition .outstanding .repayment .repaid :=
  .repayment

theorem credit_unpaid_maturity_defaults :
    CreditTransition .outstanding .unpaidMaturity .defaulted :=
  .unpaidMaturity

/-- An actual purposeful advance: the lender offers principal for custody of
collateral, the borrower accepts, and both acts are recorded on the same
history at adjacent moments. -/
structure CreditAdvance {W : ActionFrame} (T : PawnLoanTerms W) where
  history : W.History
  moment : W.Moment
  nextMoment : W.Moment
  successor : IsNextMoment W.Precedence W.mem_hist moment nextMoment history
  purposefulExchange : @BilateralExchange W T.lender T.borrower moment history
    T.principal T.money T.collateralQuantity T.collateral

namespace CreditAdvance

/-- The lender's matched-offer inventory step, derived from the purposeful
bilateral exchange and its ActionFrame enactment. -/
def lenderInventoryStep {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    InventoryStep W T.lender A.history A.moment A.nextMoment := by
  have hactions := bilateral_exchange_enacted_actions T.lender T.borrower
    A.moment A.history T.principal T.money T.collateralQuantity T.collateral
    A.purposefulExchange
  exact .matchedOffer T.borrower T.principal T.money T.collateralQuantity
    T.collateral T.distinctAgents hactions.1 hactions.2 A.successor

/-- The borrower's matched-acceptance inventory step for the same advance. -/
def borrowerInventoryStep {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    InventoryStep W T.borrower A.history A.moment A.nextMoment := by
  have hactions := bilateral_exchange_enacted_actions T.lender T.borrower
    A.moment A.history T.principal T.money T.collateralQuantity T.collateral
    A.purposefulExchange
  exact .matchedAccept T.lender T.principal T.money T.collateralQuantity
    T.collateral T.distinctAgents hactions.2 hactions.1 A.successor

/-- The matched loan advance is a one-edge lender inventory run. -/
def lenderInventoryRun {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    InventoryRun W T.lender A.history A.moment A.nextMoment :=
  .step A.lenderInventoryStep (.done A.nextMoment)

/-- The matched loan advance is a one-edge borrower inventory run. -/
def borrowerInventoryRun {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    InventoryRun W T.borrower A.history A.moment A.nextMoment :=
  .step A.borrowerInventoryStep (.done A.nextMoment)

end CreditAdvance

/-- The matched advance adds the principal to borrower cash and places the
collateral in lender custody. -/
theorem CreditAdvance.physical_transfer {W : ActionFrame}
    {T : PawnLoanTerms W} (A : CreditAdvance T) :
    W.omega T.borrower A.nextMoment A.history T.money =
        W.omega T.borrower A.moment A.history T.money + T.principal ∧
    W.omega T.lender A.nextMoment A.history T.collateral =
        W.omega T.lender A.moment A.history T.collateral + T.collateralQuantity := by
  rcases bilateral_exchange_enacted_actions T.lender T.borrower A.moment A.history
      T.principal T.money T.collateralQuantity T.collateral A.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.lender T.borrower
    A.moment A.nextMoment A.history T.principal T.money T.collateralQuantity
    T.collateral T.distinctAgents T.distinctGoods A.successor
    h_offer h_accept
  exact ⟨hflow.2.1, hflow.2.2.1⟩

/-- The lender pays the principal media during the matched advance. -/
theorem CreditAdvance.lender_media_decreases {W : ActionFrame}
    {T : PawnLoanTerms W} (A : CreditAdvance T) :
    W.omega T.lender A.nextMoment A.history T.money + T.principal =
      W.omega T.lender A.moment A.history T.money := by
  rcases bilateral_exchange_enacted_actions T.lender T.borrower A.moment A.history
      T.principal T.money T.collateralQuantity T.collateral A.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.lender T.borrower
    A.moment A.nextMoment A.history T.principal T.money T.collateralQuantity
    T.collateral T.distinctAgents T.distinctGoods A.successor h_offer h_accept
  exact hflow.1

/-- The borrower supplies the agreed collateral during the matched advance. -/
theorem CreditAdvance.borrower_collateral_decreases {W : ActionFrame}
    {T : PawnLoanTerms W} (A : CreditAdvance T) :
    W.omega T.borrower A.nextMoment A.history T.collateral + T.collateralQuantity =
      W.omega T.borrower A.moment A.history T.collateral := by
  rcases bilateral_exchange_enacted_actions T.lender T.borrower A.moment A.history
      T.principal T.money T.collateralQuantity T.collateral A.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.lender T.borrower
    A.moment A.nextMoment A.history T.principal T.money T.collateralQuantity
    T.collateral T.distinctAgents T.distinctGoods A.successor h_offer h_accept
  exact hflow.2.2.2

/-- Spendable media held by agents other than the issuer. -/
def circulatingMedia {W : ActionFrame} (issuer : W.Agent) (money : W.Means)
    (t : W.Moment) (h : W.History) : ℕ :=
  ∑ a ∈ Finset.univ.erase issuer, W.omega a t h money

/-- Total media, split into the issuer's treasury and circulation. -/
def totalMedia {W : ActionFrame} (issuer : W.Agent) (money : W.Means)
    (t : W.Moment) (h : W.History) : ℕ :=
  W.omega issuer t h money + circulatingMedia issuer money t h

/-- The treasury/circulation split is exactly the finite population total. -/
theorem totalMedia_eq_universal_sum {W : ActionFrame} (issuer : W.Agent)
    (money : W.Means) (t : W.Moment) (h : W.History) :
    totalMedia issuer money t h = ∑ a ∈ Finset.univ, W.omega a t h money := by
  classical
  unfold totalMedia circulatingMedia
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun a : W.Agent => W.omega a t h money) (Finset.mem_univ issuer)
  omega

/-- A purposeful, enacted production step that creates spendable bank media
without consuming existing media or reserve commodities.  This interface is
defined for every `ActionFrame`; a finite compiler can supply its witnesses,
but does not define the banking claim. -/
structure FiduciaryNoteIssuance {W : ActionFrame} where
  issuer : W.Agent
  history : W.History
  moment : W.Moment
  nextMoment : W.Moment
  money : W.Means
  reserve : W.Means
  principal : ℕ
  action : W.Action
  successor : IsNextMoment W.Precedence W.mem_hist moment nextMoment history
  distinctGoods : money ≠ reserve
  principalPositive : 0 < principal
  enacted : W.enacted issuer moment history = action
  purposeful : @PurposefulAct W issuer moment history action
  nontrade : ¬ W.IsTradeAction action
  moneyInputZero : W.use_means action money = 0
  moneyOutput : W.yield_means action money = principal
  reserveInputZero : W.use_means action reserve = 0
  reserveOutputZero : W.yield_means action reserve = 0
  otherAgentsIdle : ∀ a, a ≠ issuer →
    W.enacted a moment history = W.alpha_zero

/-- The actual inventory witness associated with a note-issuance certificate. -/
def FiduciaryNoteIssuance.inventoryStep {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) :
    InventoryStep W I.issuer I.history I.moment I.nextMoment :=
  .production I.action I.enacted I.nontrade I.successor

/-- Note printing raises the issuer's spendable media by exactly the printed
principal. -/
theorem FiduciaryNoteIssuance.issuer_media_increases {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) :
    W.omega I.issuer I.nextMoment I.history I.money =
      W.omega I.issuer I.moment I.history I.money + I.principal := by
  have h := I.inventoryStep.inventory_balance I.money
  simp [FiduciaryNoteIssuance.inventoryStep, InventoryStep.effectiveUse,
    InventoryStep.effectiveYield, I.moneyInputZero, I.moneyOutput] at h
  omega

/-- Printing does not alter the issuer's reserve commodity. -/
theorem FiduciaryNoteIssuance.issuer_reserve_unchanged {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) :
    W.omega I.issuer I.nextMoment I.history I.reserve =
      W.omega I.issuer I.moment I.history I.reserve := by
  have h := I.inventoryStep.inventory_balance I.reserve
  simp [FiduciaryNoteIssuance.inventoryStep, InventoryStep.effectiveUse,
    InventoryStep.effectiveYield, I.reserveInputZero, I.reserveOutputZero] at h
  omega

/-- Other agents' balances are unchanged by an issuance step when they enact
the baseline action. -/
theorem FiduciaryNoteIssuance.other_media_unchanged {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) {a : W.Agent} (ha : a ≠ I.issuer) :
    W.omega a I.nextMoment I.history I.money =
      W.omega a I.moment I.history I.money := by
  have h := W.law_in_re_transition a I.moment I.nextMoment I.history
    W.alpha_zero I.money alpha_zero_not_trade (I.otherAgentsIdle a ha) I.successor
  rw [W.use_means_alpha_zero, W.yield_means_alpha_zero] at h
  omega

/-- Minting creates notes in the issuer's treasury and leaves circulation
unchanged. -/
theorem FiduciaryNoteIssuance.circulating_media_unchanged {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) :
    circulatingMedia I.issuer I.money I.nextMoment I.history =
      circulatingMedia I.issuer I.money I.moment I.history := by
  classical
  unfold circulatingMedia
  apply Finset.sum_congr rfl
  intro a ha
  have haIssuer : a ≠ I.issuer := (Finset.mem_erase.mp ha).1
  exact I.other_media_unchanged haIssuer

/-- Minting raises total spendable media by exactly the printed principal. -/
theorem FiduciaryNoteIssuance.total_media_increases {W : ActionFrame}
    (I : FiduciaryNoteIssuance (W := W)) :
    totalMedia I.issuer I.money I.nextMoment I.history =
      totalMedia I.issuer I.money I.moment I.history + I.principal := by
  unfold totalMedia
  rw [I.issuer_media_increases, I.circulating_media_unchanged]
  omega

/-- The account-level evidence that a minted note was issued as a matched,
purposeful collateralized advance.  The record ties the generic issuance and
`CreditAdvance` certificates together by their event, agent, and good indices. -/
structure FiduciaryOrigination {W : ActionFrame} (T : PawnLoanTerms W)
    (I : FiduciaryNoteIssuance (W := W)) (A : CreditAdvance T) where
  lender_is_issuer : T.lender = I.issuer
  money_matches : T.money = I.money
  principal_matches : T.principal = I.principal
  history_matches : A.history = I.history
  advance_follows_issue : A.moment = I.nextMoment
  nonparticipants_idle : ∀ a, a ≠ T.lender → a ≠ T.borrower →
    W.enacted a A.moment A.history = W.alpha_zero

/-- Name the physical issuance certificate as a balance-sheet event. It is
still just an `InventoryStep.production` together with ActionFrame purpose
and enactment evidence. -/
abbrev FiduciaryIssuanceStep (W : ActionFrame) :=
  FiduciaryNoteIssuance (W := W)

namespace FiduciaryOrigination

/-- The note-printing production step is the one-edge inventory run that
immediately precedes the matched credit advance. -/
def issueToAdvanceRun {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryIssuanceStep W} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    InventoryRun W T.lender I.history I.moment A.moment := by
  simpa [O.lender_is_issuer, O.advance_follows_issue] using
    (InventoryRun.step I.inventoryStep (.done I.nextMoment))

/-- The banker's full origination trace consists of purposeful note printing
followed by the matched lender offer in the credit advance. -/
def lenderOriginationRun {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryIssuanceStep W} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    InventoryRun W T.lender I.history I.moment A.nextMoment := by
  have hadvance : InventoryRun W T.lender I.history A.moment A.nextMoment := by
    simpa [O.lender_is_issuer, O.history_matches] using A.lenderInventoryRun
  exact O.issueToAdvanceRun.append hadvance

/-- The borrower's full origination trace consists of idling during note
printing followed by the matched acceptance of the credit advance. -/
def borrowerOriginationRun {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryIssuanceStep W} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    InventoryRun W T.borrower I.history I.moment A.nextMoment := by
  have hBorrowerIssuer : T.borrower ≠ I.issuer := by
    intro h
    apply T.distinctAgents
    rw [O.lender_is_issuer]
    exact h.symm
  let issueStep : InventoryStep W T.borrower I.history I.moment I.nextMoment :=
    .production W.alpha_zero (I.otherAgentsIdle T.borrower hBorrowerIssuer)
      alpha_zero_not_trade I.successor
  have issueRun : InventoryRun W T.borrower I.history I.moment I.nextMoment :=
    .step issueStep (.done I.nextMoment)
  have hadvance : InventoryRun W T.borrower I.history I.nextMoment A.nextMoment := by
    simpa [O.history_matches, O.advance_follows_issue] using A.borrowerInventoryRun
  exact issueRun.append hadvance

end FiduciaryOrigination

/-- One bank-book entry couples a purposeful note issuance, its immediately
following matched advance, and the proof that they are one origination. -/
structure FiduciaryBankEvent (W : ActionFrame) where
  terms : PawnLoanTerms W
  issuance : FiduciaryIssuanceStep W
  advance : CreditAdvance terms
  origination : FiduciaryOrigination terms issuance advance

/-- An opening bank ledger records an ordered sequence of witnessed fiduciary
originations. List order is recording order; the underlying events remain
ActionFrame production and bilateral-exchange certificates. -/
structure FiduciaryBankLedger (W : ActionFrame) where
  events : List (FiduciaryBankEvent W)

namespace FiduciaryBankLedger

/-- Total note principal for a finite list of origination events. -/
def noteLiabilityOf {W : ActionFrame} (events : List (FiduciaryBankEvent W)) : ℕ :=
  (events.map fun event => event.issuance.principal).sum

/-- Total loan principal for a finite list of origination events. -/
def loanAssetsOf {W : ActionFrame} (events : List (FiduciaryBankEvent W)) : ℕ :=
  (events.map fun event => event.terms.principal).sum

/-- Equal-principal origination records keep assets and liabilities in
balance. -/
theorem loanAssetsOf_eq_noteLiabilityOf {W : ActionFrame}
    (events : List (FiduciaryBankEvent W)) :
    loanAssetsOf events = noteLiabilityOf events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      change event.terms.principal + loanAssetsOf rest =
        event.issuance.principal + noteLiabilityOf rest
      rw [event.origination.principal_matches, ih]

/-- External note liabilities issued by the bank over the recorded origination
sequence. Repayment and default events are separate lifecycle entries. -/
def externalNoteLiability {W : ActionFrame} (B : FiduciaryBankLedger W) : ℕ :=
  noteLiabilityOf B.events

/-- Loan assets opened by the same certified origination sequence. -/
def loanAssets {W : ActionFrame} (B : FiduciaryBankLedger W) : ℕ :=
  loanAssetsOf B.events

/-- Every recorded origination creates equal principal-valued note liabilities
and loan assets. This balance-sheet identity is polymorphic in `ActionFrame`. -/
theorem loanAssets_eq_externalNoteLiability {W : ActionFrame}
    (B : FiduciaryBankLedger W) :
    B.loanAssets = B.externalNoteLiability := by
  exact loanAssetsOf_eq_noteLiabilityOf B.events

/-- Appending an actual origination adds its principal to both sides of the
bank's balance sheet. -/
def append (B : FiduciaryBankLedger W) (event : FiduciaryBankEvent W) :
    FiduciaryBankLedger W :=
  { events := B.events ++ [event] }

theorem append_loanAssets {W : ActionFrame} (B : FiduciaryBankLedger W)
    (event : FiduciaryBankEvent W) :
    (B.append event).loanAssets = B.loanAssets + event.terms.principal := by
  simp [append, loanAssets, loanAssetsOf, List.map_append]

theorem append_externalNoteLiability {W : ActionFrame}
    (B : FiduciaryBankLedger W) (event : FiduciaryBankEvent W) :
    (B.append event).externalNoteLiability =
      B.externalNoteLiability + event.issuance.principal := by
  simp [append, externalNoteLiability, noteLiabilityOf, List.map_append]

end FiduciaryBankLedger

theorem FiduciaryOrigination.borrower_ne_issuer {W : ActionFrame}
    {T : PawnLoanTerms W} {I : FiduciaryNoteIssuance (W := W)}
    {A : CreditAdvance T} (O : FiduciaryOrigination T I A) :
    T.borrower ≠ I.issuer := by
  intro h
  apply T.distinctAgents
  rw [O.lender_is_issuer]
  exact h.symm

/-- A fiduciary origination returns the bank's treasury media to its
pre-issuance level after the newly printed principal is advanced. -/
theorem FiduciaryOrigination.issuer_media_unchanged
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    W.omega I.issuer A.nextMoment I.history I.money =
      W.omega I.issuer I.moment I.history I.money := by
  have hIssue := I.issuer_media_increases
  have hAdvance := A.lender_media_decreases
  rw [O.lender_is_issuer, O.money_matches, O.history_matches,
    O.advance_follows_issue] at hAdvance
  rw [O.principal_matches] at hAdvance
  omega

/-- The borrower receives the full newly issued principal, while the issuer's
printing step leaves the borrower's opening balance unchanged. -/
theorem FiduciaryOrigination.borrower_media_increases
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    W.omega T.borrower A.nextMoment I.history T.money =
      W.omega T.borrower I.moment I.history T.money + T.principal := by
  have hIssue := I.other_media_unchanged O.borrower_ne_issuer
  have hAdvance := A.physical_transfer.1
  rw [O.history_matches, O.advance_follows_issue, O.money_matches] at hAdvance
  rw [O.money_matches]
  omega

/-- A bystander receives or spends no media during a one-loan origination. -/
theorem FiduciaryOrigination.third_party_media_unchanged
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) (a : W.Agent)
    (haLender : a ≠ T.lender) (haBorrower : a ≠ T.borrower) :
    W.omega a A.nextMoment I.history T.money =
      W.omega a I.moment I.history T.money := by
  have haIssuer : a ≠ I.issuer := by
    intro h
    apply haLender
    calc
      a = I.issuer := h
      _ = T.lender := O.lender_is_issuer.symm
  have hIssue := I.other_media_unchanged haIssuer
  have hAdvance := W.law_in_re_transition a A.moment A.nextMoment A.history
    W.alpha_zero T.money alpha_zero_not_trade (O.nonparticipants_idle a haLender haBorrower)
    A.successor
  rw [W.use_means_alpha_zero, W.yield_means_alpha_zero] at hAdvance
  rw [O.history_matches, O.advance_follows_issue, O.money_matches] at hAdvance
  calc
    W.omega a A.nextMoment I.history T.money =
        W.omega a A.nextMoment I.history I.money := by rw [O.money_matches]
    _ = W.omega a I.nextMoment I.history I.money := hAdvance
    _ = W.omega a I.moment I.history I.money := hIssue
    _ = W.omega a I.moment I.history T.money := by rw [← O.money_matches]

/-- Settled fiduciary origination adds the principal to circulating media. -/
theorem FiduciaryOrigination.circulating_media_increases
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    circulatingMedia I.issuer I.money A.nextMoment I.history =
      circulatingMedia I.issuer I.money I.moment I.history + T.principal := by
  classical
  let S := Finset.univ.erase I.issuer
  have hborrower : T.borrower ∈ S := by
    simp [S, O.borrower_ne_issuer]
  have hafter := Finset.sum_erase_add S
    (fun a : W.Agent => W.omega a A.nextMoment I.history I.money) hborrower
  have hbefore := Finset.sum_erase_add S
    (fun a : W.Agent => W.omega a I.moment I.history I.money) hborrower
  have hrest :
      (∑ a ∈ S.erase T.borrower, W.omega a A.nextMoment I.history I.money) =
        ∑ a ∈ S.erase T.borrower, W.omega a I.moment I.history I.money := by
    apply Finset.sum_congr rfl
    intro a ha
    have hparts := Finset.mem_erase.mp ha
    have haIssuer : a ≠ I.issuer := (Finset.mem_erase.mp hparts.2).1
    have haBorrower : a ≠ T.borrower := hparts.1
    have haLender : a ≠ T.lender := by
      intro heq
      apply haIssuer
      calc
        a = T.lender := heq
        _ = I.issuer := O.lender_is_issuer
    have hthird := O.third_party_media_unchanged a haLender haBorrower
    rw [O.money_matches] at hthird
    exact hthird
  have hborrowerFlow := O.borrower_media_increases
  rw [O.money_matches] at hborrowerFlow
  unfold circulatingMedia
  dsimp [S] at hafter hbefore hrest
  rw [← hafter, ← hbefore, hrest]
  omega

/-- The issue-and-advance pair expands total spendable media by its principal. -/
theorem FiduciaryOrigination.total_media_increases
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A) :
    totalMedia I.issuer I.money A.nextMoment I.history =
      totalMedia I.issuer I.money I.moment I.history + T.principal := by
  unfold totalMedia
  rw [O.issuer_media_unchanged, O.circulating_media_increases]
  simp [Nat.add_assoc]

/-- An actual purposeful redemption exchanges the agreed repayment amount for
the return of collateral. -/
structure CreditRepayment {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) where
  moment : W.Moment
  nextMoment : W.Moment
  successor : IsNextMoment W.Precedence W.mem_hist moment nextMoment A.history
  afterAdvance : W.Precedence A.nextMoment moment
  beforeMaturity : W.Precedence moment T.maturity
  purposefulExchange : @BilateralExchange W T.borrower T.lender moment A.history
    T.repayment T.money T.collateralQuantity T.collateral

/-- Repayment returns collateral to the borrower and transfers the repayment
amount of cash to the lender. -/
theorem CreditRepayment.physical_transfer {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T} (R : CreditRepayment A) :
    W.omega T.lender R.nextMoment A.history T.money =
        W.omega T.lender R.moment A.history T.money + T.repayment ∧
    W.omega T.borrower R.nextMoment A.history T.collateral =
        W.omega T.borrower R.moment A.history T.collateral + T.collateralQuantity := by
  rcases bilateral_exchange_enacted_actions T.borrower T.lender R.moment A.history
      T.repayment T.money T.collateralQuantity T.collateral R.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.borrower T.lender
    R.moment R.nextMoment A.history T.repayment T.money T.collateralQuantity
    T.collateral T.distinctAgents.symm T.distinctGoods R.successor
    h_offer h_accept
  exact ⟨hflow.2.1, hflow.2.2.1⟩

/-- The borrower pays the agreed cash amount during the matched redemption. -/
theorem CreditRepayment.borrower_money_decreases {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T} (R : CreditRepayment A) :
    W.omega T.borrower R.nextMoment A.history T.money + T.repayment =
      W.omega T.borrower R.moment A.history T.money := by
  rcases bilateral_exchange_enacted_actions T.borrower T.lender R.moment A.history
      T.repayment T.money T.collateralQuantity T.collateral R.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.borrower T.lender
    R.moment R.nextMoment A.history T.repayment T.money T.collateralQuantity
    T.collateral T.distinctAgents.symm T.distinctGoods R.successor
    h_offer h_accept
  exact hflow.1

/-- The lender releases the agreed collateral when the repayment is accepted. -/
theorem CreditRepayment.lender_collateral_decreases {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T} (R : CreditRepayment A) :
    W.omega T.lender R.nextMoment A.history T.collateral + T.collateralQuantity =
      W.omega T.lender R.moment A.history T.collateral := by
  rcases bilateral_exchange_enacted_actions T.borrower T.lender R.moment A.history
      T.repayment T.money T.collateralQuantity T.collateral R.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers T.borrower T.lender
    R.moment R.nextMoment A.history T.repayment T.money T.collateralQuantity
    T.collateral T.distinctAgents.symm T.distinctGoods R.successor
    h_offer h_accept
  exact hflow.2.2.2

/-- A trace of lender custody from the completed advance to maturity. The
zero-flow conditions mean the collateral remains in custody throughout this
trace. -/
structure CollateralCustodyTrace {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) where
  run : InventoryRun W T.lender A.history A.nextMoment T.maturity
  noCollateralUse : run.totalUse T.collateral = 0
  noCollateralYield : run.totalYield T.collateral = 0

/-- The lender still holds the collateral at maturity when no intervening
action consumes or transfers it. -/
theorem CollateralCustodyTrace.collateral_retained {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T}
    (C : CollateralCustodyTrace A) :
    W.omega T.lender T.maturity A.history T.collateral =
      W.omega T.lender A.nextMoment A.history T.collateral := by
  have hbalance := C.run.inventory_balance T.collateral
  rw [C.noCollateralUse, C.noCollateralYield, Nat.add_zero, Nat.add_zero] at hbalance
  exact hbalance

/-- A contract that reaches maturity with no repayment is classified as
defaulted. The premise records non-repayment; it does not infer it from the
absence of a possible action. -/
structure UnpaidMaturity {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) where
  custody : CollateralCustodyTrace A
  noRepaymentByMaturity : ¬ Nonempty (CreditRepayment A)

theorem UnpaidMaturity.status_transition {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T} (_D : UnpaidMaturity A) :
    CreditTransition .outstanding .unpaidMaturity .defaulted :=
  .unpaidMaturity

/-- Because collateral was transferred into the lender's custody at origination,
retaining the collateral upon unpaid default requires no seizure from the borrower.
When the borrower enacts inaction `alpha_zero` at maturity across `successor`,
the borrower's entire physical stock is preserved. -/
theorem UnpaidMaturity.borrower_stock_preserved_at_default
    {W : ActionFrame} {T : PawnLoanTerms W} {A : CreditAdvance T}
    (_D : UnpaidMaturity A)
    (t_post : W.Moment)
    (h_succ : IsNextMoment W.Precedence W.mem_hist T.maturity t_post A.history)
    (h_borrower_idle : W.enacted T.borrower T.maturity A.history = W.alpha_zero) :
    StockPreserved T.borrower T.maturity t_post A.history := by
  intro m
  have h_trans := W.law_in_re_transition T.borrower T.maturity t_post A.history
    W.alpha_zero m alpha_zero_not_trade h_borrower_idle h_succ
  rw [W.use_means_alpha_zero, W.yield_means_alpha_zero, Nat.add_zero, Nat.add_zero] at h_trans
  change W.omega T.borrower T.maturity A.history m ≤ W.omega T.borrower t_post A.history m
  rw [h_trans]

/-- Retention of collateral upon default does not contract the borrower's stock in any good. -/
theorem UnpaidMaturity.borrower_stock_not_contracted
    {W : ActionFrame} {T : PawnLoanTerms W} {A : CreditAdvance T}
    (D : UnpaidMaturity A)
    (t_post : W.Moment)
    (h_succ : IsNextMoment W.Precedence W.mem_hist T.maturity t_post A.history)
    (h_borrower_idle : W.enacted T.borrower T.maturity A.history = W.alpha_zero)
    (m : W.Means) :
    ¬ StockContractedAt T.borrower T.maturity t_post A.history m := by
  have h_pres := D.borrower_stock_preserved_at_default t_post h_succ h_borrower_idle
  intro h_contr
  dsimp [StockContractedAt] at h_contr
  have h_trans := W.law_in_re_transition T.borrower T.maturity t_post A.history
    W.alpha_zero m alpha_zero_not_trade h_borrower_idle h_succ
  rw [W.use_means_alpha_zero, W.yield_means_alpha_zero, Nat.add_zero, Nat.add_zero] at h_trans
  change W.omega T.borrower t_post A.history m <
    W.omega T.borrower T.maturity A.history m at h_contr
  rw [h_trans] at h_contr
  exact lt_irrefl _ h_contr

/-- Non-invasive collateral retention: the borrower's resource-feasible menu is preserved
at default maturity without any external contraction. -/
theorem UnpaidMaturity.borrower_resource_menu_preserved
    {W : ActionFrame} {T : PawnLoanTerms W} {A : CreditAdvance T}
    (D : UnpaidMaturity A)
    (t_post : W.Moment)
    (h_succ : IsNextMoment W.Precedence W.mem_hist T.maturity t_post A.history)
    (h_borrower_idle : W.enacted T.borrower T.maturity A.history = W.alpha_zero) :
    ResourceMenuPreserved T.borrower T.maturity t_post A.history :=
  stockPreserved_implies_resourceMenuPreserved T.borrower T.maturity t_post A.history
    (D.borrower_stock_preserved_at_default t_post h_succ h_borrower_idle)

/-- Repayment settles the contract and returns the collateral under the stated
matched-exchange evidence. -/
theorem CreditRepayment.status_transition {W : ActionFrame}
    {T : PawnLoanTerms W} {A : CreditAdvance T} (_R : CreditRepayment A) :
    CreditTransition .outstanding .repayment .repaid :=
  .repayment

-- Section 5: Spot-Trade Feasibility, Media Aggregation Limits, and Redemption Shortfall

/-- In any ActionFrame, accepting a spot purchase of `qA` units of `mA` in exchange for
`price` units of `m_money` is feasible at `(t, h)` if and only if the acceptance action
is contemplated and the buyer's physical endowment of `m_money` covers `price`. -/
theorem accept_spot_trade_feasible_iff {W : ActionFrame}
    (buyer seller : W.Agent) (t : W.Moment) (h : W.History)
    (qA : ℕ) (mA : W.Means) (price : ℕ) (m_money : W.Means) :
    W.Accept buyer seller qA mA price m_money ∈ W.A_feas buyer t h ↔
      W.Accept buyer seller qA mA price m_money ∈ W.A_cont buyer t h ∧
      price ≤ W.omega buyer t h m_money := by
  rw [W.A_feas_coupling]
  constructor
  · rintro ⟨h_cont, h_all⟩
    refine ⟨h_cont, ?_⟩
    have h_m := h_all m_money
    rw [W.use_means_accept] at h_m
    simp only [ite_true] at h_m
    exact h_m
  · rintro ⟨h_cont, h_le⟩
    refine ⟨h_cont, fun m => ?_⟩
    rw [W.use_means_accept]
    split_ifs with hm
    · subst hm; exact h_le
    · exact Nat.zero_le _

/-- Cross-medium aggregation impossibility: even if a buyer's summed holdings across two
distinct media `m₁ ≠ m₂` cover `price`, if neither individual medium holding covers `price`,
then spot purchase acceptance is infeasible (and non-purposeful) in both media. -/
theorem infeasible_accept_of_split_media_endowment {W : ActionFrame}
    (buyer seller : W.Agent) (t : W.Moment) (h : W.History)
    (qA : ℕ) (mA : W.Means) (price : ℕ) (m₁ m₂ : W.Means)
    (_h_distinct : m₁ ≠ m₂)
    (_h_sum_covers : price ≤ W.omega buyer t h m₁ + W.omega buyer t h m₂)
    (h_short₁ : W.omega buyer t h m₁ < price)
    (h_short₂ : W.omega buyer t h m₂ < price) :
    W.Accept buyer seller qA mA price m₁ ∉ W.A_feas buyer t h ∧
    W.Accept buyer seller qA mA price m₂ ∉ W.A_feas buyer t h ∧
    ¬ @PurposefulAct W buyer t h (W.Accept buyer seller qA mA price m₁) ∧
    ¬ @PurposefulAct W buyer t h (W.Accept buyer seller qA mA price m₂) := by
  have h_infeas₁ : W.Accept buyer seller qA mA price m₁ ∉ W.A_feas buyer t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff buyer seller t h qA mA price m₁).mp
      h_feas |>.2
    omega
  have h_infeas₂ : W.Accept buyer seller qA mA price m₂ ∉ W.A_feas buyer t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff buyer seller t h qA mA price m₂).mp
      h_feas |>.2
    omega
  refine ⟨h_infeas₁, h_infeas₂, fun hp => h_infeas₁ hp.1, fun hp => h_infeas₂ hp.1⟩

/-- Cross-agent aggregation impossibility: even if two buyers' combined holdings of medium
`m_money` cover `price`, if neither buyer individually holds `price`, neither buyer can
feasibly or purposefully enact the spot purchase. -/
theorem infeasible_accept_of_split_agent_endowment {W : ActionFrame}
    (buyer₁ buyer₂ seller : W.Agent) (t : W.Moment) (h : W.History)
    (qA : ℕ) (mA : W.Means) (price : ℕ) (m_money : W.Means)
    (_h_sum_covers : price ≤ W.omega buyer₁ t h m_money + W.omega buyer₂ t h m_money)
    (h_short₁ : W.omega buyer₁ t h m_money < price)
    (h_short₂ : W.omega buyer₂ t h m_money < price) :
    W.Accept buyer₁ seller qA mA price m_money ∉ W.A_feas buyer₁ t h ∧
    W.Accept buyer₂ seller qA mA price m_money ∉ W.A_feas buyer₂ t h ∧
    ¬ @PurposefulAct W buyer₁ t h (W.Accept buyer₁ seller qA mA price m_money) ∧
    ¬ @PurposefulAct W buyer₂ t h (W.Accept buyer₂ seller qA mA price m_money) := by
  have h_infeas₁ : W.Accept buyer₁ seller qA mA price m_money ∉ W.A_feas buyer₁ t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff buyer₁ seller t h qA mA price m_money).mp
      h_feas |>.2
    omega
  have h_infeas₂ : W.Accept buyer₂ seller qA mA price m_money ∉ W.A_feas buyer₂ t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff buyer₂ seller t h qA mA price m_money).mp
      h_feas |>.2
    omega
  refine ⟨h_infeas₁, h_infeas₂, fun hp => h_infeas₁ hp.1, fun hp => h_infeas₂ hp.1⟩

/-- A non-fiduciary credit advance strictly conserves `totalMedia` when non-participants
enact `alpha_zero`. -/
theorem CreditAdvance.totalMedia_conserved {W : ActionFrame}
    {T : PawnLoanTerms W} (A : CreditAdvance T) (issuer : W.Agent)
    (h_idle : ∀ a, a ≠ T.lender → a ≠ T.borrower →
      W.enacted a A.moment A.history = W.alpha_zero) :
    totalMedia issuer T.money A.nextMoment A.history =
      totalMedia issuer T.money A.moment A.history := by
  classical
  rw [totalMedia_eq_universal_sum, totalMedia_eq_universal_sum]
  have h_lender := A.lender_media_decreases
  have h_borrower := A.physical_transfer.1
  have h_pair :
      W.omega T.borrower A.nextMoment A.history T.money +
        W.omega T.lender A.nextMoment A.history T.money =
      W.omega T.borrower A.moment A.history T.money +
        W.omega T.lender A.moment A.history T.money := by omega
  have h_rest : ∀ a ∈ (Finset.univ : Finset W.Agent),
      a ≠ T.borrower → a ≠ T.lender →
      W.omega a A.nextMoment A.history T.money =
        W.omega a A.moment A.history T.money := by
    intro a _ haB haL
    have haLender : a ≠ T.lender := haL
    have haBorrower : a ≠ T.borrower := haB
    have h_law := W.law_in_re_transition a A.moment A.nextMoment A.history
      W.alpha_zero T.money alpha_zero_not_trade (h_idle a haLender haBorrower) A.successor
    rw [W.use_means_alpha_zero, W.yield_means_alpha_zero, Nat.add_zero, Nat.add_zero] at h_law
    exact h_law
  exact finset_sum_pair_update Finset.univ T.borrower T.lender
    (Finset.mem_univ _) (Finset.mem_univ _) T.distinctAgents.symm
    (fun a => W.omega a A.moment A.history T.money)
    (fun a => W.omega a A.nextMoment A.history T.money)
    h_pair h_rest

/-- Advancing principal in a credit advance contracts the lender's money stock and strips
any tight money-using action from the lender's feasible menu (`FeasibleMenuStripped`). -/
theorem CreditAdvance.lender_tight_action_stripped [W : ActionFrame]
    {T : PawnLoanTerms W} (A : CreditAdvance T) (β : W.Action)
    (h_feas : β ∈ W.A_feas T.lender A.moment A.history)
    (h_cont : β ∈ W.A_cont T.lender A.nextMoment A.history)
    (h_tight : W.use_means β T.money = W.omega T.lender A.moment A.history T.money) :
    FeasibleMenuStripped T.lender A.moment A.nextMoment A.history β := by
  have h_dec := A.lender_media_decreases
  have h_pos := T.principalPositive
  have h_contract : StockContractedAt T.lender A.moment A.nextMoment A.history T.money := by
    dsimp [StockContractedAt, omega]
    omega
  exact stockContractedAt_strips_tight_action T.lender A.moment A.nextMoment A.history
    T.money β h_contract h_feas h_cont h_tight

/-- A full fiduciary origination (note printing followed by loan advance) leaves the
issuer's physical reserve stock unchanged when the advance is not collateralized in the
reserve commodity. -/
theorem FiduciaryOrigination.issuer_reserve_unchanged
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A)
    (h_collateral_ne_reserve : T.collateral ≠ I.reserve) :
    W.omega I.issuer A.nextMoment I.history I.reserve =
      W.omega I.issuer I.moment I.history I.reserve := by
  have hIssue := I.issuer_reserve_unchanged
  rcases bilateral_exchange_enacted_actions T.lender T.borrower A.moment A.history
      T.principal T.money T.collateralQuantity T.collateral A.purposefulExchange with
    ⟨h_offer, h_accept⟩
  have h_tr := (W.bilateral_transfer_law T.lender T.borrower
    T.principal T.money T.collateralQuantity T.collateral
    A.moment A.nextMoment A.history I.reserve T.distinctAgents h_offer h_accept A.successor).1
  have h_m_ne : I.reserve ≠ T.money := by
    rw [O.money_matches]
    exact I.distinctGoods.symm
  have h_c_ne : I.reserve ≠ T.collateral := h_collateral_ne_reserve.symm
  simp only [h_m_ne, h_c_ne, ite_false, Nat.add_zero] at h_tr
  rw [O.lender_is_issuer, O.history_matches, O.advance_follows_issue] at h_tr
  exact h_tr.trans hIssue

/-- Whenever a redemption demand `q` of fiduciary notes `m_note` for `q` units of
`m_reserve` exceeds the issuer's physical reserve endowment, accepting the redemption is
infeasible (`∉ A_feas`) and cannot be a `PurposefulAct`. -/
theorem redemption_accept_not_purposeful_of_exceeds_reserve {W : ActionFrame}
    (issuer holder : W.Agent) (t : W.Moment) (h : W.History)
    (q : ℕ) (m_note m_reserve : W.Means)
    (h_exceeds : W.omega issuer t h m_reserve < q) :
    W.Accept issuer holder q m_note q m_reserve ∉ W.A_feas issuer t h ∧
    ¬ @PurposefulAct W issuer t h (W.Accept issuer holder q m_note q m_reserve) := by
  have h_infeas : W.Accept issuer holder q m_note q m_reserve ∉ W.A_feas issuer t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff issuer holder t h q m_note q m_reserve).mp
      h_feas |>.2
    omega
  exact ⟨h_infeas, fun hp => h_infeas hp.1⟩

/-- Fiduciary origination creates an unbacked redemption shortfall: if opening reserves
weakly covered or equaled circulating media, the newly originated fiduciary media expands
circulation strictly beyond the unchanged physical reserve. -/
theorem FiduciaryOrigination.unbacked_expansion_creates_redemption_shortfall
    {W : ActionFrame} {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (O : FiduciaryOrigination T I A)
    (h_collateral_ne_reserve : T.collateral ≠ I.reserve)
    (h_reserve_le : W.omega I.issuer I.moment I.history I.reserve ≤
      circulatingMedia I.issuer I.money I.moment I.history) :
    W.omega I.issuer A.nextMoment I.history I.reserve <
      circulatingMedia I.issuer I.money A.nextMoment I.history := by
  have h_res := O.issuer_reserve_unchanged h_collateral_ne_reserve
  have h_circ := O.circulating_media_increases
  have h_pos := T.principalPositive
  omega

-- Section 6: Disaggregated Endowment Matrix, Two-Tier Fiat Architecture, and Base Money Partition

/-- The primary disaggregated monetary state: the full agent-by-medium endowment matrix. -/
def EndowmentMatrix (W : ActionFrame) (t : W.Moment) (h : W.History) : W.Agent → W.Means → ℕ :=
  fun a m => W.omega a t h m

/-- Macro-sum underdetermination: a macro aggregate cash sum `∑ a, omega a` does not determine
whether any individual agent can feasibly or purposefully enact a spot purchase of price `P`. -/
theorem macro_sum_underdetermines_spot_feasibility {W : ActionFrame}
    (buyer seller : W.Agent) (t : W.Moment) (h : W.History)
    (qA : ℕ) (mA : W.Means) (price : ℕ) (m_money : W.Means)
    (h_short : W.omega buyer t h m_money < price) :
    W.Accept buyer seller qA mA price m_money ∉ W.A_feas buyer t h ∧
    ¬ @PurposefulAct W buyer t h (W.Accept buyer seller qA mA price m_money) := by
  have h_infeas : W.Accept buyer seller qA mA price m_money ∉ W.A_feas buyer t h := by
    intro h_feas
    have h_le := (accept_spot_trade_feasible_iff buyer seller t h qA mA price m_money).mp
      h_feas |>.2
    omega
  exact ⟨h_infeas, fun hp => h_infeas hp.1⟩

/-- Spendable fiduciary media issued by a specific commercial bank `bank`. -/
def bankCirculatingMedia {W : ActionFrame} (bank : W.Agent) (m_dep : W.Means)
    (t : W.Moment) (h : W.History) : ℕ :=
  circulatingMedia bank m_dep t h

/-- Physical reserves held in custody by a specific commercial bank `bank`. -/
def bankReserve {W : ActionFrame} (bank : W.Agent) (m_reserve : W.Means)
    (t : W.Moment) (h : W.History) : ℕ :=
  W.omega bank t h m_reserve

/-- Unbacked fiduciary overhang for an individual commercial bank: the excess of its
circulating checkable deposit liabilities over its custodial physical reserves. -/
def bankOverhang {W : ActionFrame} (bank : W.Agent) (m_dep m_reserve : W.Means)
    (t : W.Moment) (h : W.History) : ℕ :=
  bankCirculatingMedia bank m_dep t h - bankReserve bank m_reserve t h

/-- Bank-specific redemption infeasibility: even if the system-wide sum of reserves were large,
if an individual bank's custodial reserve falls short of a redemption demand `q`, accepting
the redemption is resource-infeasible for that specific bank. -/
theorem bank_specific_redemption_infeasible_of_local_shortfall {W : ActionFrame}
    (bank holder : W.Agent) (t : W.Moment) (h : W.History)
    (q : ℕ) (m_dep m_reserve : W.Means)
    (h_short : bankReserve bank m_reserve t h < q) :
    W.Accept bank holder q m_dep q m_reserve ∉ W.A_feas bank t h ∧
    ¬ @PurposefulAct W bank t h (W.Accept bank holder q m_dep q m_reserve) := by
  dsimp [bankReserve] at h_short
  exact redemption_accept_not_purposeful_of_exceeds_reserve
    bank holder t h q m_dep m_reserve h_short

/-- The non-bank, non-treasury public agent cohort. -/
def publicAgents {W : ActionFrame} (Banks : Finset W.Agent) (treasury : W.Agent) :
    Finset W.Agent :=
  (Finset.univ \ Banks).erase treasury

/-- Physical base currency held by the non-bank public. -/
def publicBaseCash {W : ActionFrame} (Banks : Finset W.Agent) (treasury : W.Agent)
    (m_reserve : W.Means) (t : W.Moment) (h : W.History) : ℕ :=
  ∑ a ∈ publicAgents Banks treasury, W.omega a t h m_reserve

/-- Total base reserves held in custody by the commercial banking sector. -/
def bankReserves {W : ActionFrame} (Banks : Finset W.Agent)
    (m_reserve : W.Means) (t : W.Moment) (h : W.History) : ℕ :=
  ∑ b ∈ Banks, W.omega b t h m_reserve

/-- Total physical base money in the economy. -/
def totalBaseMoney {W : ActionFrame} (m_reserve : W.Means) (t : W.Moment) (h : W.History) : ℕ :=
  ∑ a ∈ Finset.univ, W.omega a t h m_reserve

/-- Exact disjoint three-sector base money partition: total base money equals public currency
plus bank custodial reserves plus treasury central bank balances. -/
theorem totalBaseMoney_eq_three_sector_partition {W : ActionFrame}
    (Banks : Finset W.Agent) (treasury : W.Agent)
    (h_treas_not_bank : treasury ∉ Banks)
    (m_reserve : W.Means) (t : W.Moment) (h : W.History) :
    totalBaseMoney m_reserve t h =
      publicBaseCash Banks treasury m_reserve t h +
      bankReserves Banks m_reserve t h +
      W.omega treasury t h m_reserve := by
  classical
  unfold totalBaseMoney publicBaseCash bankReserves publicAgents
  have h_sub : Banks ⊆ Finset.univ := Finset.subset_univ Banks
  have h_split := (Finset.sum_sdiff h_sub (f := fun a => W.omega a t h m_reserve)).symm
  have h_mem : treasury ∈ Finset.univ \ Banks := by
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ treasury, h_treas_not_bank⟩
  have h_erase := Finset.sum_erase_add (Finset.univ \ Banks)
    (fun a => W.omega a t h m_reserve) h_mem
  omega

/-- Two-tier fiat architecture and Lender-of-Last-Resort (LOLR) bailout dichotomy:
If an individual commercial bank's custodial reserve falls short of redemption demand `q`,
autonomous redemption without external injection is infeasible.
If the central bank executes a fiduciary note issuance of base reserves with principal `ΔM > 0`,
total base money in the economy strictly expands. -/
theorem two_tier_fiat_lolr_dichotomy {W : ActionFrame}
    (bank holder : W.Agent) (t : W.Moment) (h : W.History)
    (q : ℕ) (m_dep m_reserve : W.Means)
    (h_short : bankReserve bank m_reserve t h < q)
    (cbIssue : FiduciaryNoteIssuance (W := W))
    (h_cb_money : cbIssue.money = m_reserve)
    (h_cb_moment : cbIssue.moment = t)
    (h_cb_history : cbIssue.history = h)
    (h_pos : 0 < cbIssue.principal) :
    (W.Accept bank holder q m_dep q m_reserve ∉ W.A_feas bank t h ∧
     ¬ @PurposefulAct W bank t h (W.Accept bank holder q m_dep q m_reserve)) ∧
    totalMedia cbIssue.issuer m_reserve t h <
      totalMedia cbIssue.issuer m_reserve cbIssue.nextMoment h := by
  refine ⟨bank_specific_redemption_infeasible_of_local_shortfall
    bank holder t h q m_dep m_reserve h_short, ?_⟩
  rw [← h_cb_money, ← h_cb_moment, ← h_cb_history]
  have h_inc := cbIssue.total_media_increases
  omega

/-- Commercial bank reserves partition additively across disjoint bank tiers. -/
theorem bankReserves_tier_partition {W : ActionFrame}
    (Tier₁ Tier₂ : Finset W.Agent)
    (h_disjoint : Disjoint Tier₁ Tier₂)
    (m_reserve : W.Means) (t : W.Moment) (h : W.History) :
    bankReserves (Tier₁ ∪ Tier₂) m_reserve t h =
      bankReserves Tier₁ m_reserve t h + bankReserves Tier₂ m_reserve t h := by
  unfold bankReserves
  exact Finset.sum_union h_disjoint

/-- Cross-multiplied reserve coverage divergence between two banking tiers.
If Tier 1 has a strictly higher reserve-to-deposit ratio than Tier 2, then Tier 2's
coverage ratio is strictly less than the consolidated banking system coverage ratio. -/
theorem asymmetric_tier_coverage_divergence
    (R₁ R₂ D₁ D₂ : ℕ)
    (_hD₁ : 0 < D₁) (_hD₂ : 0 < D₂)
    (h_tier_ineq : R₂ * D₁ < R₁ * D₂) :
    R₂ * (D₁ + D₂) < (R₁ + R₂) * D₂ := by
  rw [Nat.mul_add, Nat.add_mul]
  omega

/-- Localized bank run infeasibility under tier reserve asymmetry:
Even if system-wide bank reserves across all tiers cover the redemption demand `q`,
if an individual bank `b₂` in Tier 2 has insufficient local custodial reserves (`< q`),
spot redemption at bank `b₂` is resource-infeasible and non-purposeful. -/
theorem tier_asymmetric_reserve_run_infeasibility {W : ActionFrame}
    (b₂ holder : W.Agent) (t : W.Moment) (h : W.History)
    (q : ℕ) (m_dep m_reserve : W.Means)
    (h_short : bankReserve b₂ m_reserve t h < q)
    (Tier₁ Tier₂ : Finset W.Agent)
    (h_agg_suff : q ≤ bankReserves (Tier₁ ∪ Tier₂) m_reserve t h) :
    (W.Accept b₂ holder q m_dep q m_reserve ∉ W.A_feas b₂ t h ∧
     ¬ @PurposefulAct W b₂ t h (W.Accept b₂ holder q m_dep q m_reserve)) ∧
    q ≤ bankReserves (Tier₁ ∪ Tier₂) m_reserve t h := by
  refine ⟨bank_specific_redemption_infeasible_of_local_shortfall
    b₂ holder t h q m_dep m_reserve h_short, h_agg_suff⟩

/-- Automated sweep conversion vs. liquidity freeze dichotomy:
If a buyer holds insufficient money (`< price`) for a spot purchase at `t`:
(1) If a matched credit advance conversion executes at `t → t'`, transferring sufficient
    media to the buyer, spot purchase acceptance becomes feasible at `t'` (conditional on
    contemplation);
(2) If a liquidity freeze occurs (the buyer enacts `alpha_zero` at `t → t'`), the buyer's money
    endowment remains unchanged (`< price`), and spot purchase acceptance at `t'` remains
    strictly infeasible and non-purposeful. -/
theorem automated_sweep_two_step_vs_freeze_dichotomy {W : ActionFrame}
    (buyer seller : W.Agent) (t t' : W.Moment) (h : W.History)
    (qA : ℕ) (mA : W.Means) (price : ℕ) (m_money : W.Means)
    (h_succ : IsNextMoment W.Precedence W.mem_hist t t' h)
    (h_short : W.omega buyer t h m_money < price) :
    (∀ (T : PawnLoanTerms W) (A : CreditAdvance T),
      T.borrower = buyer →
      T.money = m_money →
      price ≤ W.omega buyer t h m_money + T.principal →
      A.moment = t →
      A.nextMoment = t' →
      A.history = h →
      (W.Accept buyer seller qA mA price m_money ∈ W.A_cont buyer t' h →
       W.Accept buyer seller qA mA price m_money ∈ W.A_feas buyer t' h)) ∧
    (W.enacted buyer t h = W.alpha_zero →
      W.Accept buyer seller qA mA price m_money ∉ W.A_feas buyer t' h ∧
      ¬ @PurposefulAct W buyer t' h (W.Accept buyer seller qA mA price m_money)) := by
  refine ⟨?_, ?_⟩
  · intro T A h_borrower h_money h_cov h_mom h_next h_hist h_cont
    rw [accept_spot_trade_feasible_iff]
    refine ⟨h_cont, ?_⟩
    have h_trans := A.physical_transfer.1
    rw [h_borrower, h_money, h_mom, h_next, h_hist] at h_trans
    omega
  · intro h_idle
    have h_trans := W.law_in_re_transition buyer t t' h W.alpha_zero m_money
      alpha_zero_not_trade h_idle h_succ
    rw [W.use_means_alpha_zero, W.yield_means_alpha_zero] at h_trans
    have h_short' : W.omega buyer t' h m_money < price := by omega
    exact macro_sum_underdetermines_spot_feasibility
      buyer seller t' h qA mA price m_money h_short'

/-- Standing central bank LOLR origination restores commercial bank reserve sufficiency
while strictly encumbering collateral and expanding total base money in the economy. -/
theorem standing_lolr_origination_restores_reserve_and_expands_base {W : ActionFrame}
    (bank cb : W.Agent) (m_reserve : W.Means) (q : ℕ)
    (T : PawnLoanTerms W) (I : FiduciaryIssuanceStep W) (A : CreditAdvance T)
    (O : FiduciaryOrigination T I A)
    (h_borrower : T.borrower = bank)
    (_h_issuer : I.issuer = cb)
    (h_money : I.money = m_reserve)
    (h_reserve_cov : q ≤ bankReserve bank m_reserve I.moment I.history + T.principal) :
    q ≤ bankReserve bank m_reserve A.nextMoment I.history ∧
    W.omega bank A.nextMoment I.history T.collateral + T.collateralQuantity =
      W.omega bank I.moment I.history T.collateral ∧
    totalBaseMoney m_reserve A.nextMoment I.history =
      totalBaseMoney m_reserve I.moment I.history + T.principal := by
  have h_borrower_inc := O.borrower_media_increases
  have h_T_money : T.money = m_reserve := by rw [O.money_matches, h_money]
  rw [h_borrower, h_T_money] at h_borrower_inc
  have h_res : q ≤ bankReserve bank m_reserve A.nextMoment I.history := by
    dsimp [bankReserve] at h_reserve_cov ⊢
    omega
  have h_col_dec := A.borrower_collateral_decreases
  rw [h_borrower, O.history_matches, O.advance_follows_issue] at h_col_dec
  have h_ne : bank ≠ I.issuer := by
    intro h_eq
    have h_ne_orig := O.borrower_ne_issuer
    rw [h_borrower] at h_ne_orig
    exact h_ne_orig h_eq
  have h_idle := I.otherAgentsIdle bank h_ne
  have h_step := W.law_in_re_transition bank I.moment I.nextMoment I.history
    W.alpha_zero T.collateral alpha_zero_not_trade h_idle I.successor
  rw [W.use_means_alpha_zero, W.yield_means_alpha_zero] at h_step
  have h_col : W.omega bank A.nextMoment I.history T.collateral + T.collateralQuantity =
      W.omega bank I.moment I.history T.collateral := by omega
  have h_univ_after :=
    (totalMedia_eq_universal_sum I.issuer m_reserve A.nextMoment I.history).symm
  have h_univ_before :=
    (totalMedia_eq_universal_sum I.issuer m_reserve I.moment I.history).symm
  unfold totalBaseMoney
  rw [h_univ_after, h_univ_before]
  have h_tot := O.total_media_increases
  rw [h_money] at h_tot
  refine ⟨h_res, h_col, h_tot⟩

-- Section 8: Endogenous Loan Rate Suppression from Fiduciary Expansion

/-- Contractual rate suppression lemma: when two loan contracts have equal principal,
a strictly lower total repayment amount implies a strictly lower gross repayment factor. -/
theorem loan_rate_suppression_of_repayment_lt {W : ActionFrame}
    (T₁ T₂ : PawnLoanTerms W)
    (h_principal : T₁.principal = T₂.principal)
    (h_rep : T₂.repayment < T₁.repayment) :
    T₂.grossRepaymentFactor < T₁.grossRepaymentFactor := by
  have h₁ : T₁.repayment = T₁.principal * T₁.grossRepaymentFactor := rfl
  have h₂ : T₂.repayment = T₂.principal * T₂.grossRepaymentFactor := rfl
  rw [h₁, h₂, h_principal] at h_rep
  exact Nat.lt_of_mul_lt_mul_left h_rep

/-- An offering of repayment of amount `repay` in money `m_money` requires the borrower to hold
at least `repay` units of `m_money`. If cash holdings are strictly less than `repay`, the offer
is physically infeasible and cannot be purposeful. -/
theorem offer_repayment_infeasible_of_insufficient_cash {W : ActionFrame}
    (borrower lender : W.Agent) (t : W.Moment) (h : W.History)
    (repay : ℕ) (m_money : W.Means) (coll_qty : ℕ) (m_coll : W.Means)
    (h_short : W.omega borrower t h m_money < repay) :
    W.Offer borrower lender repay m_money coll_qty m_coll ∉ W.A_feas borrower t h ∧
    ¬ @PurposefulAct W borrower t h (W.Offer borrower lender repay m_money coll_qty m_coll) := by
  constructor
  · rw [W.A_feas_coupling]
    intro ⟨_, h_all⟩
    have h_m := h_all m_money
    rw [W.use_means_offer] at h_m
    simp only [ite_true] at h_m
    omega
  · intro h_purp
    have h_feas := h_purp.1
    rw [W.A_feas_coupling] at h_feas
    have h_m := h_feas.2 m_money
    rw [W.use_means_offer] at h_m
    simp only [ite_true] at h_m
    omega

/-- Endogenous loan rate suppression theorem:
When a bank issues unbacked notes (`FiduciaryNoteIssuance`) and advances principal `P`
in a credit origination (`FiduciaryOrigination`) to a marginal borrower `b`,
if the borrower's gross project revenue at repayment moment `R.moment` is strictly less
than the repayment demanded under a natural-savings contract `T_nat` for that same principal,
then:
1. Contractual credit repayment is strictly less than natural repayment
   (`T_cred.repayment < T_nat.repayment`),
2. The gross loan rate is endogenously suppressed
   (`T_cred.grossRepaymentFactor < T_nat.grossRepaymentFactor`),
3. Total circulating/base media expands by principal `T_cred.principal`,
4. Repaying under natural terms is physically infeasible and non-purposeful for the borrower. -/
theorem endogenous_fiduciary_expansion_lowers_loan_rate {W : ActionFrame}
    (T_nat T_cred : PawnLoanTerms W)
    (I : FiduciaryNoteIssuance (W := W))
    (A_cred : CreditAdvance T_cred)
    (O : FiduciaryOrigination T_cred I A_cred)
    (R : CreditRepayment A_cred)
    (h_same_principal : T_nat.principal = T_cred.principal)
    (h_same_money : T_nat.money = T_cred.money)
    (h_marginal_shortfall :
      W.omega T_cred.borrower R.moment A_cred.history T_cred.money < T_nat.repayment) :
    T_cred.repayment < T_nat.repayment ∧
    T_cred.grossRepaymentFactor < T_nat.grossRepaymentFactor ∧
    totalMedia I.issuer I.money A_cred.nextMoment I.history =
      totalMedia I.issuer I.money I.moment I.history + T_cred.principal ∧
    W.Offer T_cred.borrower T_nat.lender T_nat.repayment T_nat.money
        T_nat.collateralQuantity T_nat.collateral ∉
      W.A_feas T_cred.borrower R.moment A_cred.history ∧
    ¬ @PurposefulAct W T_cred.borrower R.moment A_cred.history
        (W.Offer T_cred.borrower T_nat.lender T_nat.repayment T_nat.money
          T_nat.collateralQuantity T_nat.collateral) := by
  have h_dec := R.borrower_money_decreases
  have h_cov : T_cred.repayment ≤ W.omega T_cred.borrower R.moment A_cred.history T_cred.money := by
    omega
  have h_rep_lt : T_cred.repayment < T_nat.repayment :=
    lt_of_le_of_lt h_cov h_marginal_shortfall
  have h_rate_lt :=
    loan_rate_suppression_of_repayment_lt T_nat T_cred h_same_principal h_rep_lt
  have h_tot := O.total_media_increases
  have h_short_nat :
      W.omega T_cred.borrower R.moment A_cred.history T_nat.money < T_nat.repayment := by
    rw [h_same_money]
    exact h_marginal_shortfall
  have h_infeas := offer_repayment_infeasible_of_insufficient_cash
    T_cred.borrower T_nat.lender R.moment A_cred.history T_nat.repayment
    T_nat.money T_nat.collateralQuantity T_nat.collateral h_short_nat
  exact ⟨h_rep_lt, h_rate_lt, h_tot, h_infeas.1, h_infeas.2⟩

end Praxeology
