/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.EpistemicAbility
public import Praxeology.Entrepreneurship

/-! 
# Credit Signals and Entrepreneurial Information

This module separates an observed signal from the regime that produced it.
Indistinguishability follows from an observation map; a shared signal alone
does not force agents to choose the same action or establish that the action
is feasible.
-/

@[expose] public section

namespace Praxeology

/-- The three regimes used in the signal-extraction comparison. -/
inductive CreditRegime where
  | genuineSaving
  | fiduciaryExpansion
  | noShock
  deriving DecidableEq

/-- Observations available to an entrepreneur in the regime comparison. -/
inductive CreditObservation where
  | unchangedRate
  | lowerRate
  | savingVerified
  | creditVerified
  deriving DecidableEq

/-- A signal read from Catallactics data. The tags keep contractual credit
rates, transaction prices, and anticipated factor-price bounds distinct. -/
inductive CatallacticMarketSignal (C : Type) where
  | grossRepaymentFactor (money : C) (factor : ℕ)
  | transactionPrice (good money : C) (quantity price : ℕ)
  | factorPriceBounds (factor : C) (lower upper : ℕ)

/-- Read market signals at ActionFrame decision nodes. Knowledge derived from
this reader is indistinguishability by the Catallactic signal available to an
agent at each node. -/
def ActionFrame.marketSignalKnowledge (W : ActionFrame)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means) :
    KnowledgeRelation W.Agent W.DecisionIndex where
  indistinguishable := fun i x y => read i x = read i y
  refl := by intro _ _; rfl
  symm := by intro _ _ _ h; exact h.symm
  trans := by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂

theorem ActionFrame.same_market_signal_indistinguishable
    (W : ActionFrame)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means)
    (i : W.Agent) (x y : W.DecisionIndex)
    (h : read i x = read i y) :
    (W.marketSignalKnowledge read).indistinguishable i x y := h

/-- Different Catallactics readings distinguish two ActionFrame decision
nodes under the signal-based knowledge relation. -/
theorem ActionFrame.different_market_signals_distinguishable
    (W : ActionFrame)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means)
    (i : W.Agent) (x y : W.DecisionIndex)
    (h : read i x ≠ read i y) :
    ¬ (W.marketSignalKnowledge read).indistinguishable i x y := h

/-- Regime knowledge derived directly from an ActionFrame-indexed
Catallactics signal reader. The regime label is not itself observable. -/
def ActionFrame.creditRegimeKnowledge (W : ActionFrame)
    (node : W.Agent → CreditRegime → W.DecisionIndex)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means) :
    KnowledgeRelation W.Agent CreditRegime where
  indistinguishable := fun i r s => read i (node i r) = read i (node i s)
  refl := by intro _ _; rfl
  symm := by intro _ _ _ h; exact h.symm
  trans := by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂

/-- Credit-regime knowledge for project labels, read through the corresponding
ActionFrame agent and decision node. -/
def ActionFrame.creditRegimeKnowledgeOn (W : ActionFrame) (Project : Type)
    (agent : Project → W.Agent)
    (node : Project → CreditRegime → W.DecisionIndex)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means) :
    KnowledgeRelation Project CreditRegime where
  indistinguishable := fun e r s => read (agent e) (node e r) = read (agent e) (node e s)
  refl := by intro _ _; rfl
  symm := by intro _ _ _ h; exact h.symm
  trans := by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂

/-- Matching Catallactics signals leave the saving and fiduciary-credit
origins unidentified from that signal alone. -/
theorem ActionFrame.same_market_signal_precludes_credit_identification
    (W : ActionFrame)
    (node : W.Agent → CreditRegime → W.DecisionIndex)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means)
    (i : W.Agent)
    (h : read i (node i .genuineSaving) =
      read i (node i .fiduciaryExpansion)) :
    ¬ Knows (W.creditRegimeKnowledge node read) i .genuineSaving
      (fun r => r = .genuineSaving) := by
  intro hk
  have hcredit := hk .fiduciaryExpansion h
  cases hcredit

/-- The project-indexed form of the same result, retaining the ActionFrame
agent and decision-node readings behind each observation. -/
theorem ActionFrame.same_market_signal_on_precludes_credit_identification
    (W : ActionFrame) (Project : Type)
    (agent : Project → W.Agent)
    (node : Project → CreditRegime → W.DecisionIndex)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means)
    (e : Project)
    (h : read (agent e) (node e .genuineSaving) =
      read (agent e) (node e .fiduciaryExpansion)) :
    ¬ Knows (W.creditRegimeKnowledgeOn Project agent node read) e .genuineSaving
      (fun r => r = .genuineSaving) := by
  intro hk
  have hcredit := hk .fiduciaryExpansion h
  cases hcredit

/-- The gross repayment factor quoted by a loan contract. -/
def PawnLoanTerms.marketSignal {W : ActionFrame} (T : PawnLoanTerms W) :
    CatallacticMarketSignal W.Means :=
  .grossRepaymentFactor T.money T.grossRepaymentFactor

/-- The factor-price interval for one good, read from an existing Catallactics
price box. `factorOf` identifies the economic good represented by each box
coordinate. -/
def FactorPriceBox.marketSignal {W : ActionFrame} {d : ℕ}
    (B : FactorPriceBox d) (factorOf : Fin d → W.Means) (k : Fin d) :
    CatallacticMarketSignal W.Means :=
  .factorPriceBounds (factorOf k) (B.P_inf k) (B.P_sup k)

/-- A loan participant's rate signal is indexed by the ActionFrame decision
node where the matched advance occurs. -/
def CreditAdvance.decisionNode {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) : W.DecisionIndex :=
  W.decisionIndex A.moment A.history A.successor.1

def CreditAdvance.borrowerMarketSignal {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    W.Agent × W.DecisionIndex × CatallacticMarketSignal W.Means :=
  (T.borrower, A.decisionNode, T.marketSignal)

/-- The lender reads the same contractual quote at the same ActionFrame node. -/
def CreditAdvance.lenderMarketSignal {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) :
    W.Agent × W.DecisionIndex × CatallacticMarketSignal W.Means :=
  (T.lender, A.decisionNode, T.marketSignal)

theorem CreditAdvance.parties_share_rate_signal {W : ActionFrame}
    {T : PawnLoanTerms W} (A : CreditAdvance T) :
    A.borrowerMarketSignal.2.2 = A.lenderMarketSignal.2.2 := rfl

/-- A loan quote backed by an actually enacted advance and repayment on an
ActionFrame history. -/
structure EnactedLoanQuote (W : ActionFrame) where
  terms : PawnLoanTerms W
  advance : CreditAdvance terms
  repayment : CreditRepayment advance

namespace EnactedLoanQuote

def decisionNode {W : ActionFrame} (Q : EnactedLoanQuote W) :
    W.DecisionIndex := Q.advance.decisionNode

def marketSignal {W : ActionFrame} (Q : EnactedLoanQuote W) :
    CatallacticMarketSignal W.Means := Q.terms.marketSignal

end EnactedLoanQuote

/-- ActionFrame evidence that a lender deliberately retained a principal-sized
balance before making an advance: refraining was purposeful, and no money was
spent between that choice and the loan. -/
structure PurposefulSavingEvidence {W : ActionFrame} {T : PawnLoanTerms W}
    (A : CreditAdvance T) where
  savingDecision : W.DecisionIndex
  same_history : savingDecision.history = A.history
  saving_choice : @PurposefulAct W T.lender savingDecision.moment
    savingDecision.history W.alpha_zero
  saved_balance_covers_principal :
    T.principal ≤ W.omega T.lender savingDecision.moment
      savingDecision.history T.money
  retainedRun : InventoryRun W T.lender A.history
    savingDecision.moment A.moment
  no_money_spent : retainedRun.totalUse T.money = 0

namespace PurposefulSavingEvidence

/-- The principal-sized balance remains available at the advance after the
purposeful saving choice and the recorded no-spending run. -/
theorem principal_available_at_advance {W : ActionFrame} {T : PawnLoanTerms W}
    {A : CreditAdvance T} (S : PurposefulSavingEvidence A) :
    T.principal ≤ W.omega T.lender A.moment A.history T.money := by
  have hsaved := S.saved_balance_covers_principal
  rw [S.same_history] at hsaved
  have hbalance := S.retainedRun.inventory_balance T.money
  rw [S.no_money_spent] at hbalance
  omega

end PurposefulSavingEvidence

/-- A clearing price is read from the executed bilateral actions at their
ActionFrame decision node. -/
def MultilateralClearingScenario.marketSignal
    [W : ActionFrame] {M : MultilateralCohortMarket W.Agent W.Means}
    (S : MultilateralClearingScenario M) :
    W.Agent × W.DecisionIndex × CatallacticMarketSignal W.Means :=
  (S.buyer, W.decisionIndex S.moment S.history S.successor.1,
    .transactionPrice M.m_good M.m_money 1 S.price)

/-- The seller's reading of the same enacted clearing price. -/
def MultilateralClearingScenario.sellerMarketSignal
    [W : ActionFrame] {M : MultilateralCohortMarket W.Agent W.Means}
    (S : MultilateralClearingScenario M) :
    W.Agent × W.DecisionIndex × CatallacticMarketSignal W.Means :=
  (S.seller, W.decisionIndex S.moment S.history S.successor.1,
    .transactionPrice M.m_good M.m_money 1 S.price)

theorem MultilateralClearingScenario.parties_share_price_signal
    [W : ActionFrame] {M : MultilateralCohortMarket W.Agent W.Means}
    (S : MultilateralClearingScenario M) :
    S.marketSignal.2.2 = S.sellerMarketSignal.2.2 := rfl

/-- Equal goods and quoted repayment factors yield the same Catallactics
signal, regardless of whether the quote arose in a saving or credit regime. -/
theorem PawnLoanTerms.same_market_signal_of_same_quote {W : ActionFrame}
    (T₁ T₂ : PawnLoanTerms W)
    (h_money : T₁.money = T₂.money)
    (h_rate : T₁.grossRepaymentFactor = T₂.grossRepaymentFactor) :
    T₁.marketSignal = T₂.marketSignal := by
  simp [PawnLoanTerms.marketSignal, h_money, h_rate]

namespace CatallacticCreditRateComparison

/-- Matching market denomination plus the derived common clearing price gives
the same Catallactic loan-rate signal. -/
theorem same_market_signal {W : ActionFrame}
    {T_saving T_credit : PawnLoanTerms W}
    (Q : CatallacticCreditRateComparison T_saving T_credit) :
    T_saving.marketSignal = T_credit.marketSignal := by
  exact PawnLoanTerms.same_market_signal_of_same_quote T_saving T_credit
    (Q.savingMoney_is_marketMoney.trans Q.creditMoney_is_marketMoney.symm)
    Q.same_gross_repayment_factor

end CatallacticCreditRateComparison

/-- If repayment offers in two circumstances are observationally the same,
and the loans have equal principal, their contractual rate signals coincide.
The offer is recovered from each executed `CreditRepayment`; injectivity of
the ActionFrame offer constructor extracts the repayment quantity. -/
theorem CreditRepayment.same_rate_signal_of_same_observed_offer
    {W : ActionFrame} {T₁ T₂ : PawnLoanTerms W}
    {A₁ : CreditAdvance T₁} {A₂ : CreditAdvance T₂}
    (R₁ : CreditRepayment A₁) (R₂ : CreditRepayment A₂)
    (h_principal : T₁.principal = T₂.principal)
    (h_observed_offer :
      W.enacted T₁.borrower R₁.moment A₁.history =
        W.enacted T₂.borrower R₂.moment A₂.history) :
    T₁.marketSignal = T₂.marketSignal := by
  have h_offer₁ := bilateral_exchange_enacted_actions T₁.borrower T₁.lender
    R₁.moment A₁.history T₁.repayment T₁.money
    T₁.collateralQuantity T₁.collateral R₁.purposefulExchange
  have h_offer₂ := bilateral_exchange_enacted_actions T₂.borrower T₂.lender
    R₂.moment A₂.history T₂.repayment T₂.money
    T₂.collateralQuantity T₂.collateral R₂.purposefulExchange
  have h_offer :
      W.Offer T₁.borrower T₁.lender T₁.repayment T₁.money
          T₁.collateralQuantity T₁.collateral =
        W.Offer T₂.borrower T₂.lender T₂.repayment T₂.money
          T₂.collateralQuantity T₂.collateral := by
    calc
      _ = W.enacted T₁.borrower R₁.moment A₁.history := h_offer₁.1.symm
      _ = W.enacted T₂.borrower R₂.moment A₂.history := h_observed_offer
      _ = _ := h_offer₂.1
  have h_params := W.offer_inj h_offer
  have h_repayment : T₁.repayment = T₂.repayment := h_params.2.2.1
  have h_money : T₁.money = T₂.money := h_params.2.2.2.1
  exact PawnLoanTerms.same_market_signal_of_same_quote T₁ T₂ h_money
    (PawnLoanTerms.same_grossRepaymentFactor_of_same_principal_and_repayment T₁ T₂
      h_principal h_repayment)

/-- Matching enacted advance and repayment offers derive equal loan
quantities. Offer injectivity recovers principal and repayment from the
ActionFrame's Catallactics events. -/
theorem CreditRepayment.same_contract_quantities_of_same_observed_contract
    {W : ActionFrame} {T₁ T₂ : PawnLoanTerms W}
    {A₁ : CreditAdvance T₁} {A₂ : CreditAdvance T₂}
    (R₁ : CreditRepayment A₁) (R₂ : CreditRepayment A₂)
    (h_advance_offer :
      W.enacted T₁.lender A₁.moment A₁.history =
        W.enacted T₂.lender A₂.moment A₂.history)
    (h_repayment_offer :
      W.enacted T₁.borrower R₁.moment A₁.history =
        W.enacted T₂.borrower R₂.moment A₂.history) :
    T₁.principal = T₂.principal ∧
      T₁.repayment = T₂.repayment ∧ T₁.money = T₂.money := by
  have h_advance₁ := bilateral_exchange_enacted_actions T₁.lender T₁.borrower
    A₁.moment A₁.history T₁.principal T₁.money
    T₁.collateralQuantity T₁.collateral A₁.purposefulExchange
  have h_advance₂ := bilateral_exchange_enacted_actions T₂.lender T₂.borrower
    A₂.moment A₂.history T₂.principal T₂.money
    T₂.collateralQuantity T₂.collateral A₂.purposefulExchange
  have h_issue_offer :
      W.Offer T₁.lender T₁.borrower T₁.principal T₁.money
          T₁.collateralQuantity T₁.collateral =
        W.Offer T₂.lender T₂.borrower T₂.principal T₂.money
          T₂.collateralQuantity T₂.collateral := by
    calc
      _ = W.enacted T₁.lender A₁.moment A₁.history := h_advance₁.1.symm
      _ = W.enacted T₂.lender A₂.moment A₂.history := h_advance_offer
      _ = _ := h_advance₂.1
  have h_principal : T₁.principal = T₂.principal :=
    (W.offer_inj h_issue_offer).2.2.1
  have h_repay₁ := bilateral_exchange_enacted_actions T₁.borrower T₁.lender
    R₁.moment A₁.history T₁.repayment T₁.money
    T₁.collateralQuantity T₁.collateral R₁.purposefulExchange
  have h_repay₂ := bilateral_exchange_enacted_actions T₂.borrower T₂.lender
    R₂.moment A₂.history T₂.repayment T₂.money
    T₂.collateralQuantity T₂.collateral R₂.purposefulExchange
  have h_repay_offer :
      W.Offer T₁.borrower T₁.lender T₁.repayment T₁.money
          T₁.collateralQuantity T₁.collateral =
        W.Offer T₂.borrower T₂.lender T₂.repayment T₂.money
          T₂.collateralQuantity T₂.collateral := by
    calc
      _ = W.enacted T₁.borrower R₁.moment A₁.history := h_repay₁.1.symm
      _ = W.enacted T₂.borrower R₂.moment A₂.history := h_repayment_offer
      _ = _ := h_repay₂.1
  have h_repay_params := W.offer_inj h_repay_offer
  exact ⟨h_principal, h_repay_params.2.2.1, h_repay_params.2.2.2.1⟩

/-- Identical enacted loan offers derive equal contractual rates: the matched
Catallactics events determine principal and repayment, and the loan accounting
identity determines the gross repayment factor. -/
theorem CreditRepayment.same_rate_of_same_observed_contract
    {W : ActionFrame} {T₁ T₂ : PawnLoanTerms W}
    {A₁ : CreditAdvance T₁} {A₂ : CreditAdvance T₂}
    (R₁ : CreditRepayment A₁) (R₂ : CreditRepayment A₂)
    (h_advance_offer :
      W.enacted T₁.lender A₁.moment A₁.history =
        W.enacted T₂.lender A₂.moment A₂.history)
    (h_repayment_offer :
      W.enacted T₁.borrower R₁.moment A₁.history =
        W.enacted T₂.borrower R₂.moment A₂.history) :
    T₁.grossRepaymentFactor = T₂.grossRepaymentFactor := by
  obtain ⟨hprincipal, hrepayment, _hmoney⟩ :=
    CreditRepayment.same_contract_quantities_of_same_observed_contract
      R₁ R₂ h_advance_offer h_repayment_offer
  exact PawnLoanTerms.same_grossRepaymentFactor_of_same_principal_and_repayment
    T₁ T₂ hprincipal hrepayment

/-- Matching enacted advance and repayment offers derive the same contractual
rate signal and money denomination. -/
theorem CreditRepayment.same_rate_signal_of_same_observed_contract
    {W : ActionFrame} {T₁ T₂ : PawnLoanTerms W}
    {A₁ : CreditAdvance T₁} {A₂ : CreditAdvance T₂}
    (R₁ : CreditRepayment A₁) (R₂ : CreditRepayment A₂)
    (h_advance_offer :
      W.enacted T₁.lender A₁.moment A₁.history =
        W.enacted T₂.lender A₂.moment A₂.history)
    (h_repayment_offer :
      W.enacted T₁.borrower R₁.moment A₁.history =
        W.enacted T₂.borrower R₂.moment A₂.history) :
    T₁.marketSignal = T₂.marketSignal := by
  obtain ⟨_hprincipal, _hrepayment, hmoney⟩ :=
    CreditRepayment.same_contract_quantities_of_same_observed_contract
      R₁ R₂ h_advance_offer h_repayment_offer
  exact PawnLoanTerms.same_market_signal_of_same_quote T₁ T₂ hmoney
    (CreditRepayment.same_rate_of_same_observed_contract
      R₁ R₂ h_advance_offer h_repayment_offer)

/-- Evidence for comparing a saving-side loan quote with a
fiduciary-credit-funded loan. Both contracts are recorded as enacted
ActionFrame exchanges. The saving-side evidence records a purposeful refrain
and retained balance, while leaving the initial source of that balance
untraced. When both situations enact the same loan offers and repayments,
Catallactics contract accounting derives equal rates. -/
structure SavingCreditLoanQuotes {W : ActionFrame}
    {T_credit : PawnLoanTerms W} (A_credit : CreditAdvance T_credit) where
  savingTerms : PawnLoanTerms W
  savingAdvance : CreditAdvance savingTerms
  savingRepayment : CreditRepayment savingAdvance
  savingEvidence : PurposefulSavingEvidence savingAdvance
  creditRepayment : CreditRepayment A_credit
  marketComparison : CatallacticCreditRateComparison savingTerms T_credit

namespace SavingCreditLoanQuotes

/-- The common Catallactic market's unique clearing price derives equal
contractual gross repayment factors for saving-funded and credit-funded loans.
The actual advances and repayments remain recorded separately in the
ActionFrame evidence above. -/
theorem same_gross_repayment_factor {W : ActionFrame}
    {T_credit : PawnLoanTerms W} {A_credit : CreditAdvance T_credit}
    (Q : SavingCreditLoanQuotes A_credit) :
    Q.savingTerms.grossRepaymentFactor = T_credit.grossRepaymentFactor :=
  Q.marketComparison.same_gross_repayment_factor

/-- The saving-side and credit-side loan terms yield the same Catallactics
signal, with the gross factor equality derived from their shared market
clearing evidence. -/
theorem same_rate_signal {W : ActionFrame} {T_credit : PawnLoanTerms W}
    {A_credit : CreditAdvance T_credit}
    (Q : SavingCreditLoanQuotes A_credit) :
    Q.savingTerms.marketSignal = T_credit.marketSignal := by
  exact Q.marketComparison.same_market_signal

end SavingCreditLoanQuotes

/-- Compose the transaction-derived rate equality with ActionFrame-indexed
observations: if the caller associates the matched transaction evidence with
the saving and fiduciary-credit nodes, the observed signal alone cannot
identify which node obtains. The theorem derives signal equality; it does not
certify the funding origin assigned to either node. -/
theorem CreditRepayment.same_observed_contract_precludes_credit_identification
    (W : ActionFrame)
    (node : W.Agent → CreditRegime → W.DecisionIndex)
    (read : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means)
    (i : W.Agent)
    {T₁ T₂ : PawnLoanTerms W}
    {A₁ : CreditAdvance T₁} {A₂ : CreditAdvance T₂}
    (R₁ : CreditRepayment A₁) (R₂ : CreditRepayment A₂)
    (h_saving_signal : read i (node i .genuineSaving) = T₁.marketSignal)
    (h_credit_signal : read i (node i .fiduciaryExpansion) = T₂.marketSignal)
    (h_advance_offer :
      W.enacted T₁.lender A₁.moment A₁.history =
        W.enacted T₂.lender A₂.moment A₂.history)
    (h_repayment_offer :
      W.enacted T₁.borrower R₁.moment A₁.history =
        W.enacted T₂.borrower R₂.moment A₂.history) :
    ¬ Knows (W.creditRegimeKnowledge node read) i .genuineSaving
      (fun r => r = .genuineSaving) := by
  apply W.same_market_signal_precludes_credit_identification node read i
  rw [h_saving_signal, h_credit_signal]
  exact CreditRepayment.same_rate_signal_of_same_observed_contract
    R₁ R₂ h_advance_offer h_repayment_offer

/-- A deterministic response policy maps an observation to a contemplated
choice. Its existence does not imply feasibility or execution. -/
structure ObservationPolicy (V Observation Choice : Type) where
  choose : V → Observation → Choice

theorem ObservationPolicy.same_observation_same_choice
    {V Observation Choice : Type}
    (π : ObservationPolicy V Observation Choice)
    (i : V) (o₁ o₂ : Observation)
    (h : o₁ = o₂) : π.choose i o₁ = π.choose i o₂ := by
  rw [h]

/-- Evidence kept separate from policy response: the policy-selected choice
may still be unavailable, or may fail to be enacted. -/
structure PolicyImplementation (V Observation Choice : Type)
    (π : ObservationPolicy V Observation Choice) where
  available : V → Observation → Choice → Prop
  enacted : V → Observation → Choice → Prop

end Praxeology
