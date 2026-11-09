/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.BusinessCycle.Information

/-!
# Common Credit Shocks and Entrepreneurial Clusters

The results here are conditional. A shared observation coordinates plans only
under a shared response policy. Multiple failures require aggregate resource
or cash-buffer conditions; neither a credit shock nor a blocked project alone
implies regret.
-/

@[expose] public section

namespace Praxeology

/-- One entrepreneur's credit-financed project, funding, and purposeful action,
without an assumption that completion is later blocked. -/
structure CreditProjectEvidence (W : ActionFrame) [BilateralExchangeFrame W] (Context : Type) where
  cycle : EntrepreneurialCycleScenario W Context
  fundingRate : ℕ
  funding : EntrepreneurialCreditFunding cycle.investment.i cycle.investment.x fundingRate
  purposefulAtCreditRate : PurposefulAct cycle.investment.i cycle.investment.x.moment
    cycle.investment.x.history cycle.investment.investment
  rejectedAtNaturalRate : ¬ PurposefulAct cycle.investment.i
    cycle.investment.naturalDecision.moment cycle.investment.naturalDecision.history
    cycle.investment.investment

namespace CreditProjectEvidence

/-- Separate credit funding and purposeful choice yields an active investment choice. -/
theorem purposeful_at_credit_rate {W : ActionFrame} [BilateralExchangeFrame W] {Context : Type}
    (P : CreditProjectEvidence W Context) :
    PurposefulAct P.cycle.investment.i P.cycle.investment.x.moment
      P.cycle.investment.x.history P.cycle.investment.investment :=
  P.purposefulAtCreditRate

end CreditProjectEvidence

/-- A collateralized credit advance funded from one earlier fiduciary-note
issuance. Unlike `FiduciaryOrigination`, this allows the common note issue to
fund several loans at later moments on the same history. The cohort separately
bounds their aggregate principal by the amount issued. -/
structure FiduciaryIssueBackedAdvance {W : ActionFrame} [BilateralExchangeFrame W]
    (T : PawnLoanTerms W) (I : FiduciaryNoteIssuance (W := W))
    (A : CreditAdvance T) where
  lender_is_issuer : T.lender = I.issuer
  money_matches : T.money = I.money
  history_matches : A.history = I.history
  advance_after_issue : I.nextMoment = A.moment ∨ W.Precedence I.nextMoment A.moment
  principal_within_issue : T.principal ≤ I.principal

/-- A note-backed advance still records the borrower's actual matched
collateralized transfer. -/
theorem FiduciaryIssueBackedAdvance.borrower_receives_principal
    {W : ActionFrame} [BilateralExchangeFrame W] {T : PawnLoanTerms W}
    {I : FiduciaryNoteIssuance (W := W)} {A : CreditAdvance T}
    (_F : FiduciaryIssueBackedAdvance T I A) :
    W.omega T.borrower A.nextMoment A.history T.money =
      W.omega T.borrower A.moment A.history T.money + T.principal :=
  A.physical_transfer.1

/-- A finite cohort exposed to one common note issue and rate signal. Each
member's loan is backed by that issuance on the same history, after the notes
are issued; aggregate principal cannot exceed the amount issued. Members may
have different project terms, while the lender, observation
map, and response policy are shared. -/
structure CreditShockCohort (W : ActionFrame) [BilateralExchangeFrame W]
    (Context Entrepreneur : Type)
    [DecidableEq Entrepreneur] where
  entrepreneurs : Finset Entrepreneur
  project : Entrepreneur → CreditProjectEvidence W Context
  agent : Entrepreneur → W.Agent
  agent_injective : Set.InjOn agent entrepreneurs
  action_actor_matches_agent : ∀ e ∈ entrepreneurs,
    (project e).cycle.investment.i = agent e
  credit_borrower_matches_agent : ∀ e ∈ entrepreneurs,
    (project e).funding.terms.borrower = agent e
  commonLender : W.Agent
  commonIssuance : FiduciaryNoteIssuance (W := W)
  common_lender_is_issuer : commonIssuance.issuer = commonLender
  backedAdvance : ∀ e ∈ entrepreneurs,
    FiduciaryIssueBackedAdvance (project e).funding.terms commonIssuance
      (project e).funding.advance
  aggregate_principal_within_issue :
    entrepreneurs.sum (fun e => (project e).funding.terms.principal) ≤
      commonIssuance.principal
  commonCreditRate : ℚ
  credit_rate_shared : ∀ e ∈ entrepreneurs,
    (project e).funding.terms.grossRepaymentFactor = commonCreditRate
  rateQuotes : ∀ e, SavingCreditLoanQuotes (project e).funding.advance
  saving_borrower_matches_agent : ∀ e ∈ entrepreneurs,
    (rateQuotes e).savingTerms.borrower = agent e
  /-- The reader observes the actual Catallactics quote at each enacted
  saving-side and credit-side advance node. -/
  signalReader : W.Agent → W.DecisionIndex → CatallacticMarketSignal W.Means
  saving_signal_read : ∀ e,
    signalReader (agent e) (rateQuotes e).savingAdvance.decisionNode =
      (rateQuotes e).savingTerms.marketSignal
  credit_signal_read : ∀ e,
    signalReader (agent e) (project e).funding.advance.decisionNode =
      (project e).funding.terms.marketSignal
  naturalRate : Entrepreneur → ℚ
  credit_rate_below_natural : ∀ e ∈ entrepreneurs, commonCreditRate < naturalRate e
  /-- The baseline rate is itself an enacted Catallactics loan quote. -/
  noShockQuote : Entrepreneur → EnactedLoanQuote W
  no_shock_borrower_matches_agent : ∀ e ∈ entrepreneurs,
    (noShockQuote e).terms.borrower = agent e
  no_shock_rate_is_natural : ∀ e ∈ entrepreneurs,
    (noShockQuote e).terms.grossRepaymentFactor = naturalRate e
  no_shock_signal_read : ∀ e ∈ entrepreneurs,
    signalReader (agent e) (noShockQuote e).decisionNode =
      (noShockQuote e).marketSignal
  marketObservation : CatallacticMarketSignal W.Means → CreditObservation
  lower_rate_observation_of_rate_below_natural : ∀ e ∈ entrepreneurs,
    ∀ money rate, rate < naturalRate e →
      marketObservation (.grossRepaymentFactor money rate) = .lowerRate
  unchanged_rate_observation_at_or_above_natural : ∀ e ∈ entrepreneurs,
    ∀ money rate, naturalRate e ≤ rate →
      marketObservation (.grossRepaymentFactor money rate) = .unchangedRate
  responsePolicy : ObservationPolicy Entrepreneur CreditObservation W.Action
  credit_response_is_investment : ∀ e ∈ entrepreneurs,
    responsePolicy.choose e .lowerRate =
      (project e).cycle.investment.investment

namespace CreditShockCohort

/-- Each exposed loan's origination is recorded on one ActionFrame history:
the shared issue precedes the advance, and the advance precedes the investment
decision. No repayment outcome is part of this ordering result. -/
theorem credit_lifecycle_ordered {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    (C.commonIssuance.nextMoment =
        (C.project e).funding.advance.moment ∨
      W.Precedence C.commonIssuance.nextMoment
        (C.project e).funding.advance.moment) ∧
    W.Precedence (C.project e).funding.advance.nextMoment
      (C.project e).cycle.investment.x.moment := by
  exact ⟨(C.backedAdvance e he).advance_after_issue,
    (C.project e).funding.advancePrecedesDecision⟩

/-- If repayment is separately supplied, project completion can be ordered
before it without making successful repayment a premise of the cohort. -/
theorem credit_lifecycle_ordered_with_repayment {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (_he : e ∈ C.entrepreneurs)
    (R : CreditRepayment (C.project e).funding.advance)
    (h_project_before_repayment :
      W.Precedence (C.project e).cycle.investment.next R.moment) :
    W.Precedence (C.project e).cycle.investment.next R.moment ∧
      W.Precedence R.moment (C.project e).funding.terms.maturity := by
  exact ⟨h_project_before_repayment, R.beforeMaturity⟩

/-- The issue, project, and advance are tied to the same ActionFrame history;
later settlement evidence remains separately indexed by the advance. -/
theorem credit_lifecycle_same_history {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.commonIssuance.history =
        (C.project e).funding.advance.history ∧
    (C.project e).funding.advance.history =
        (C.project e).cycle.investment.x.history := by
  exact ⟨(C.backedAdvance e he).history_matches.symm,
    (C.project e).funding.advanceHistoryIsDecisionHistory⟩

/-- Origination changes actual ActionFrame balances: issuance adds the note
principal and the borrower receives the matched advance. This conclusion
does not depend on a later repayment outcome. -/
theorem credit_lifecycle_balance_changes {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    W.omega C.commonLender C.commonIssuance.nextMoment
        C.commonIssuance.history C.commonIssuance.money =
      W.omega C.commonLender C.commonIssuance.moment
        C.commonIssuance.history C.commonIssuance.money +
        C.commonIssuance.principal ∧
    W.omega (C.agent e) (C.project e).funding.advance.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money =
      W.omega (C.agent e) (C.project e).funding.advance.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.principal := by
  have hissue := C.commonIssuance.issuer_media_increases
  have hadvance := (C.project e).funding.advance.physical_transfer
  have hborrower : (C.project e).funding.terms.borrower = C.agent e :=
    C.credit_borrower_matches_agent e he
  refine ⟨?_, ?_⟩
  · rw [← C.common_lender_is_issuer]
    exact hissue
  · simpa only [hborrower] using hadvance.1

/-- A separately supplied matched repayment changes lender cash and returns
pledged collateral to the borrower. -/
theorem credit_lifecycle_repayment_balance_changes {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs)
    (R : CreditRepayment (C.project e).funding.advance) :
    W.omega C.commonLender R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money =
      W.omega C.commonLender R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.repayment ∧
    W.omega (C.agent e) R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral =
      W.omega (C.agent e) R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral +
        (C.project e).funding.terms.collateralQuantity := by
  have hrepayment := R.physical_transfer
  have hborrower : (C.project e).funding.terms.borrower = C.agent e :=
    C.credit_borrower_matches_agent e he
  have hlender : (C.project e).funding.terms.lender = C.commonLender := by
    exact (C.backedAdvance e he).lender_is_issuer.trans C.common_lender_is_issuer
  refine ⟨?_, ?_⟩
  · rw [← hlender]
    exact hrepayment.1
  · rw [← hborrower]
    exact hrepayment.2

/-- Full account-level cash and collateral movements for a cohort member with
separately supplied repayment evidence. This records both sides of the
issuance, advance, and repayment transfers. -/
theorem credit_lifecycle_full_transfer {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs)
    (R : CreditRepayment (C.project e).funding.advance) :
    W.omega C.commonLender C.commonIssuance.nextMoment
        C.commonIssuance.history C.commonIssuance.money =
      W.omega C.commonLender C.commonIssuance.moment
        C.commonIssuance.history C.commonIssuance.money +
        C.commonIssuance.principal ∧
    W.omega C.commonLender (C.project e).funding.advance.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.principal =
      W.omega C.commonLender (C.project e).funding.advance.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money ∧
    W.omega (C.agent e) (C.project e).funding.advance.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money =
      W.omega (C.agent e) (C.project e).funding.advance.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.principal ∧
    W.omega (C.agent e) (C.project e).funding.advance.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral +
        (C.project e).funding.terms.collateralQuantity =
      W.omega (C.agent e) (C.project e).funding.advance.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral ∧
    W.omega C.commonLender R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money =
      W.omega C.commonLender R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.repayment ∧
    W.omega (C.agent e) R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money +
        (C.project e).funding.terms.repayment =
      W.omega (C.agent e) R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.money ∧
    W.omega (C.agent e) R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral =
      W.omega (C.agent e) R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral +
        (C.project e).funding.terms.collateralQuantity ∧
    W.omega C.commonLender R.nextMoment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral +
        (C.project e).funding.terms.collateralQuantity =
      W.omega C.commonLender R.moment
        (C.project e).funding.advance.history
        (C.project e).funding.terms.collateral := by
  have hbase := C.credit_lifecycle_balance_changes he
  have hissue := C.commonIssuance.issuer_media_increases
  have hadvanceLender :=
    (C.project e).funding.advance.lender_media_decreases
  have hadvanceCollateral :=
    (C.project e).funding.advance.borrower_collateral_decreases
  have hrepaymentBorrower := R.borrower_money_decreases
  have hrepaymentLenderCollateral := R.lender_collateral_decreases
  have hborrower : (C.project e).funding.terms.borrower = C.agent e :=
    C.credit_borrower_matches_agent e he
  have hlender : (C.project e).funding.terms.lender = C.commonLender := by
    exact (C.backedAdvance e he).lender_is_issuer.trans C.common_lender_is_issuer
  have hissuer : C.commonIssuance.issuer = C.commonLender :=
    C.common_lender_is_issuer
  rcases hbase with ⟨hissueBalance, hadvanceBalance⟩
  have hsettlement := C.credit_lifecycle_repayment_balance_changes he R
  rcases hsettlement with ⟨hrepaymentBalance, hcollateralReturned⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hissuer] using hissue
  · simpa only [hlender] using hadvanceLender
  · exact hadvanceBalance
  · simpa only [hborrower] using hadvanceCollateral
  · exact hrepaymentBalance
  · simpa only [hborrower] using hrepaymentBorrower
  · exact hcollateralReturned
  · simpa only [hlender] using hrepaymentLenderCollateral

/-- Each regime's observation is read from its ActionFrame node. The no-shock
baseline is an enacted loan quote at the natural rate. -/
def observation {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    Entrepreneur → CreditRegime → CreditObservation := fun e regime =>
      match regime with
      | .genuineSaving => C.marketObservation
          (C.signalReader (C.agent e) (C.rateQuotes e).savingAdvance.decisionNode)
      | .fiduciaryExpansion =>
          C.marketObservation (C.signalReader (C.agent e)
            (C.project e).funding.advance.decisionNode)
      | .noShock => C.marketObservation
          (C.signalReader (C.agent e) (C.noShockQuote e).decisionNode)

/-- Observation-based regime knowledge is induced by the cohort's actual
ActionFrame-indexed Catallactics readings. -/
def observationKnowledge {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    KnowledgeRelation Entrepreneur CreditRegime where
  indistinguishable := fun e r s => C.observation e r = C.observation e s
  refl := by intro _ _; rfl
  symm := by intro _ _ _ h; exact h.symm
  trans := by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂

/-- If two ActionFrame-derived regime observations agree, they are
indistinguishable by that observation. -/
theorem same_observation_indistinguishable {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    (e : Entrepreneur) (r s : CreditRegime)
    (h : C.observation e r = C.observation e s) :
    C.observationKnowledge.indistinguishable e r s := h

/-- Regime nodes are the enacted saving-side quote, fiduciary-backed credit
advance, and enacted natural-rate baseline quote. -/
def regimeNode {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    (e : Entrepreneur) : CreditRegime → W.DecisionIndex
  | .genuineSaving => (C.rateQuotes e).savingAdvance.decisionNode
  | .fiduciaryExpansion => (C.project e).funding.advance.decisionNode
  | .noShock => (C.noShockQuote e).decisionNode

/-- A disclosed funding-source record distinguishes otherwise identical
market observations. The disclosure is extra evidence; equality of market
signals alone does not supply it. -/
def observationWithSourceDisclosure {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    Entrepreneur → CreditRegime →
      CatallacticMarketSignal W.Means × CreditRegime :=
  fun e regime =>
    (C.signalReader (C.agent e) (C.regimeNode e regime), regime)

def disclosedKnowledge {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    KnowledgeRelation Entrepreneur CreditRegime where
  indistinguishable := fun e r s =>
    C.observationWithSourceDisclosure e r = C.observationWithSourceDisclosure e s
  refl := by intro _ _; rfl
  symm := by intro _ _ _ h; exact h.symm
  trans := by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂

theorem source_disclosure_distinguishes_saving_and_credit
    {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) (e : Entrepreneur) :
    ¬ C.disclosedKnowledge.indistinguishable e .genuineSaving .fiduciaryExpansion := by
  intro h
  have hsource := congrArg Prod.snd h
  cases hsource

/-- Market-rate knowledge is induced by the cohort's ActionFrame-indexed
Catallactics signal reader, with no separate regime label in the observation. -/
def marketKnowledge {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    KnowledgeRelation Entrepreneur CreditRegime :=
  W.creditRegimeKnowledgeOn Entrepreneur C.agent C.regimeNode C.signalReader

/-- The shared issuer/lender is distinct from each exposed borrower, as
required by the underlying PawnLoanTerms. -/
theorem lender_distinct_from_exposed_borrower {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.commonLender ≠ C.agent e := by
  have hlender := (C.backedAdvance e he).lender_is_issuer.trans
    C.common_lender_is_issuer
  have hborrower := C.credit_borrower_matches_agent e he
  intro h
  apply (C.project e).funding.terms.distinctAgents
  exact hlender.trans (h.trans hborrower.symm)

/-- The no-shock node reads its enacted loan quote, whose factor is tied to the
natural rate; the rate classifier therefore returns the unchanged baseline. -/
theorem no_shock_observed_as_unchanged {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.observation e .noShock = .unchangedRate := by
  change C.marketObservation
    (C.signalReader (C.agent e) (C.noShockQuote e).decisionNode) = _
  rw [C.no_shock_signal_read e he]
  have hrate : C.naturalRate e ≤
      (C.noShockQuote e).terms.grossRepaymentFactor := by
    rw [C.no_shock_rate_is_natural e he]
  exact C.unchanged_rate_observation_at_or_above_natural e he
    (C.noShockQuote e).terms.money
    (C.noShockQuote e).terms.grossRepaymentFactor hrate

/-- The credit node's enacted Catallactics quote is classified as lower from
the rate comparison. -/
theorem credit_observation_is_lower_rate {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.marketObservation ((C.project e).funding.terms.marketSignal) =
      .lowerRate := by
  have hrate :
      (C.project e).funding.terms.grossRepaymentFactor <
        C.naturalRate e := by
    rw [C.credit_rate_shared e he]
    exact C.credit_rate_below_natural e he
  exact C.lower_rate_observation_of_rate_below_natural e he
    (C.project e).funding.terms.money
    (C.project e).funding.terms.grossRepaymentFactor hrate

/-- The shared Catallactic market derives equal loan-rate signals; the signal
reader then yields equal saving and credit observations at their ActionFrame
decision nodes. -/
theorem saving_and_credit_observationally_equal {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    (e : Entrepreneur) :
    C.observation e .genuineSaving =
      C.observation e .fiduciaryExpansion := by
  change C.marketObservation
      (C.signalReader (C.agent e) (C.rateQuotes e).savingAdvance.decisionNode) =
    C.marketObservation (C.signalReader (C.agent e)
      (C.project e).funding.advance.decisionNode)
  rw [C.saving_signal_read e, C.credit_signal_read e]
  exact congrArg C.marketObservation (C.rateQuotes e).same_rate_signal

/-- The saving-side and credit-side contracts have the same derived repayment
factor when their rates are quoted in the cohort's shared Catallactic market. -/
theorem saving_rate_equals_credit_rate {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) (e : Entrepreneur) :
    (C.rateQuotes e).savingTerms.grossRepaymentFactor =
      (C.project e).funding.terms.grossRepaymentFactor :=
  (C.rateQuotes e).same_gross_repayment_factor

/-- The credit node's enacted Catallactics quote is classified as the
lower-rate observation used by the shared response policy. -/
theorem credit_situation_observed_as_lower_rate {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.observation e .fiduciaryExpansion = .lowerRate := by
  change C.marketObservation (C.signalReader (C.agent e)
    (C.project e).funding.advance.decisionNode) = .lowerRate
  rw [C.credit_signal_read e]
  exact C.credit_observation_is_lower_rate he

/-- The matched saving-side contract is observed as the same lower rate. -/
theorem saving_situation_observed_as_lower_rate {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.observation e .genuineSaving = .lowerRate := by
  rw [C.saving_and_credit_observationally_equal e]
  exact C.credit_situation_observed_as_lower_rate he

/-- The no-shock node is distinguishable from the matched lower-rate saving
observation under the cohort's stated signal classifications. -/
theorem no_shock_distinguished_from_saving {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    ¬ C.observationKnowledge.indistinguishable e .genuineSaving .noShock := by
  change C.observation e .genuineSaving ≠
    C.observation e .noShock
  rw [C.saving_situation_observed_as_lower_rate he,
    C.no_shock_observed_as_unchanged he]
  decide

/-- Under the cohort's stated Catallactic clearing conditions,
the genuine-saving and fiduciary-credit quotes share the lower-rate signal,
while the enacted natural-rate baseline produces the unchanged-rate signal.
-/
theorem observation_signature {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.observation e .genuineSaving = .lowerRate ∧
      C.observation e .fiduciaryExpansion = .lowerRate ∧
      C.observation e .noShock = .unchangedRate := by
  exact ⟨C.saving_situation_observed_as_lower_rate he,
    C.credit_situation_observed_as_lower_rate he,
    C.no_shock_observed_as_unchanged he⟩

/-- In the exposed cohort, each saving-side contract's gross rate equals the
common credit rate: Catallactic clearing derives equality with the credit
loan's quoted rate. -/
theorem saving_rate_is_common_credit_rate {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    (C.rateQuotes e).savingTerms.grossRepaymentFactor = C.commonCreditRate := by
  calc
    (C.rateQuotes e).savingTerms.grossRepaymentFactor =
        (C.project e).funding.terms.grossRepaymentFactor :=
      (C.rateQuotes e).same_gross_repayment_factor
    _ = C.commonCreditRate := C.credit_rate_shared e he

/-- Since a shared Catallactic market derives the same observed rate, the
cohort's signal alone does not let an entrepreneur identify saving versus
fiduciary expansion. -/
theorem market_rate_does_not_identify_credit_regime {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) (e : Entrepreneur) :
    ¬ Knows C.observationKnowledge e .genuineSaving
      (fun regime => regime = .genuineSaving) := by
  intro hk
  have hcredit := hk .fiduciaryExpansion
    (C.saving_and_credit_observationally_equal e)
  cases hcredit

/-- Under the shared policy, the same saving and credit signal selects the
same plan. This result does not say the plan is available or enacted in the
saving regime. -/
theorem saving_signal_selects_credit_plan {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.responsePolicy.choose e
        (C.observation e .genuineSaving) =
      (C.project e).cycle.investment.investment := by
  calc
    C.responsePolicy.choose e (C.observation e .genuineSaving) =
        C.responsePolicy.choose e (C.observation e .fiduciaryExpansion) :=
      congrArg (C.responsePolicy.choose e)
        (C.saving_and_credit_observationally_equal e)
    _ = C.responsePolicy.choose e .lowerRate := by
      rw [C.credit_situation_observed_as_lower_rate he]
    _ = (C.project e).cycle.investment.investment :=
      C.credit_response_is_investment e he

/-- Each cohort member's stated credit evidence yields purposeful investment.
-/
theorem purposeful_choices {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (_he : e ∈ C.entrepreneurs) :
    PurposefulAct (C.project e).cycle.investment.i
      (C.project e).cycle.investment.x.moment
      (C.project e).cycle.investment.x.history
      (C.project e).cycle.investment.investment :=
  (C.project e).purposeful_at_credit_rate

/-- The signal comparison and the credit-regime choice evidence compose: the
shared policy selects the same investment under the saving signal, while the
credit appraisal separately establishes that investment as purposeful in the
credit scenario. This does not establish saving-regime feasibility or
execution. -/
theorem saving_signal_selects_credit_purposeful_plan {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e : Entrepreneur} (he : e ∈ C.entrepreneurs) :
    C.responsePolicy.choose e (C.observation e .genuineSaving) =
        (C.project e).cycle.investment.investment ∧
      PurposefulAct (C.project e).cycle.investment.i
        (C.project e).cycle.investment.x.moment
        (C.project e).cycle.investment.x.history
        (C.project e).cycle.investment.investment := by
  exact ⟨C.saving_signal_selects_credit_plan he, C.purposeful_choices he⟩

end CreditShockCohort

/-- If unit-demand projects share an input pool, aggregate holdings below
project count force a corresponding number of zero allocations. -/
def PositiveAllocations {Entrepreneur : Type} [DecidableEq Entrepreneur]
    (entrepreneurs : Finset Entrepreneur) (allocation : Entrepreneur → ℕ) :
    Finset Entrepreneur := entrepreneurs.filter fun e => 0 < allocation e

def ZeroAllocations {Entrepreneur : Type} [DecidableEq Entrepreneur]
    (entrepreneurs : Finset Entrepreneur) (allocation : Entrepreneur → ℕ) :
    Finset Entrepreneur := entrepreneurs.filter fun e => ¬ 0 < allocation e

/-- A finite set with at least two members contains a distinct pair. -/
theorem finset_two_distinct_of_two_le_card {α : Type}
    (s : Finset α) (hcard : 2 ≤ s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  classical
  have hpos : 0 < s.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hposErase : 0 < (s.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hposErase
  have hyErase := Finset.mem_erase.mp hy
  exact ⟨x, y, hx, hyErase.2, hyErase.1.symm⟩

/-- If supply falls `k` units short of the number of unit-demand projects,
at least `k` distinct projects receive no input. -/
theorem at_least_k_projects_unfunded
    {Entrepreneur : Type} [DecidableEq Entrepreneur]
    (entrepreneurs : Finset Entrepreneur) (allocation : Entrepreneur → ℕ)
    (supply k : ℕ)
    (h_shortfall : supply + k = entrepreneurs.card)
    (h_supply_bound : entrepreneurs.sum allocation ≤ supply) :
    (ZeroAllocations entrepreneurs allocation).card ≥ k := by
  classical
  let funded := PositiveAllocations entrepreneurs allocation
  have h_funded_sum : funded.card ≤ entrepreneurs.sum allocation := by
    calc
      funded.card = funded.sum (fun _ => 1) := by
        exact Finset.card_eq_sum_ones funded
      _ ≤ funded.sum allocation := by
        apply Finset.sum_le_sum
        intro e he
        have hp : 0 < allocation e := (Finset.mem_filter.mp he).2
        omega
      _ ≤ entrepreneurs.sum allocation := by
        dsimp [funded, PositiveAllocations]
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro e he
        by_cases hp : 0 < allocation e <;> simp [hp]
  have h_partition : funded.card +
      (ZeroAllocations entrepreneurs allocation).card = entrepreneurs.card := by
    dsimp [funded, PositiveAllocations, ZeroAllocations]
    exact Finset.card_filter_add_card_filter_not
      (s := entrepreneurs) (p := fun e => 0 < allocation e)
  omega

/-- The shortfall bound is sharp: with two unit-demand projects and one unit
of input, an allocation can leave exactly one project unfunded. This is an
allocation boundary case, not a separate economic or ActionFrame model. -/
theorem one_unit_shortfall_can_leave_exactly_one_project_unfunded :
    ∃ allocation : Fin 2 → ℕ,
      ((Finset.univ : Finset (Fin 2)).sum allocation) + 1 =
          (Finset.univ : Finset (Fin 2)).card ∧
      (ZeroAllocations (Finset.univ : Finset (Fin 2)) allocation).card = 1 := by
  let allocation : Fin 2 → ℕ := fun e => if e = 0 then 1 else 0
  refine ⟨allocation, ?_, ?_⟩
  · rw [Finset.univ_fin2]
    simp [allocation]
  · rw [Finset.univ_fin2]
    change (Finset.filter (fun e : Fin 2 => ¬ 0 < allocation e)
      ({0, 1} : Finset (Fin 2))).card = 1
    have hfilter : Finset.filter (fun e : Fin 2 => ¬ 0 < allocation e)
        ({0, 1} : Finset (Fin 2)) = {1} := by
      ext e
      fin_cases e <;> simp [allocation]
    rw [hfilter]
    simp

/-- A shared pool tied to the ActionFrame balances of a credit-exposed cohort.
The stock bound is aggregate accounting after consumer retention; unit
completion requirements turn zero allocations into blocked projects. -/
structure SharedInputShortage {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    (C : CreditShockCohort W Context Entrepreneur) where
  next : W.Moment
  history : W.History
  input : W.Means
  /-- The modeled pool is a finite set of ActionFrame owners, partitioned
  between accessible holders and consumers retaining this input. -/
  resourceActors : Finset W.Agent
  accessibleOwners : Finset W.Agent
  consumerOwners : Finset W.Agent
  resourceActors_partition : resourceActors = accessibleOwners ∪ consumerOwners
  accessible_consumer_disjoint : Disjoint accessibleOwners consumerOwners
  resourceHolder : W.Agent
  resource_holder_accessible : resourceHolder ∈ accessibleOwners
  cohort_agents_accessible : ∀ e ∈ C.entrepreneurs,
    C.agent e ∈ accessibleOwners
  grossSupply : ℕ
  gross_supply_is_inventory :
    grossSupply = resourceActors.sum (fun a => W.omega a next history input)
  consumerRetention : ℕ
  consumer_retention_is_inventory :
    consumerRetention = consumerOwners.sum (fun a => W.omega a next history input)
  accessibleSupply : ℕ
  accessible_supply_is_inventory :
    accessibleSupply = accessibleOwners.sum (fun a => W.omega a next history input)
  minimumFailures : ℕ
  cluster_size : 2 ≤ minimumFailures
  supply_shortfall : accessibleSupply + minimumFailures = C.entrepreneurs.card
  commonNext : ∀ e ∈ C.entrepreneurs,
    (C.project e).cycle.investment.next = next
  commonHistory : ∀ e ∈ C.entrepreneurs,
    (C.project e).cycle.investment.x.history = history
  commonInput : ∀ e ∈ C.entrepreneurs,
    (C.project e).cycle.investment.complementary = input
  unit_completion_demand : ∀ e ∈ C.entrepreneurs,
    W.use_means (C.project e).cycle.investment.completion input = 1

namespace SharedInputShortage

theorem accessible_after_retention {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) :
    S.accessibleSupply + S.consumerRetention = S.grossSupply := by
  rw [S.accessible_supply_is_inventory, S.consumer_retention_is_inventory,
    S.gross_supply_is_inventory, S.resourceActors_partition]
  rw [Finset.sum_union S.accessible_consumer_disjoint]

theorem aggregate_holdings_bounded {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) :
    C.entrepreneurs.sum (fun e => W.omega (C.agent e) S.next S.history S.input) ≤
      S.accessibleSupply := by
  rw [S.accessible_supply_is_inventory]
  have hsubset : C.entrepreneurs.image C.agent ⊆ S.accessibleOwners := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨e, he, rfl⟩
    exact S.cohort_agents_accessible e he
  calc
    C.entrepreneurs.sum (fun e => W.omega (C.agent e) S.next S.history S.input) =
        (C.entrepreneurs.image C.agent).sum
          (fun a => W.omega a S.next S.history S.input) := by
      exact (Finset.sum_image
        (f := fun a => W.omega a S.next S.history S.input)
        C.agent_injective).symm
    _ ≤ S.accessibleOwners.sum
        (fun a => W.omega a S.next S.history S.input) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro a ha hnot
      exact Nat.zero_le _

def allocation {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) : Entrepreneur → ℕ :=
  fun e => W.omega (C.agent e) S.next S.history S.input

def failed {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) : Finset Entrepreneur :=
  ZeroAllocations C.entrepreneurs S.allocation

theorem at_least_minimum_failures {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) : S.failed.card ≥ S.minimumFailures := by
  apply at_least_k_projects_unfunded C.entrepreneurs S.allocation
    S.accessibleSupply S.minimumFailures S.supply_shortfall
  exact S.aggregate_holdings_bounded

theorem completion_blocked {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) {e : Entrepreneur}
    (he : e ∈ S.failed) :
    (C.project e).cycle.investment.completion ∉
      W.A_feas (C.agent e) S.next S.history := by
  have hm := Finset.mem_filter.mp he
  have hzero : S.allocation e = 0 := by omega
  have hzeroCommon : W.omega (C.agent e) S.next S.history S.input = 0 := by
    change W.omega (C.agent e) S.next S.history S.input = 0 at hzero
    exact hzero
  apply infeasible_of_insufficient_endowment
    (C.agent e) S.next S.history
    (C.project e).cycle.investment.completion S.input
  change W.omega (C.agent e) S.next S.history S.input <
    W.use_means (C.project e).cycle.investment.completion S.input
  rw [hzeroCommon, S.unit_completion_demand e hm.1]
  exact Nat.zero_lt_one

/-- Shortage supplies blockage for every zero-allocation project. Contextual
regret is then derived from that project's separate safe-action, valuation,
and counterfactual-evaluation evidence. -/
theorem contextual_regret_for_failed_project
    {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) {e : Entrepreneur}
    (he : e ∈ S.failed) :
    EntrepreneurialCycleConclusion (C.project e).cycle := by
  have hblocked := S.completion_blocked he
  have hpurposeful := C.purposeful_choices (Finset.mem_filter.mp he).1
  have hblocked' : (C.project e).cycle.investment.completion ∉
      W.A_feas (C.project e).cycle.investment.i
        (C.project e).cycle.investment.next
        (C.project e).cycle.investment.x.history := by
    rw [C.action_actor_matches_agent e (Finset.mem_filter.mp he).1,
      S.commonNext e (Finset.mem_filter.mp he).1,
      S.commonHistory e (Finset.mem_filter.mp he).1]
    exact hblocked
  exact (C.project e).cycle.regret_of_blocked_completion ⟨hblocked'⟩ hpurposeful

/-- The shortage mechanism yields a finite cluster of at least
`minimumFailures` projects with proved cycle conclusions, not just a count of
projects that lack the shared input. -/
theorem contextual_regret_cluster {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) :
    ∃ projects : Finset Entrepreneur,
      projects.card ≥ S.minimumFailures ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle := by
  exact ⟨S.failed, S.at_least_minimum_failures,
    fun e he => S.contextual_regret_for_failed_project he⟩

theorem at_least_two_regretful {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] [DecidableEq W.Agent]
    {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) :
    ∃ projects : Finset Entrepreneur,
      2 ≤ projects.card ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle := by
  obtain ⟨projects, hsize, hregret⟩ := S.contextual_regret_cluster
  exact ⟨projects, le_trans S.cluster_size hsize, hregret⟩

/-- The shortage result identifies two distinct exposed entrepreneurs, hence
two different ActionFrame agents, whose projects each satisfy the cycle
conclusion. -/
theorem two_distinct_regretful_entrepreneurs {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    [DecidableEq W.Agent] {C : CreditShockCohort W Context Entrepreneur}
    (S : SharedInputShortage C) :
    ∃ e₁ e₂, e₁ ∈ C.entrepreneurs ∧ e₂ ∈ C.entrepreneurs ∧ e₁ ≠ e₂ ∧
      C.agent e₁ ≠ C.agent e₂ ∧
      EntrepreneurialCycleConclusion (C.project e₁).cycle ∧
      EntrepreneurialCycleConclusion (C.project e₂).cycle := by
  obtain ⟨e₁, e₂, he₁failed, he₂failed, hne⟩ :=
    finset_two_distinct_of_two_le_card S.failed
      (le_trans S.cluster_size S.at_least_minimum_failures)
  have he₁cohort : e₁ ∈ C.entrepreneurs := (Finset.mem_filter.mp he₁failed).1
  have he₂cohort : e₂ ∈ C.entrepreneurs := (Finset.mem_filter.mp he₂failed).1
  have hagents : C.agent e₁ ≠ C.agent e₂ := by
    intro h
    exact hne (C.agent_injective he₁cohort he₂cohort h)
  exact ⟨e₁, e₂, he₁cohort, he₂cohort, hne, hagents,
    S.contextual_regret_for_failed_project he₁failed,
    S.contextual_regret_for_failed_project he₂failed⟩

end SharedInputShortage

/-- A common factor-price response with one rising bottleneck price. -/
structure CommonFactorPriceResponse (d : ℕ) where
  preBox : FactorPriceBox d
  postBox : FactorPriceBox d
  bottleneck : Fin d
  increase : ℕ
  increase_positive : 0 < increase
  widened : PriceBoxWidening preBox postBox
  bottleneck_rule : postBox.P_sup bottleneck = preBox.P_sup bottleneck + increase
  other_prices_unchanged : ∀ k, k ≠ bottleneck →
    postBox.P_sup k = preBox.P_sup k

namespace CommonFactorPriceResponse

/-- The price response raises completion cost by the price increase times
bottleneck-factor demand. -/
theorem post_cost_eq_pre_cost_add {d : ℕ}
    (R : CommonFactorPriceResponse d) (q : Fin d → ℕ) :
    PrecautionaryCashDemand R.postBox q =
      PrecautionaryCashDemand R.preBox q + R.increase * q R.bottleneck := by
  classical
  unfold PrecautionaryCashDemand
  calc
    (∑ k : Fin d, R.postBox.P_sup k * q k) =
        ∑ k : Fin d, (R.preBox.P_sup k * q k +
          if k = R.bottleneck then R.increase * q k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = R.bottleneck
      · subst k
        rw [R.bottleneck_rule]
        simp [Nat.add_mul]
      · rw [R.other_prices_unchanged k h]
        simp [h]
    _ = (∑ k : Fin d, R.preBox.P_sup k * q k) +
        ∑ k : Fin d, if k = R.bottleneck then R.increase * q k else 0 :=
      Finset.sum_add_distrib
    _ = (∑ k : Fin d, R.preBox.P_sup k * q k) +
        R.increase * q R.bottleneck := by
      congr 1
      rw [Finset.sum_eq_single_of_mem R.bottleneck (Finset.mem_univ _)]
      · simp
      · intro k hk hne
        simp [hne]

theorem post_cost_strictly_higher {d : ℕ}
    (R : CommonFactorPriceResponse d) (q : Fin d → ℕ)
    (h_uses_factor : 0 < q R.bottleneck) :
    PrecautionaryCashDemand R.preBox q <
      PrecautionaryCashDemand R.postBox q := by
  rw [R.post_cost_eq_pre_cost_add]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos R.increase_positive h_uses_factor)

/-- The factor-price signal at the bottleneck changes when the response raises
its upper price bound by a positive amount. -/
theorem bottleneck_market_signal_changes {W : ActionFrame} [BilateralExchangeFrame W] {d : ℕ}
    (R : CommonFactorPriceResponse d) (factorOf : Fin d → W.Means) :
    R.preBox.marketSignal factorOf R.bottleneck ≠
      R.postBox.marketSignal factorOf R.bottleneck := by
  intro h
  have h_upper : R.preBox.P_sup R.bottleneck =
      R.postBox.P_sup R.bottleneck := by
    have hread := congrArg (fun signal : CatallacticMarketSignal W.Means =>
      match signal with
      | .factorPriceBounds _ _ upper => upper
      | _ => 0) h
    simpa [FactorPriceBox.marketSignal] using hread
  rw [R.bottleneck_rule] at h_upper
  have hincrease := R.increase_positive
  omega

end CommonFactorPriceResponse

/-- A cohort price squeeze tied to ActionFrame cash balances and project
completion costs. The price response is shared; project quantities, buffers,
and appraisals may differ. -/
structure PriceSqueezeCohort {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] (C : CreditShockCohort W Context Entrepreneur)
    (d : ℕ) where
  next : W.Moment
  history : W.History
  money : W.Means
  response : CommonFactorPriceResponse d
  factorOf : Fin d → W.Means
  quantity : Entrepreneur → Fin d → ℕ
  affected : Finset Entrepreneur
  affected_subset : affected ⊆ C.entrepreneurs
  prePriceNode : W.DecisionIndex
  postPriceNode : W.DecisionIndex
  pre_price_node_history : prePriceNode.history = history
  post_price_node_history : postPriceNode.history = history
  post_price_node_at_completion : postPriceNode.moment = next
  price_change_precedes_completion : W.Precedence prePriceNode.moment next
  pre_price_signal_read : ∀ e ∈ affected,
    C.signalReader (C.agent e) prePriceNode =
      response.preBox.marketSignal factorOf response.bottleneck
  post_price_signal_read : ∀ e ∈ affected,
    C.signalReader (C.agent e) postPriceNode =
      response.postBox.marketSignal factorOf response.bottleneck
  commonNext : ∀ e ∈ affected,
    (C.project e).cycle.investment.next = next
  commonHistory : ∀ e ∈ affected,
    (C.project e).cycle.investment.x.history = history
  pre_affordable : ∀ e ∈ affected,
    PrecautionaryCashDemand response.preBox (quantity e) ≤
      W.omega (C.agent e) next history money
  /-- The project's unchanged cash balance lies below the cost threshold
  obtained by adding the stated bottleneck-price increase to its pre-response
  bill. This crossing is an explicit scenario condition; a price increase by
  itself does not establish it. -/
  cash_below_price_adjusted_threshold : ∀ e ∈ affected,
    W.omega (C.agent e) next history money <
      PrecautionaryCashDemand response.preBox (quantity e) +
        response.increase * quantity e response.bottleneck
  bottleneck_used : ∀ e ∈ affected,
    0 < quantity e response.bottleneck
  completion_cost : ∀ e ∈ affected,
    W.use_means (C.project e).cycle.investment.completion money =
      PrecautionaryCashDemand response.postBox (quantity e)
  minimumFailures : ℕ
  minimum_failures_at_least_two : 2 ≤ minimumFailures
  cluster_size : minimumFailures ≤ affected.card

namespace PriceSqueezeCohort

/-- The same ActionFrame reader distinguishes the pre- and post-response
bottleneck prices. -/
theorem bottleneck_price_observable {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) {e : Entrepreneur}
    (he : e ∈ S.affected) :
    ¬ (W.marketSignalKnowledge C.signalReader).indistinguishable
      (C.agent e) S.prePriceNode S.postPriceNode := by
  apply W.different_market_signals_distinguishable
  rw [S.pre_price_signal_read e he, S.post_price_signal_read e he]
  exact S.response.bottleneck_market_signal_changes S.factorOf

theorem post_cost_unaffordable {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) {e : Entrepreneur}
    (he : e ∈ S.affected) :
    W.omega (C.agent e) S.next S.history S.money <
      PrecautionaryCashDemand S.response.postBox (S.quantity e) := by
  rw [S.response.post_cost_eq_pre_cost_add]
  exact S.cash_below_price_adjusted_threshold e he

/-- A shared price response makes every member of the specified affected set
unable to cover its completion bill; hence at least `minimumFailures` are
unaffordable. -/
theorem at_least_minimum_failures_unaffordable {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    {C : CreditShockCohort W Context Entrepreneur} {d : ℕ}
    (S : PriceSqueezeCohort C d) :
    ∃ projects : Finset Entrepreneur,
      projects.card ≥ S.minimumFailures ∧
      (∀ e ∈ projects, e ∈ S.affected) ∧
      ∀ e ∈ projects,
        W.omega (C.agent e) S.next S.history S.money <
          PrecautionaryCashDemand S.response.postBox (S.quantity e) := by
  exact ⟨S.affected, S.cluster_size, fun _ he => he,
    fun e he => S.post_cost_unaffordable he⟩

/-- A contemplated completion remains feasible when the current inventory
covers its stated cash cost and every other required input. This boundary
lemma is independent of the price-squeeze cohort, whose affected projects are
defined by having insufficient cash. The concrete sufficient-real-input
execution is recorded in `fiveProject_sufficient_real_inputs_output_sales_execute`.
-/
theorem completion_feasible_with_sufficient_current_cash
    {W : ActionFrame} [BilateralExchangeFrame W] (agent : W.Agent) (moment : W.Moment)
    (history : W.History) (money : W.Means) (completion : W.Action)
    (cashCost : ℕ)
    (h_contemplated : completion ∈ W.A_cont agent moment history)
    (h_cost : W.use_means completion money = cashCost)
    (h_cash : cashCost ≤ W.omega agent moment history money)
    (h_other_inputs : ∀ m, m ≠ money →
      W.use_means completion m ≤ W.omega agent moment history m) :
    completion ∈ W.A_feas agent moment history := by
  apply (W.A_feas_coupling agent moment history completion).2
  refine ⟨h_contemplated, ?_⟩
  intro m
  by_cases hm : m = money
  · subst m
    rw [h_cost]
    exact h_cash
  · exact h_other_inputs m hm

theorem completion_blocked {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) {e : Entrepreneur}
    (he : e ∈ S.affected) :
    (C.project e).cycle.investment.completion ∉
      W.A_feas (C.agent e) S.next S.history := by
  apply factor_completion_infeasible_of_price_box_squeeze
    S.response.postBox (S.quantity e) (C.agent e) S.next S.history
    (C.project e).cycle.investment.completion S.money
    (S.completion_cost e he)
  exact S.post_cost_unaffordable he

/-- Every affected project is blocked by the shared price response. Its
cycle's separate safe alternative and valuation evidence then yield regret.
-/
theorem contextual_regret_for_affected_project
    {W : ActionFrame} [BilateralExchangeFrame W] {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) {e : Entrepreneur}
    (he : e ∈ S.affected) :
    EntrepreneurialCycleConclusion (C.project e).cycle := by
  have hblocked := S.completion_blocked he
  have hpurposeful := C.purposeful_choices (S.affected_subset he)
  have hblocked' : (C.project e).cycle.investment.completion ∉
      W.A_feas (C.project e).cycle.investment.i
        (C.project e).cycle.investment.next
        (C.project e).cycle.investment.x.history := by
    rw [C.action_actor_matches_agent e (S.affected_subset he), S.commonNext e he,
      S.commonHistory e he]
    exact hblocked
  exact (C.project e).cycle.regret_of_blocked_completion ⟨hblocked'⟩ hpurposeful

/-- Every project in the price-squeezed group has its own contextual-regret
conclusion, so at least the affected cohort size forms a proved cluster. -/
theorem contextual_regret_cluster {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) :
    ∃ projects : Finset Entrepreneur,
      projects.card ≥ S.minimumFailures ∧
      (∀ e ∈ projects, e ∈ S.affected) ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle := by
  exact ⟨S.affected, S.cluster_size, fun _ he => he,
    fun e he => S.contextual_regret_for_affected_project he⟩

theorem at_least_two_regretful {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type}
    [DecidableEq Entrepreneur] {C : CreditShockCohort W Context Entrepreneur}
    {d : ℕ} (S : PriceSqueezeCohort C d) :
    ∃ projects : Finset Entrepreneur,
      2 ≤ projects.card ∧
      (∀ e ∈ projects, e ∈ S.affected) ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle := by
  obtain ⟨projects, hsize, haffected, hregret⟩ := S.contextual_regret_cluster
  exact ⟨projects, le_trans S.minimum_failures_at_least_two hsize,
    haffected, hregret⟩

/-- The price-squeeze result identifies two distinct exposed entrepreneurs,
hence two different ActionFrame agents, with contextual-regret conclusions.
-/
theorem two_distinct_regretful_entrepreneurs {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    {C : CreditShockCohort W Context Entrepreneur} {d : ℕ}
    (S : PriceSqueezeCohort C d) :
    ∃ e₁ e₂, e₁ ∈ C.entrepreneurs ∧ e₂ ∈ C.entrepreneurs ∧ e₁ ≠ e₂ ∧
      C.agent e₁ ≠ C.agent e₂ ∧
      EntrepreneurialCycleConclusion (C.project e₁).cycle ∧
      EntrepreneurialCycleConclusion (C.project e₂).cycle := by
  obtain ⟨projects, hsize, haffected, hregret⟩ := S.at_least_two_regretful
  obtain ⟨e₁, e₂, he₁, he₂, hne⟩ := finset_two_distinct_of_two_le_card projects hsize
  have he₁affected := haffected e₁ he₁
  have he₂affected := haffected e₂ he₂
  have he₁cohort := S.affected_subset he₁affected
  have he₂cohort := S.affected_subset he₂affected
  have hagents : C.agent e₁ ≠ C.agent e₂ := by
    intro h
    exact hne (C.agent_injective he₁cohort he₂cohort h)
  exact ⟨e₁, e₂, he₁cohort, he₂cohort, hne, hagents,
    hregret e₁ he₁, hregret e₂ he₂⟩

/-- Compositionally Self-Falsifying Cohort Forecasts (Fallacy of Composition in ABCT):
Formalizes how entrepreneurial forecasts can be individually sound under unilateral execution
yet systematically self-falsify under symmetric cohort entry:
(1) **Unilateral Pre-Box Affordability**: Under the pre-response price box `S.response.preBox`,
    every entrepreneur `e ∈ S.affected` holds sufficient cash to cover the completion factor bill
    (`PrecautionaryCashDemand S.response.preBox (S.quantity e) ≤ omega ...`);
(2) **Cohort-Induced Squeeze & Blocked Completion**: Symmetric cohort execution triggers the
    bottleneck price squeeze `S.response.postBox`, making completion strictly unaffordable and
    physically infeasible (`completion ∉ A_feas`) for all `e ∈ S.affected`;
(3) **Cluster Failure & Regret**: At least `S.minimumFailures` (≥ 2) distinct entrepreneurs
    simultaneously suffer `EntrepreneurialCycleConclusion` with derived contextual regret. -/
theorem compositionally_self_falsifying_cohort_forecasts
    {W : ActionFrame} [BilateralExchangeFrame W]
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    {C : CreditShockCohort W Context Entrepreneur} {d : ℕ}
    (S : PriceSqueezeCohort C d) :
    (∀ e ∈ S.affected,
      PrecautionaryCashDemand S.response.preBox (S.quantity e) ≤
        W.omega (C.agent e) S.next S.history S.money) ∧
    (∀ e ∈ S.affected,
      (C.project e).cycle.investment.completion ∉
        W.A_feas (C.agent e) S.next S.history) ∧
    (∃ projects : Finset Entrepreneur,
      projects.card ≥ S.minimumFailures ∧
      (∀ e ∈ projects, e ∈ S.affected) ∧
      ∀ e ∈ projects, EntrepreneurialCycleConclusion (C.project e).cycle) ∧
    (∃ e₁ e₂, e₁ ∈ C.entrepreneurs ∧ e₂ ∈ C.entrepreneurs ∧ e₁ ≠ e₂ ∧
      C.agent e₁ ≠ C.agent e₂ ∧
      EntrepreneurialCycleConclusion (C.project e₁).cycle ∧
      EntrepreneurialCycleConclusion (C.project e₂).cycle) :=
  ⟨S.pre_affordable, fun _ he => S.completion_blocked he,
    S.contextual_regret_cluster, S.two_distinct_regretful_entrepreneurs⟩

end PriceSqueezeCohort

/-- Top-level alias for `PriceSqueezeCohort.compositionally_self_falsifying_cohort_forecasts`. -/
abbrev compositionally_self_falsifying_cohort_forecasts :=
  @PriceSqueezeCohort.compositionally_self_falsifying_cohort_forecasts

/-- A blocked project alone cannot imply contextual regret: a regret witness
also requires a feasible safe alternative. -/
theorem no_contextual_regret_without_safe_feasibility
    {W : ActionFrame} {Context : Type}
    (C : ActionFrame.ContextCorrespondence W Context)
    (i : W.Agent) (x : W.DecisionIndex) (actualMaturity : W.Moment)
    (investment safeAction : W.Action)
    (h_safe : safeAction ∉ W.A_feas i x.moment x.history) :
    ¬ ContextMatchedRegret C i x actualMaturity investment safeAction := by
  rintro ⟨h_feasible, _⟩
  exact h_safe h_feasible

/-- Even a feasible safe action does not establish regret without a context in
which the alternative outcome is admitted and strictly preferred. -/
theorem no_contextual_regret_without_preferred_admitted_alternative
    {W : ActionFrame} {Context : Type}
    (C : ActionFrame.ContextCorrespondence W Context)
    (i : W.Agent) (x : W.DecisionIndex) (actualMaturity : W.Moment)
    (investment safeAction : W.Action)
    (h_no_better_admitted_alternative :
      ∀ c hAlt τAlt,
        C.compatible i x.moment x.history c →
        C.admissible i x c investment x.history actualMaturity →
        C.admissible i x c safeAction hAlt τAlt →
        ¬ W.Preference i actualMaturity x.history
          (W.OutcomeOf i safeAction x.moment τAlt hAlt)
          (W.OutcomeOf i investment x.moment actualMaturity x.history)) :
    ¬ ContextMatchedRegret C i x actualMaturity investment safeAction := by
  rintro ⟨_, c, hAlt, τAlt, hc, hactual, hsafe, hpref⟩
  exact h_no_better_admitted_alternative c hAlt τAlt hc hactual hsafe hpref

end Praxeology
