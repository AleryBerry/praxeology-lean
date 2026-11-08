/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Catallactics
public import Praxeology.EpistemicAbility

/-!
# Organization: Firms, Contracts, and Authority

This module formalizes organizational structures, employment contracts,
and authority relationships in praxeological terms.
-/

@[expose] public section


namespace Praxeology


structure DelegationVocabulary (W : ActionFrame) where
  acceptsAssignment : W.Action → W.Action → Prop
  taskInScope : W.Action → W.Action → Prop
  instructionSelectsTask : W.Action → W.Action → W.Action → Prop
  compensation : W.Action → W.Means → ℕ
  authorizesTerms : W.Action → W.Action → W.Action → Prop


structure DelegationProposal {W : ActionFrame} (V : DelegationVocabulary W) where
  principal : W.Agent
  operator : W.Agent
  decisionMoment : W.Moment
  history : W.History
  assignment : W.Action
  acceptance : W.Action
  taskScope : Finset W.Action
  compensationMeans : W.Means
  compensationQuantity : ℕ
  agents_distinct : principal ≠ operator
  decision_incident : W.mem_hist decisionMoment history
  assignment_active : assignment ≠ W.alpha_zero
  acceptance_active : acceptance ≠ W.alpha_zero
  scope_interpreted : ∀ task ∈ taskScope, V.taskInScope assignment task
  compensation_interpreted : V.compensation assignment compensationMeans = compensationQuantity
  acceptance_content : V.acceptsAssignment assignment acceptance


structure DelegationExecution {W : ActionFrame} {V : DelegationVocabulary W}
    (P : DelegationProposal V) where
  instructionMoment : W.Moment
  instruction : W.Action
  workMoment : W.Moment
  task : W.Action
  instruction_incident : W.mem_hist instructionMoment P.history
  work_incident : W.mem_hist workMoment P.history
  decision_precedes_instruction : W.Precedence P.decisionMoment instructionMoment
  instruction_precedes_work : W.Precedence instructionMoment workMoment
  instruction_active : instruction ≠ W.alpha_zero
  instruction_selects_task : V.instructionSelectsTask P.assignment instruction task
  task_active : task ≠ W.alpha_zero
  task_in_scope : task ∈ P.taskScope
  task_scope_interpreted : V.taskInScope P.assignment task


structure AcceptedDelegation {W : ActionFrame} (V : DelegationVocabulary W) where
  proposal : DelegationProposal V
  execution : DelegationExecution proposal
  principal_chooses_assignment : @PurposefulAct W proposal.principal proposal.decisionMoment
    proposal.history proposal.assignment
  principal_issues_instruction : @PurposefulAct W proposal.principal execution.instructionMoment
    proposal.history execution.instruction
  operator_accepts_assignment : @PurposefulAct W proposal.operator proposal.decisionMoment
    proposal.history proposal.acceptance
  operator_executes_task : @PurposefulAct W proposal.operator execution.workMoment
    proposal.history execution.task

/-- Accepted delegation with purposeful assignment, acceptance, instruction, and task actions. -/
def AcceptedDelegation.ofEvidence {W : ActionFrame} {V : DelegationVocabulary W}
    (P : DelegationProposal V) (X : DelegationExecution P)
    (hprincipal : @PurposefulAct W P.principal P.decisionMoment P.history P.assignment)
    (hinstruction : @PurposefulAct W P.principal X.instructionMoment P.history X.instruction)
    (haccept : @PurposefulAct W P.operator P.decisionMoment P.history P.acceptance)
    (htask : @PurposefulAct W P.operator X.workMoment P.history X.task) : AcceptedDelegation V :=
  ⟨P, X, hprincipal, hinstruction, haccept, htask⟩


def AcceptedDelegation.principal {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Agent := D.proposal.principal

def AcceptedDelegation.operator {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Agent := D.proposal.operator

def AcceptedDelegation.decisionMoment {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Moment := D.proposal.decisionMoment

def AcceptedDelegation.workMoment {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Moment := D.execution.workMoment

def AcceptedDelegation.history {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.History := D.proposal.history

def AcceptedDelegation.assignment {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Action := D.proposal.assignment

def AcceptedDelegation.acceptance {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Action := D.proposal.acceptance

def AcceptedDelegation.task {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Action := D.execution.task

theorem AcceptedDelegation.agents_distinct {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : D.principal ≠ D.operator := D.proposal.agents_distinct

theorem AcceptedDelegation.decision_incident {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) :
    W.mem_hist D.decisionMoment D.history := D.proposal.decision_incident

theorem AcceptedDelegation.work_incident {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.mem_hist D.workMoment D.history := D.execution.work_incident

def AcceptedDelegation.instructionMoment {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Moment := D.execution.instructionMoment

def AcceptedDelegation.instruction {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Action := D.execution.instruction

theorem AcceptedDelegation.instruction_incident {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.mem_hist D.instructionMoment D.history :=
  D.execution.instruction_incident

theorem AcceptedDelegation.decision_precedes_instruction {W : ActionFrame}
    {V : DelegationVocabulary W} (D : AcceptedDelegation V) :
    W.Precedence D.decisionMoment D.instructionMoment := D.execution.decision_precedes_instruction

theorem AcceptedDelegation.instruction_precedes_work {W : ActionFrame}
    {V : DelegationVocabulary W} (D : AcceptedDelegation V) :
    W.Precedence D.instructionMoment D.workMoment := D.execution.instruction_precedes_work

theorem AcceptedDelegation.decision_precedes_work {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : W.Precedence D.decisionMoment D.workMoment :=
  W.moment_lt_trans D.execution.decision_precedes_instruction D.execution.instruction_precedes_work

theorem AcceptedDelegation.assignment_active {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : D.assignment ≠ W.alpha_zero := D.proposal.assignment_active

theorem AcceptedDelegation.acceptance_active {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : D.acceptance ≠ W.alpha_zero := D.proposal.acceptance_active

theorem AcceptedDelegation.task_active {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : D.task ≠ W.alpha_zero := D.execution.task_active

theorem AcceptedDelegation.acceptance_content {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : V.acceptsAssignment D.assignment D.acceptance :=
  D.proposal.acceptance_content

theorem AcceptedDelegation.assignment_covers_task {W : ActionFrame} {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) : V.taskInScope D.assignment D.task :=
  D.execution.task_scope_interpreted

theorem AcceptedDelegation.instruction_authorizes_task {W : ActionFrame}
    {V : DelegationVocabulary W} (D : AcceptedDelegation V) :
    V.instructionSelectsTask D.assignment D.instruction D.task :=
  D.execution.instruction_selects_task

/-- The acceptance action cannot equal `alpha_zero`. -/
theorem AcceptedDelegation.refusal_is_not_acceptance {W : ActionFrame}
    {V : DelegationVocabulary W} (D : AcceptedDelegation V)
    (hrefusal : D.acceptance = W.alpha_zero) : False :=
  D.proposal.acceptance_active hrefusal

/-- Every task selected after an assignment is within its accepted scope. -/
theorem DelegationExecution.task_in_accepted_scope {W : ActionFrame}
    {V : DelegationVocabulary W} {P : DelegationProposal V}
    (X : DelegationExecution P) : X.task ∈ P.taskScope :=
  X.task_in_scope


structure DelegationCompensationEvidence {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} (P : DelegationProposal V) (X : DelegationExecution P) where
  transferMoment : W.Moment
  deliveredQuantity : ℕ
  deliveredGood : W.Means
  rawMaterial : W.Means
  operatorCapacity : W.Means
  compensationQuantity : ℕ
  compensationGood : W.Means
  transfer_incident : W.mem_hist transferMoment P.history
  work_precedes_transfer : W.Precedence X.workMoment transferMoment
  work_to_transfer_is_next : IsNextMoment W.Precedence W.mem_hist
    X.workMoment transferMoment P.history
  task_enacted : W.enacted P.operator X.workMoment P.history = X.task
  task_is_physical_production : ¬ W.IsTradeAction X.task
  recipe_goods_distinct : rawMaterial ≠ deliveredGood ∧ operatorCapacity ≠ deliveredGood ∧
    rawMaterial ≠ operatorCapacity
  task_uses_raw_material : 0 < W.use_means X.task rawMaterial
  task_uses_operator_capacity : 0 < W.use_means X.task operatorCapacity
  delivery_and_compensation_positive : 0 < deliveredQuantity ∧ 0 < compensationQuantity
  raw_material_available_at_work : W.use_means X.task rawMaterial ≤
    W.omega P.operator X.workMoment P.history rawMaterial
  capacity_available_at_work : W.use_means X.task operatorCapacity ≤
    W.omega P.operator X.workMoment P.history operatorCapacity
  no_opening_delivery_stock : W.omega P.operator X.workMoment P.history deliveredGood = 0
  task_does_not_consume_delivered_good : W.use_means X.task deliveredGood = 0
  delivered_from_task : deliveredQuantity ≤ W.yield_means X.task deliveredGood
  exchange : BilateralExchange (W := W) P.operator P.principal transferMoment P.history
    deliveredQuantity deliveredGood compensationQuantity compensationGood
  compensation_matches_contract : compensationQuantity = P.compensationQuantity ∧
    compensationGood = P.compensationMeans
  terms_authorized : V.authorizesTerms P.assignment
    (W.Offer P.operator P.principal deliveredQuantity deliveredGood
      compensationQuantity compensationGood)
    (W.Accept P.principal P.operator deliveredQuantity deliveredGood
      compensationQuantity compensationGood)


theorem DelegationCompensationEvidence.delivered_stock_from_task
    {W : ActionFrame} [BilateralExchangeFrame W] {V : DelegationVocabulary W}
    {P : DelegationProposal V} {X : DelegationExecution P}
    (E : DelegationCompensationEvidence P X) :
    E.deliveredQuantity ≤ W.omega P.operator E.transferMoment P.history E.deliveredGood := by
  have hbalance := W.law_in_re_transition P.operator X.workMoment E.transferMoment P.history
    X.task E.deliveredGood E.task_is_physical_production E.task_enacted
    E.work_to_transfer_is_next
  rw [E.task_does_not_consume_delivered_good, E.no_opening_delivery_stock,
    Nat.add_zero, Nat.zero_add] at hbalance
  rw [hbalance]
  exact E.delivered_from_task


structure DelegatedInternalTransfer {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    (D : AcceptedDelegation V) where
  transferMoment : W.Moment
  qA : ℕ
  mA : W.Means
  qB : ℕ
  mB : W.Means
  rawMaterial : W.Means
  operatorCapacity : W.Means
  transfer_incident : W.mem_hist transferMoment D.history
  work_precedes_transfer : W.Precedence D.workMoment transferMoment
  work_to_transfer_is_next : IsNextMoment W.Precedence W.mem_hist
    D.workMoment transferMoment D.history
  task_enacted : W.enacted D.operator D.workMoment D.history = D.task
  task_is_physical_production : ¬ W.IsTradeAction D.task
  recipe_goods_distinct : rawMaterial ≠ mA ∧ operatorCapacity ≠ mA ∧ rawMaterial ≠ operatorCapacity
  task_uses_raw_material : 0 < W.use_means D.task rawMaterial
  task_uses_operator_capacity : 0 < W.use_means D.task operatorCapacity
  delivery_and_compensation_positive : 0 < qA ∧ 0 < qB
  raw_material_available_at_work : W.use_means D.task rawMaterial ≤
    W.omega D.operator D.workMoment D.history rawMaterial
  capacity_available_at_work : W.use_means D.task operatorCapacity ≤
    W.omega D.operator D.workMoment D.history operatorCapacity
  no_opening_delivery_stock : W.omega D.operator D.workMoment D.history mA = 0
  task_does_not_consume_delivered_good : W.use_means D.task mA = 0
  produced_delivery : qA ≤ W.yield_means D.task mA
  delivered_stock_at_transfer : qA ≤ W.omega D.operator transferMoment D.history mA
  trade : BilateralExchange (W := W) D.operator D.principal transferMoment D.history qA mA qB mB
  compensation_settled : qB = D.proposal.compensationQuantity ∧
    mB = D.proposal.compensationMeans
  terms_authorized : V.authorizesTerms D.assignment
    (W.Offer D.operator D.principal qA mA qB mB)
    (W.Accept D.principal D.operator qA mA qB mB)

/-- The principal's post-transfer inventory includes the intermediate good
accepted from the operator. The successor moment is supplied explicitly
because an exchange at `transferMoment` changes stocks at the next moment. -/
theorem DelegatedInternalTransfer.principal_receives_delivered_good
    {W : ActionFrame} [BilateralExchangeFrame W] {V : DelegationVocabulary W}
    {D : AcceptedDelegation V} (T : DelegatedInternalTransfer D)
    (postTransfer : W.Moment)
    (h_next : IsNextMoment W.Precedence W.mem_hist T.transferMoment
      postTransfer D.history) :
    W.omega D.principal postTransfer D.history T.mA =
      W.omega D.principal T.transferMoment D.history T.mA + T.qA := by
  rcases bilateral_exchange_enacted_actions D.operator D.principal T.transferMoment
      D.history T.qA T.mA T.qB T.mB T.trade with ⟨h_offer, h_accept⟩
  have hflow := bilateral_exchange_commodity_transfers D.operator D.principal
    T.transferMoment postTransfer D.history T.qA T.mA T.qB T.mB
    T.trade.1 T.trade.2.1 h_next h_offer h_accept
  exact hflow.2.1


def DelegatedInternalTransfer.ofEvidence {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    (P : DelegationProposal V) (X : DelegationExecution P)
    (hprincipal : @PurposefulAct W P.principal P.decisionMoment P.history P.assignment)
    (hinstruction : @PurposefulAct W P.principal X.instructionMoment P.history X.instruction)
    (haccept : @PurposefulAct W P.operator P.decisionMoment P.history P.acceptance)
    (htask : @PurposefulAct W P.operator X.workMoment P.history X.task)
    (E : DelegationCompensationEvidence P X) :
    DelegatedInternalTransfer
      (AcceptedDelegation.ofEvidence P X hprincipal hinstruction haccept htask) := by
  refine ⟨E.transferMoment, E.deliveredQuantity, E.deliveredGood, E.compensationQuantity,
    E.compensationGood, E.rawMaterial, E.operatorCapacity, E.transfer_incident,
    E.work_precedes_transfer, E.work_to_transfer_is_next, E.task_enacted,
    E.task_is_physical_production, E.recipe_goods_distinct, E.task_uses_raw_material,
    E.task_uses_operator_capacity, E.delivery_and_compensation_positive,
    E.raw_material_available_at_work, E.capacity_available_at_work,
    E.no_opening_delivery_stock, E.task_does_not_consume_delivered_good,
    E.delivered_from_task, E.delivered_stock_from_task, E.exchange,
    E.compensation_matches_contract, E.terms_authorized⟩


structure MarketBargainingMeaning (W : ActionFrame) where
  independentGovernance : W.Agent → W.Agent → W.Moment → W.History → Prop
  freshlyBargained : W.Agent → W.Agent → W.Moment → W.History → ℕ → W.Means → ℕ → W.Means → Prop


inductive GovernanceCapacity where
  | principal
  | delegate
  deriving DecidableEq

/-- Authority for a decision assigned to a principal or accepted delegate. -/
structure GovernanceRole {W : ActionFrame} (V : DelegationVocabulary W) where
  actor : W.Agent
  principal : W.Agent
  capacity : GovernanceCapacity
  decision : W.Action
  authority : match capacity with
    | .principal => actor = principal
    | .delegate => ∃ D : AcceptedDelegation V,
        D.principal = principal ∧ D.operator = actor ∧ decision ∈ D.proposal.taskScope


structure IndependentMarketInterface {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) where
  seller : W.Agent
  buyer : W.Agent
  sellerPrincipal : W.Agent
  buyerPrincipal : W.Agent
  moment : W.Moment
  history : W.History
  qA : ℕ
  mA : W.Means
  qB : ℕ
  mB : W.Means
  sellerRole : GovernanceRole V
  buyerRole : GovernanceRole V
  seller_role_actor : sellerRole.actor = seller
  seller_role_principal : sellerRole.principal = sellerPrincipal
  seller_role_decision : sellerRole.decision = W.Offer seller buyer qA mA qB mB
  buyer_role_actor : buyerRole.actor = buyer
  buyer_role_principal : buyerRole.principal = buyerPrincipal
  buyer_role_decision : buyerRole.decision = W.Accept buyer seller qA mA qB mB
  exchange : BilateralExchange (W := W) seller buyer moment history qA mA qB mB
  principals_distinct : sellerPrincipal ≠ buyerPrincipal
  independently_governed : M.independentGovernance sellerPrincipal buyerPrincipal moment history


structure ObservedUnitPriceRecord {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) (observer : W.Agent) (good paymentGood : W.Means) where
  transaction : IndependentMarketInterface V M
  observer_is_party : observer = transaction.sellerPrincipal ∨
    observer = transaction.buyerPrincipal
  traded_good : transaction.mA = good
  payment_good : transaction.mB = paymentGood
  unit_quantity : transaction.qA = 1

/-- The observed unit price is the payment quantity in the matched transaction. -/
def ObservedUnitPriceRecord.price {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {observer : W.Agent} {good paymentGood : W.Means}
    (Q : ObservedUnitPriceRecord V M observer good paymentGood) : ℕ := Q.transaction.qB

/-- A registered price observation that may be named by a communication event. -/
structure UnitPriceQuoteSource {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) (good paymentGood : W.Means) where
  observer : W.Agent
  record : ObservedUnitPriceRecord V M observer good paymentGood

/-- A finite registry maps each message identifier to the source observation
whose transaction determines the quoted price. -/
structure UnitPriceQuoteRegistry {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) (good paymentGood : W.Means) where
  MessageId : Type
  [instFintypeMessageId : Fintype MessageId]
  [instDecidableEqMessageId : DecidableEq MessageId]
  source : MessageId → UnitPriceQuoteSource V M good paymentGood

/-- The protocol's send and receive actions.  Communication is physically
neutral and cannot be mistaken for a trade. -/
structure UnitPriceMessageProtocol {W : ActionFrame} (MessageId : Type) where
  send : W.Agent → W.Agent → MessageId → W.Action
  receive : W.Agent → W.Agent → MessageId → W.Action
  send_nontrade : ∀ sender recipient id, ¬ W.IsTradeAction (send sender recipient id)
  receive_nontrade : ∀ sender recipient id, ¬ W.IsTradeAction (receive sender recipient id)
  send_use_zero : ∀ sender recipient id m,
    W.use_means (send sender recipient id) m = 0
  send_yield_zero : ∀ sender recipient id m,
    W.yield_means (send sender recipient id) m = 0
  receive_use_zero : ∀ sender recipient id m,
    W.use_means (receive sender recipient id) m = 0
  receive_yield_zero : ∀ sender recipient id m,
    W.yield_means (receive sender recipient id) m = 0

/-- A quote is delivered only when its registered source transaction is
observed by a party, the source is settled, and purposeful send/receive actions
occur on the same history before the recipient's decision. -/
structure DeliveredUnitPriceRecord {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    (R : UnitPriceQuoteRegistry V M good paymentGood)
    (P : UnitPriceMessageProtocol R.MessageId) where
  messageId : R.MessageId
  source : UnitPriceQuoteSource V M good paymentGood
  source_registered : R.source messageId = source
  recipient : W.Agent
  history : W.History
  sendingMoment : W.Moment
  receiptMoment : W.Moment
  decisionMoment : W.Moment
  recipient_distinct : recipient ≠ source.observer
  source_same_history : source.record.transaction.history = history
  source_settled_before_send : W.Precedence source.record.transaction.moment sendingMoment
  delivery_successor : IsNextMoment W.Precedence W.mem_hist sendingMoment receiptMoment history
  receipt_before_decision : W.Precedence receiptMoment decisionMoment
  send_enacted : W.enacted source.observer sendingMoment history =
    P.send source.observer recipient messageId
  receive_enacted : W.enacted recipient receiptMoment history =
    P.receive source.observer recipient messageId
  send_purposeful : @PurposefulAct W source.observer sendingMoment history
    (P.send source.observer recipient messageId)
  receive_purposeful : @PurposefulAct W recipient receiptMoment history
    (P.receive source.observer recipient messageId)

/-- The delivered price is read from its registered source transaction. -/
def DeliveredUnitPriceRecord.price {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId}
    (D : DeliveredUnitPriceRecord R P) : ℕ := D.source.record.price

/-- A recipient's price envelope starts from one observed source and records
only delivered price observations thereafter. -/
structure DeliveredPriceEnvelope {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    (R : UnitPriceQuoteRegistry V M good paymentGood)
    (P : UnitPriceMessageProtocol R.MessageId) (recipient : W.Agent) where
  seed : UnitPriceQuoteSource V M good paymentGood
  delivered : List (DeliveredUnitPriceRecord R P)
  delivered_to_recipient : ∀ D ∈ delivered, D.recipient = recipient

/-- Lower endpoint computed from the witnessed source and delivered records. -/
def DeliveredPriceEnvelope.lower {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (E : DeliveredPriceEnvelope R P recipient) : ℕ :=
  E.delivered.foldr (fun D n => min D.price n) E.seed.record.price

/-- Upper endpoint computed from the witnessed source and delivered records. -/
def DeliveredPriceEnvelope.upper {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (E : DeliveredPriceEnvelope R P recipient) : ℕ :=
  E.delivered.foldr (fun D n => max D.price n) E.seed.record.price

/-- Add one actually delivered record to a recipient's quote envelope. -/
def DeliveredPriceEnvelope.extend {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (E : DeliveredPriceEnvelope R P recipient)
    (D : DeliveredUnitPriceRecord R P) (hD : D.recipient = recipient) :
    DeliveredPriceEnvelope R P recipient :=
  { seed := E.seed,
    delivered := D :: E.delivered,
    delivered_to_recipient := by
      intro D' hD'
      simp only [List.mem_cons] at hD'
      rcases hD' with rfl | hD'
      · exact hD
      · exact E.delivered_to_recipient D' hD' }

/-- Every delivered record weakly widens both sides of the price envelope. -/
theorem DeliveredPriceEnvelope.extend_widens {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {good paymentGood : W.Means}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (E : DeliveredPriceEnvelope R P recipient)
    (D : DeliveredUnitPriceRecord R P) (hD : D.recipient = recipient) :
    (E.extend D hD).lower ≤ E.lower ∧ E.upper ≤ (E.extend D hD).upper := by
  change min D.price E.lower ≤ E.lower ∧ E.upper ≤ max D.price E.upper
  exact ⟨Nat.min_le_right _ _, Nat.le_max_right _ _⟩

/-- A delivered quote strictly raises the recorded upper endpoint when its
source price exceeds the previous upper endpoint. -/
theorem DeliveredPriceEnvelope.extend_strict_upper {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means} {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (E : DeliveredPriceEnvelope R P recipient)
    (D : DeliveredUnitPriceRecord R P) (hD : D.recipient = recipient)
    (hprice : E.upper < D.price) : E.upper < (E.extend D hD).upper := by
  change E.upper < max D.price E.upper
  exact Nat.lt_of_lt_of_le hprice (Nat.le_max_left _ _)

/-- A quote is available only when the observer has a matching transaction record. -/
abbrev UnitPriceQuoteAvailability {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) (observer : W.Agent) (good paymentGood : W.Means) :=
  Option (ObservedUnitPriceRecord V M observer good paymentGood)

/-- A numeric quote can be read only from an available exchange record. -/
def observedUnitPrice? {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {observer : W.Agent} {good paymentGood : W.Means}
    (quote : UnitPriceQuoteAvailability V M observer good paymentGood) : Option ℕ :=
  quote.map ObservedUnitPriceRecord.price

/-- An unavailable quote maps to `none`. -/
theorem unavailable_quote_is_not_zero {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {observer : W.Agent} {good paymentGood : W.Means} :
    observedUnitPrice? (V := V) (M := M) (observer := observer) (good := good)
      (paymentGood := paymentGood) none ≠ some 0 := by
  intro h
  cases h

/-- A two-sided price interval is available only when both endpoints are actual unit-price
    records observed by the same principal on the same history before the decision. -/
structure ObservedUnitPriceSpread {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) (observer : W.Agent) (good paymentGood : W.Means)
    (decisionMoment : W.Moment) (history : W.History) where
  lowerRecord : ObservedUnitPriceRecord V M observer good paymentGood
  upperRecord : ObservedUnitPriceRecord V M observer good paymentGood
  lower_history : lowerRecord.transaction.history = history
  upper_history : upperRecord.transaction.history = history
  lower_precedes_decision : W.Precedence lowerRecord.transaction.moment decisionMoment
  upper_precedes_decision : W.Precedence upperRecord.transaction.moment decisionMoment
  spread : ℕ
  spreadCertified : lowerRecord.price + spread = upperRecord.price

/-- An additive quote spread certifies the order of its endpoints. -/
theorem ObservedUnitPriceSpread.ordered {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} {observer : W.Agent} {good paymentGood : W.Means}
    {decisionMoment : W.Moment} {history : W.History}
    (Q : ObservedUnitPriceSpread V M observer good paymentGood decisionMoment history) :
    Q.lowerRecord.price ≤ Q.upperRecord.price := by
  rw [← Q.spreadCertified]
  omega

/-- An unavailable quote maps to `none`. -/
theorem no_spread_endpoint_from_unavailable_quote {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {observer : W.Agent} {good paymentGood : W.Means}
    (quote : UnitPriceQuoteAvailability V M observer good paymentGood)
    (h_unavailable : quote = none) : observedUnitPrice? quote = none := by
  subst quote
  rfl

/-- The seller is the principal or an accepted delegate authorized to offer. -/
theorem IndependentMarketInterface.seller_authority {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (E : IndependentMarketInterface V M) :
    (E.sellerRole.capacity = .principal ∧ E.seller = E.sellerPrincipal) ∨
    (E.sellerRole.capacity = .delegate ∧ ∃ D : AcceptedDelegation V,
      D.principal = E.sellerPrincipal ∧ D.operator = E.seller ∧
      W.Offer E.seller E.buyer E.qA E.mA E.qB E.mB ∈ D.proposal.taskScope) := by
  cases hcapacity : E.sellerRole.capacity with
  | principal =>
      left
      have hauthority : E.sellerRole.actor = E.sellerRole.principal := by
        simpa [hcapacity] using E.sellerRole.authority
      exact ⟨rfl, E.seller_role_actor.symm.trans
        (hauthority.trans E.seller_role_principal)⟩
  | delegate =>
      right
      have hauthority : ∃ D : AcceptedDelegation V,
          D.principal = E.sellerRole.principal ∧ D.operator = E.sellerRole.actor ∧
            E.sellerRole.decision ∈ D.proposal.taskScope := by
        simpa [hcapacity] using E.sellerRole.authority
      rcases hauthority with ⟨D, hprincipal, hactor, hauthority⟩
      refine ⟨rfl, D, ?_, ?_, ?_⟩
      · exact hprincipal.trans E.seller_role_principal
      · exact hactor.trans E.seller_role_actor
      · rw [← E.seller_role_decision]
        exact hauthority

/-- The buyer is the principal or an accepted delegate authorized to accept. -/
theorem IndependentMarketInterface.buyer_authority {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (E : IndependentMarketInterface V M) :
    (E.buyerRole.capacity = .principal ∧ E.buyer = E.buyerPrincipal) ∨
    (E.buyerRole.capacity = .delegate ∧ ∃ D : AcceptedDelegation V,
      D.principal = E.buyerPrincipal ∧ D.operator = E.buyer ∧
      W.Accept E.buyer E.seller E.qA E.mA E.qB E.mB ∈ D.proposal.taskScope) := by
  cases hcapacity : E.buyerRole.capacity with
  | principal =>
      left
      have hauthority : E.buyerRole.actor = E.buyerRole.principal := by
        simpa [hcapacity] using E.buyerRole.authority
      exact ⟨rfl, E.buyer_role_actor.symm.trans
        (hauthority.trans E.buyer_role_principal)⟩
  | delegate =>
      right
      have hauthority : ∃ D : AcceptedDelegation V,
          D.principal = E.buyerRole.principal ∧ D.operator = E.buyerRole.actor ∧
            E.buyerRole.decision ∈ D.proposal.taskScope := by
        simpa [hcapacity] using E.buyerRole.authority
      rcases hauthority with ⟨D, hprincipal, hactor, hauthority⟩
      refine ⟨rfl, D, ?_, ?_, ?_⟩
      · exact hprincipal.trans E.buyer_role_principal
      · exact hactor.trans E.buyer_role_actor
      · rw [← E.buyer_role_decision]
        exact hauthority


structure FreshlyBargainedInterface {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (E : IndependentMarketInterface V M) where
  terms_freshly_bargained : M.freshlyBargained E.seller E.buyer E.moment E.history
    E.qA E.mA E.qB E.mB


structure OrganizationNetwork {W : ActionFrame} [BilateralExchangeFrame W]
    (V : DelegationVocabulary W)
    (M : MarketBargainingMeaning W) where
  Stage : Type
  [instDecidableEqStage : DecidableEq Stage]
  stages : Finset Stage
  every_stage_listed : ∀ s : Stage, s ∈ stages
  controller : Stage → W.Agent
  operator : Stage → W.Agent
  task : Stage → W.Action
  internallyDirected : Stage → Stage → Prop
  accepted_direction : ∀ {upstream downstream}, internallyDirected upstream downstream →
    AcceptedDelegation V
  direction_alignment : ∀ {upstream downstream} (h : internallyDirected upstream downstream),
    (accepted_direction h).principal = controller upstream ∧
    (accepted_direction h).principal = controller downstream ∧
    (accepted_direction h).operator = operator downstream ∧
    (accepted_direction h).task = task downstream
  marketInterface : Stage → Stage → Prop
  market_evidence : ∀ {upstream downstream}, marketInterface upstream downstream →
    IndependentMarketInterface V M
  market_alignment : ∀ {upstream downstream} (h : marketInterface upstream downstream),
    (market_evidence h).sellerPrincipal = controller upstream ∧
    (market_evidence h).buyerPrincipal = controller downstream
  interface_kinds_disjoint : ∀ upstream downstream,
    internallyDirected upstream downstream → ¬ marketInterface upstream downstream



  connected_chain_coherence : ∀ {upstream middle downstream}
    (hinternal : internallyDirected upstream middle)
    (hmarket : marketInterface middle downstream),
      (accepted_direction hinternal).history = (market_evidence hmarket).history ∧
      W.Precedence (accepted_direction hinternal).workMoment (market_evidence hmarket).moment
  internalEdges : Finset (Stage × Stage)
  internalEdges_exact : ∀ upstream downstream,
    (upstream, downstream) ∈ internalEdges ↔ internallyDirected upstream downstream
  marketEdges : Finset (Stage × Stage)
  marketEdges_exact : ∀ upstream downstream,
    (upstream, downstream) ∈ marketEdges ↔ marketInterface upstream downstream

/-- The organization retains a market boundary when an edge crosses independent governance. -/
def OrganizationNetwork.HasFirmBoundary {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (O : OrganizationNetwork V M) : Prop :=
  ∃ upstream downstream, O.marketInterface upstream downstream

/-- A network contains internal direction when at least one stage edge is governed by an
    accepted, purposeful assignment. -/
def OrganizationNetwork.HasInternalDirection {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (O : OrganizationNetwork V M) : Prop :=
  ∃ upstream downstream, O.internallyDirected upstream downstream


def OrganizationNetwork.HasFirmStructure {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (O : OrganizationNetwork V M) : Prop :=
  ∃ upstream middle downstream,
    O.internallyDirected upstream middle ∧ O.marketInterface middle downstream


def threeStageFirmNetwork {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (D : AcceptedDelegation V)
    (E : IndependentMarketInterface V M)
    (h_firm_seller : D.principal = E.sellerPrincipal)
    (h_same_history : D.history = E.history)
    (h_market_after_task : W.Precedence D.workMoment E.moment) : OrganizationNetwork V M := by
  let O : OrganizationNetwork V M := {
    Stage := Fin 3
    stages := {0, 1, 2}
    every_stage_listed := by intro s; fin_cases s <;> simp
    controller := fun s => if s = 2 then E.buyerPrincipal else D.principal
    operator := fun s => if s = 1 then D.operator else E.buyer
    task := fun s => if s = 1 then D.task else W.alpha_zero
    internallyDirected := fun upstream downstream => upstream = 0 ∧ downstream = 1
    accepted_direction := by
      intro upstream downstream hedge
      rcases hedge with ⟨rfl, rfl⟩
      exact D
    direction_alignment := by
      intro upstream downstream hedge
      rcases hedge with ⟨rfl, rfl⟩
      simp
    marketInterface := fun upstream downstream => upstream = 1 ∧ downstream = 2
    market_evidence := by
      intro upstream downstream hedge
      rcases hedge with ⟨rfl, rfl⟩
      exact E
    market_alignment := by
      intro upstream downstream hedge
      rcases hedge with ⟨rfl, rfl⟩
      simp [h_firm_seller]
    interface_kinds_disjoint := by
      intro upstream downstream hinternal hmarket
      rcases hinternal with ⟨hu0, hd1⟩
      rcases hmarket with ⟨hu1, hd2⟩
      have h01 : (0 : Fin 3) = 1 := hu0.symm.trans hu1
      exact (by decide : (0 : Fin 3) ≠ 1) h01
    connected_chain_coherence := by
      intro upstream middle downstream hinternal hmarket
      rcases hinternal with ⟨hu0, hm1⟩
      rcases hmarket with ⟨hm1', hd2⟩
      have hmiddle : middle = (1 : Fin 3) := hm1
      subst middle
      have hupstream : upstream = (0 : Fin 3) := hu0
      have hdownstream : downstream = (2 : Fin 3) := hd2
      subst upstream
      subst downstream
      exact ⟨h_same_history, h_market_after_task⟩
    internalEdges := {((0 : Fin 3), (1 : Fin 3))}
    internalEdges_exact := by
      intro upstream downstream
      fin_cases upstream <;> fin_cases downstream <;> simp
    marketEdges := {((1 : Fin 3), (2 : Fin 3))}
    marketEdges_exact := by
      intro upstream downstream
      fin_cases upstream <;> fin_cases downstream <;> simp
  }
  exact O

/-- The three-stage network has an internal edge and a market edge. -/
theorem threeStageFirmNetwork_has_firm_structure {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (D : AcceptedDelegation V) (E : IndependentMarketInterface V M)
    (h_firm_seller : D.principal = E.sellerPrincipal)
    (h_same_history : D.history = E.history)
    (h_market_after_task : W.Precedence D.workMoment E.moment) :
    (threeStageFirmNetwork D E h_firm_seller
      h_same_history h_market_after_task).HasFirmStructure := by
  simp only [OrganizationNetwork.HasFirmStructure, threeStageFirmNetwork]
  exact ⟨(0 : Fin 3), 1, 2, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- A firm structure has an internal direction and a market boundary. -/
theorem OrganizationNetwork.firm_structure_components {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (O : OrganizationNetwork V M) (h : O.HasFirmStructure) :
    O.HasInternalDirection ∧ O.HasFirmBoundary := by
  rcases h with ⟨upstream, middle, downstream, hint, hmarket⟩
  exact ⟨⟨upstream, middle, hint⟩, ⟨middle, downstream, hmarket⟩⟩

/-- A firm structure has an accepted task and a later market exchange on the same history. -/
theorem OrganizationNetwork.firm_structure_coherence {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (O : OrganizationNetwork V M) (h : O.HasFirmStructure) :
    ∃ upstream middle downstream,
      ∃ hint : O.internallyDirected upstream middle,
      ∃ hmarket : O.marketInterface middle downstream,
        (O.accepted_direction hint).history = (O.market_evidence hmarket).history ∧
        W.Precedence (O.accepted_direction hint).workMoment (O.market_evidence hmarket).moment := by
  rcases h with ⟨upstream, middle, downstream, hint, hmarket⟩
  exact ⟨upstream, middle, downstream, hint, hmarket,
    O.connected_chain_coherence hint hmarket⟩


theorem threeStageFirmNetwork_edge_counts {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (D : AcceptedDelegation V) (E : IndependentMarketInterface V M)
    (h_firm_seller : D.principal = E.sellerPrincipal)
    (h_same_history : D.history = E.history)
    (h_market_after_task : W.Precedence D.workMoment E.moment) :
    (threeStageFirmNetwork D E h_firm_seller
      h_same_history h_market_after_task).stages.card = 3 ∧
    (threeStageFirmNetwork D E h_firm_seller
      h_same_history h_market_after_task).internalEdges.card = 1 ∧
    (threeStageFirmNetwork D E h_firm_seller
      h_same_history h_market_after_task).marketEdges.card = 1 := by
  simp [threeStageFirmNetwork]


theorem threeStageFirmNetwork_edges_retain_certificates {W : ActionFrame}
    [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (D : AcceptedDelegation V) (E : IndependentMarketInterface V M)
    (h_firm_seller : D.principal = E.sellerPrincipal)
    (h_same_history : D.history = E.history)
    (h_market_after_task : W.Precedence D.workMoment E.moment) :
    (∃ hd : (threeStageFirmNetwork D E h_firm_seller
        h_same_history h_market_after_task).internallyDirected (0 : Fin 3) (1 : Fin 3),
      (threeStageFirmNetwork D E h_firm_seller
        h_same_history h_market_after_task).accepted_direction hd = D) ∧
    (∃ hm : (threeStageFirmNetwork D E h_firm_seller
        h_same_history h_market_after_task).marketInterface (1 : Fin 3) (2 : Fin 3),
      (threeStageFirmNetwork D E h_firm_seller
        h_same_history h_market_after_task).market_evidence hm = E) := by
  constructor
  · refine ⟨?_, ?_⟩
    · change (0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1
      exact ⟨rfl, rfl⟩
    · rfl
  · refine ⟨?_, ?_⟩
    · change (1 : Fin 3) = 1 ∧ (2 : Fin 3) = 2
      exact ⟨rfl, rfl⟩
    · rfl

/-- Number of market edges in the network. -/
def OrganizationNetwork.externalBoundaryCount {W : ActionFrame} [BilateralExchangeFrame W]
    {V : DelegationVocabulary W}
    {M : MarketBargainingMeaning W} (O : OrganizationNetwork V M) : ℕ :=
  O.marketEdges.card


theorem OrganizationNetwork.externalBoundaryCount_pos_iff {W : ActionFrame}
    [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (O : OrganizationNetwork V M) :
    0 < O.externalBoundaryCount ↔ O.HasFirmBoundary := by
  constructor
  · intro hcount
    obtain ⟨⟨upstream, downstream⟩, hmem⟩ := Finset.card_pos.mp hcount
    exact ⟨upstream, downstream, (O.marketEdges_exact upstream downstream).1 hmem⟩
  · rintro ⟨upstream, downstream, hedge⟩
    have hmem : (upstream, downstream) ∈ O.marketEdges :=
      (O.marketEdges_exact upstream downstream).2 hedge
    exact Finset.card_pos.mpr ⟨(upstream, downstream), hmem⟩

/-- Each market interface has a bilateral exchange. -/
theorem OrganizationNetwork.boundary_witness_exchange {W : ActionFrame}
    [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (O : OrganizationNetwork V M) {upstream downstream : O.Stage}
    (h : O.marketInterface upstream downstream) :
    BilateralExchange (W := W) (O.market_evidence h).seller (O.market_evidence h).buyer
      (O.market_evidence h).moment (O.market_evidence h).history
      (O.market_evidence h).qA (O.market_evidence h).mA
      (O.market_evidence h).qB (O.market_evidence h).mB :=
  (O.market_evidence h).exchange

/-- The interface terms satisfy `freshlyBargained`. -/
theorem FreshlyBargainedInterface.boundary_witness_has_fresh_terms {W : ActionFrame}
    [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {E : IndependentMarketInterface V M} (F : FreshlyBargainedInterface E) :
    M.freshlyBargained E.seller E.buyer E.moment E.history E.qA E.mA E.qB E.mB :=
  F.terms_freshly_bargained

/-- An internal edge has purposeful assignment, acceptance, and task actions. -/
theorem OrganizationNetwork.internal_edge_has_purposeful_direction {W : ActionFrame}
    [BilateralExchangeFrame W]
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    (O : OrganizationNetwork V M) {upstream downstream : O.Stage}
    (h : O.internallyDirected upstream downstream) :
    ∃ D : AcceptedDelegation V,
      @PurposefulAct W D.principal D.decisionMoment D.history D.assignment ∧
      @PurposefulAct W D.operator D.decisionMoment D.history D.acceptance ∧
      @PurposefulAct W D.operator D.workMoment D.history D.task := by
  let D := O.accepted_direction h
  exact ⟨D, D.principal_chooses_assignment, D.operator_accepts_assignment,
    D.operator_executes_task⟩

/-- A state-contingent policy respects an agent's information when indistinguishable decision
    indices always receive the same action. -/
def KnowledgeRespectingPolicy {V Index Act : Type}
    (K : KnowledgeRelation V Index) (i : V) (π : Index → Act) : Prop :=
  ∀ x y, K.indistinguishable i x y → π x = π y


theorem no_knowledge_respecting_policy_across_conflict
    {V Index Act : Type} (K : KnowledgeRelation V Index)
    (i : V) (π required : Index → Act) (x y : Index)
    (hxy : K.indistinguishable i x y) (h_required : required x ≠ required y) :
    ¬ (KnowledgeRespectingPolicy K i π ∧ (∀ z, π z = required z)) := by
  rintro ⟨h_respects, h_correct⟩
  apply h_required
  calc
    required x = π x := (h_correct x).symm
    _ = π y := h_respects x y hxy
    _ = required y := h_correct y


def subjectiveTradeDelegationVocabulary :
    DelegationVocabulary SubjectiveBilateralTradeActionFrame where
  acceptsAssignment := fun _ _ => False
  taskInScope := fun _ _ => False
  instructionSelectsTask := fun _ _ _ => False
  compensation := fun _ _ => 0
  authorizesTerms := fun _ _ _ => False

/-- Bargaining terms for the trade interface. -/
def subjectiveTradeBargainingMeaning :
    MarketBargainingMeaning SubjectiveBilateralTradeActionFrame where
  independentGovernance := fun a b _ _ => a ≠ b
  freshlyBargained := fun seller buyer moment history qA mA qB mB =>
    seller = tradeAgent0 ∧ buyer = tradeAgent1 ∧ moment = BilateralMoment.root ∧
    history = tradeHistory ∧ qA = 1 ∧ mA = tradeMeans0 ∧ qB = 1 ∧ mB = tradeMeans1

/-- A concrete network interpretation of the complete bilateral trade ActionFrame. -/
def subjectiveTradeBoundaryNetwork :
    OrganizationNetwork subjectiveTradeDelegationVocabulary subjectiveTradeBargainingMeaning where
  Stage := Fin 2
  stages := {0, 1}
  every_stage_listed := by intro s; fin_cases s <;> simp
  controller := fun s => s
  operator := fun s => s
  task := fun _ => ModelAction.idle
  internallyDirected := fun _ _ => False
  accepted_direction := by intro _ _ h; exact False.elim h
  direction_alignment := by intro _ _ h; exact False.elim h
  marketInterface := fun upstream downstream => upstream = 0 ∧ downstream = 1
  market_evidence := by
    intro upstream downstream h
    have hupstream : upstream = 0 := h.1
    have hdownstream : downstream = 1 := h.2
    subst upstream
    subst downstream
    exact {
      seller := tradeAgent0
      buyer := tradeAgent1
      sellerPrincipal := tradeAgent0
      buyerPrincipal := tradeAgent1
      moment := BilateralMoment.root
      history := tradeHistory
      qA := 1
      mA := tradeMeans0
      qB := 1
      mB := tradeMeans1
      sellerRole := {
        actor := tradeAgent0
        principal := tradeAgent0
        capacity := .principal
        decision := SubjectiveBilateralTradeActionFrame.Offer tradeAgent0 tradeAgent1
          1 tradeMeans0 1 tradeMeans1
        authority := rfl
      }
      buyerRole := {
        actor := tradeAgent1
        principal := tradeAgent1
        capacity := .principal
        decision := SubjectiveBilateralTradeActionFrame.Accept tradeAgent1 tradeAgent0
          1 tradeMeans0 1 tradeMeans1
        authority := rfl
      }
      seller_role_actor := rfl
      seller_role_principal := rfl
      seller_role_decision := rfl
      buyer_role_actor := rfl
      buyer_role_principal := rfl
      buyer_role_decision := rfl
      exchange := (subjective_bilateral_trade_action_frame_witness).2.1
      principals_distinct := by decide
      independently_governed := by
        change tradeAgent0 ≠ tradeAgent1
        decide
    }
  market_alignment := by
    intro upstream downstream h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  interface_kinds_disjoint := by
    intro upstream downstream h
    exact False.elim h
  connected_chain_coherence := by
    intro upstream middle downstream hinternal _hmarket
    exact False.elim hinternal
  internalEdges := ∅
  internalEdges_exact := by intro upstream downstream; simp
  marketEdges := {((0 : Fin 2), (1 : Fin 2))}
  marketEdges_exact := by
    intro upstream downstream
    fin_cases upstream <;> fin_cases downstream <;>
      simp

/-- The trade network has a market boundary and no internal edges. -/
theorem subjective_trade_frame_has_market_boundary :
    subjectiveTradeBoundaryNetwork.HasFirmBoundary ∧
    ¬ subjectiveTradeBoundaryNetwork.HasInternalDirection := by
  constructor
  · exact ⟨(0 : Fin 2), (1 : Fin 2), ⟨rfl, rfl⟩⟩
  · rintro ⟨upstream, downstream, h⟩
    exact h

/-- The market edge carries the bilateral exchange in the trade frame. -/
theorem subjective_trade_frame_boundary_is_bilateral_exchange :
    BilateralExchange (W := SubjectiveBilateralTradeActionFrame) tradeAgent0 tradeAgent1
      BilateralMoment.root tradeHistory 1 tradeMeans0 1 tradeMeans1 := by
  exact (subjectiveTradeBoundaryNetwork.market_evidence ⟨rfl, rfl⟩).exchange

end Praxeology
