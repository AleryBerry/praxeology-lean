/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Execution
public import Praxeology.Organization

/-!
# Finite communication compiler

Finite message rows are only a witness format. Compiling a row produces the
polymorphic `DeliveredUnitPriceRecord` from `Organization.lean`, retaining its
ActionFrame enactment, purpose, source transaction, and temporal evidence.
-/

@[expose] public section

namespace Praxeology

/-- A finite journal row for a quote delivery on a selected generated history.
The row stores finite node indices and profile actions; `instantiate` maps
those entries into the general ActionFrame delivery record. -/
structure FiniteMessageJournal {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    (S : FiniteEconomySpec W T)
    (R : UnitPriceQuoteRegistry V M good paymentGood)
    (P : UnitPriceMessageProtocol R.MessageId) where
  messageId : R.MessageId
  source : UnitPriceQuoteSource V M good paymentGood
  source_registered : R.source messageId = source
  recipient : W.Agent
  history : T.History
  sourceNode : T.Node
  sendingNode : T.Node
  receiptNode : T.Node
  decisionNode : T.Node
  recipient_distinct : recipient ≠ source.observer
  source_moment_matches : source.record.transaction.moment =
    S.presentation.moment sourceNode
  source_history_matches : source.record.transaction.history =
    S.presentation.history history
  source_settled_before_send : T.Precedence sourceNode sendingNode
  delivery_successor : IsNextMoment T.Precedence T.MemHist
    sendingNode receiptNode history
  receipt_before_decision : T.Precedence receiptNode decisionNode
  send_profile : S.actionProfile source.observer sendingNode history =
    P.send source.observer recipient messageId
  receive_profile : S.actionProfile recipient receiptNode history =
    P.receive source.observer recipient messageId
  send_purposeful : @PurposefulAct W source.observer
    (S.presentation.moment sendingNode) (S.presentation.history history)
    (P.send source.observer recipient messageId)
  receive_purposeful : @PurposefulAct W recipient
    (S.presentation.moment receiptNode) (S.presentation.history history)
    (P.receive source.observer recipient messageId)

namespace FiniteMessageJournal

/-- Instantiate a finite journal row as a general ActionFrame price-delivery
record. All economic meaning and purpose obligations remain in the generic
record; only its node indices and enacted profile actions come from the
finite scenario. -/
def instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    {S : FiniteEconomySpec W T}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId}
    (J : FiniteMessageJournal S R P) : DeliveredUnitPriceRecord R P := by
  let frame := S.presentation
  refine
    { messageId := J.messageId
      source := J.source
      source_registered := J.source_registered
      recipient := J.recipient
      history := frame.history J.history
      sendingMoment := frame.moment J.sendingNode
      receiptMoment := frame.moment J.receiptNode
      decisionMoment := frame.moment J.decisionNode
      recipient_distinct := J.recipient_distinct
      source_same_history := J.source_history_matches
      source_settled_before_send := ?_
      delivery_successor := frame.map_next_moment J.delivery_successor
      receipt_before_decision := (frame.precedence_iff _ _).2 J.receipt_before_decision
      send_enacted := ?_
      receive_enacted := ?_
      send_purposeful := J.send_purposeful
      receive_purposeful := J.receive_purposeful }
  · rw [J.source_moment_matches]
    exact (frame.precedence_iff _ _).2 J.source_settled_before_send
  · calc
      W.enacted J.source.observer (frame.moment J.sendingNode) (frame.history J.history)
          = S.actionProfile J.source.observer J.sendingNode J.history :=
            S.actionProfile_matches J.source.observer J.sendingNode J.history
              J.delivery_successor.1
      _ = P.send J.source.observer J.recipient J.messageId := J.send_profile
  · calc
      W.enacted J.recipient (frame.moment J.receiptNode) (frame.history J.history)
          = S.actionProfile J.recipient J.receiptNode J.history :=
            S.actionProfile_matches J.recipient J.receiptNode J.history
              J.delivery_successor.2.1
      _ = P.receive J.source.observer J.recipient J.messageId := J.receive_profile

/-- The compiled quote retains the registered observation's unit price. -/
theorem price_eq_source {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    {S : FiniteEconomySpec W T}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId}
    (J : FiniteMessageJournal S R P) :
    J.instantiate.price = J.source.record.price := rfl

end FiniteMessageJournal

/-- A finite quote-envelope journal contains its initial observation and all
message rows intended for one recipient. Its compiled output is the generic
ActionFrame price envelope from Organization.lean. -/
structure FiniteMessageEnvelopeJournal {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    (S : FiniteEconomySpec W T)
    (R : UnitPriceQuoteRegistry V M good paymentGood)
    (P : UnitPriceMessageProtocol R.MessageId) (recipient : W.Agent) where
  seed : UnitPriceQuoteSource V M good paymentGood
  messages : List (FiniteMessageJournal S R P)
  messages_reach_recipient : ∀ J ∈ messages, J.recipient = recipient

namespace FiniteMessageEnvelopeJournal

/-- Compile all message rows into ActionFrame delivery witnesses and assemble
the general price envelope. -/
def instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    {S : FiniteEconomySpec W T}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (J : FiniteMessageEnvelopeJournal S R P recipient) :
    DeliveredPriceEnvelope R P recipient :=
  { seed := J.seed
    delivered := J.messages.map fun row => row.instantiate
    delivered_to_recipient := by
      intro D hD
      rcases List.mem_map.mp hD with ⟨row, hrow, rfl⟩
      exact J.messages_reach_recipient row hrow }

/-- Every generated delivery retains the generic purpose, enactment, and
precedence certificate; adding it can only widen the ActionFrame envelope. -/
theorem add_widens {W : ActionFrame} {T : FiniteTreeSpec}
    {V : DelegationVocabulary W} {M : MarketBargainingMeaning W}
    {good paymentGood : W.Means}
    {S : FiniteEconomySpec W T}
    {R : UnitPriceQuoteRegistry V M good paymentGood}
    {P : UnitPriceMessageProtocol R.MessageId} {recipient : W.Agent}
    (J : FiniteMessageEnvelopeJournal S R P recipient)
    (row : FiniteMessageJournal S R P)
    (hrecipient : row.recipient = recipient) :
    (J.instantiate.extend row.instantiate hrecipient).lower ≤ J.instantiate.lower ∧
      J.instantiate.upper ≤ (J.instantiate.extend row.instantiate hrecipient).upper :=
  J.instantiate.extend_widens row.instantiate hrecipient

end FiniteMessageEnvelopeJournal

end Praxeology

end
