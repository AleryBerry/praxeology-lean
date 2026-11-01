/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Catallactics.Credit
public import Praxeology.FiniteEconomy.Execution

/-!
# Finite banking compiler

Finite banking rows compile into the polymorphic issuance and origination
certificates in `Catallactics/Credit.lean`. Balance-sheet results continue to
follow from ActionFrame inventory and purposeful-exchange laws.
-/

@[expose] public section

namespace Praxeology

/-- Finite profile evidence for one purposeful note-printing transition. -/
structure FiniteFiduciaryIssueRow {W : ActionFrame} {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) where
  issuer : W.Agent
  history : T.History
  node : T.Node
  nextNode : T.Node
  money : W.Means
  reserve : W.Means
  principal : ℕ
  action : W.Action
  successor : IsNextMoment T.Precedence T.MemHist node nextNode history
  distinctGoods : money ≠ reserve
  principalPositive : 0 < principal
  action_profile : S.actionProfile issuer node history = action
  purposeful : @PurposefulAct W issuer (S.presentation.moment node)
    (S.presentation.history history) action
  nontrade : ¬ W.IsTradeAction action
  moneyInputZero : W.use_means action money = 0
  moneyOutput : W.yield_means action money = principal
  reserveInputZero : W.use_means action reserve = 0
  reserveOutputZero : W.yield_means action reserve = 0
  otherAgentsIdle : ∀ a, a ≠ issuer →
    S.actionProfile a node history = W.alpha_zero

namespace FiniteFiduciaryIssueRow

/-- Instantiate the row as a general ActionFrame issuance certificate. -/
def instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} (J : FiniteFiduciaryIssueRow S) :
    FiduciaryNoteIssuance (W := W) := by
  let frame := S.presentation
  refine
    { issuer := J.issuer
      history := frame.history J.history
      moment := frame.moment J.node
      nextMoment := frame.moment J.nextNode
      money := J.money
      reserve := J.reserve
      principal := J.principal
      action := J.action
      successor := frame.map_next_moment J.successor
      distinctGoods := J.distinctGoods
      principalPositive := J.principalPositive
      enacted := ?_
      purposeful := J.purposeful
      nontrade := J.nontrade
      moneyInputZero := J.moneyInputZero
      moneyOutput := J.moneyOutput
      reserveInputZero := J.reserveInputZero
      reserveOutputZero := J.reserveOutputZero
      otherAgentsIdle := ?_ }
  · calc
      W.enacted J.issuer (frame.moment J.node) (frame.history J.history)
          = S.actionProfile J.issuer J.node J.history :=
            S.actionProfile_matches J.issuer J.node J.history J.successor.1
      _ = J.action := J.action_profile
  · intro a ha
    calc
      W.enacted a (frame.moment J.node) (frame.history J.history)
          = S.actionProfile a J.node J.history :=
            S.actionProfile_matches a J.node J.history J.successor.1
      _ = W.alpha_zero := J.otherAgentsIdle a ha

end FiniteFiduciaryIssueRow

/-- Finite profile evidence for a purposeful collateralized advance. The
compiler constructs the generic `CreditAdvance` using ActionFrame Offer and
Accept primitives. -/
structure FiniteCreditAdvanceRow {W : ActionFrame} {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) (terms : PawnLoanTerms W) where
  history : T.History
  node : T.Node
  nextNode : T.Node
  successor : IsNextMoment T.Precedence T.MemHist node nextNode history
  purposefulOffer : @PurposefulAct W terms.lender (S.presentation.moment node)
    (S.presentation.history history)
    (W.Offer terms.lender terms.borrower terms.principal terms.money
      terms.collateralQuantity terms.collateral)
  offer_nonzero : W.Offer terms.lender terms.borrower terms.principal terms.money
    terms.collateralQuantity terms.collateral ≠ W.alpha_zero
  purposefulAccept : @PurposefulAct W terms.borrower (S.presentation.moment node)
    (S.presentation.history history)
    (W.Accept terms.borrower terms.lender terms.principal terms.money
      terms.collateralQuantity terms.collateral)
  accept_nonzero : W.Accept terms.borrower terms.lender terms.principal terms.money
    terms.collateralQuantity terms.collateral ≠ W.alpha_zero

namespace FiniteCreditAdvanceRow

/-- Compile a finite event row into the generic purposeful credit advance. -/
def instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} {terms : PawnLoanTerms W}
    (J : FiniteCreditAdvanceRow S terms) : CreditAdvance terms :=
  { history := S.presentation.history J.history
    moment := S.presentation.moment J.node
    nextMoment := S.presentation.moment J.nextNode
    successor := S.presentation.map_next_moment J.successor
    purposefulExchange :=
      ⟨terms.distinctAgents, terms.distinctGoods,
        ⟨terms.distinctAgents, J.purposefulOffer, J.offer_nonzero,
          J.purposefulAccept, J.accept_nonzero⟩⟩ }

end FiniteCreditAdvanceRow

/-- Finite data tying a compiled note issue to a general purposeful credit
advance and its generic origination certificate. -/
structure FiniteFiduciaryOriginationRow {W : ActionFrame} {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) where
  terms : PawnLoanTerms W
  issue : FiniteFiduciaryIssueRow S
  advance : FiniteCreditAdvanceRow S terms
  lender_is_issuer : terms.lender = issue.issuer
  money_matches : terms.money = issue.money
  principal_matches : terms.principal = issue.principal
  history_matches : advance.history = issue.history
  advance_follows_issue : advance.node = issue.nextNode
  nonparticipants_idle : ∀ a, a ≠ terms.lender → a ≠ terms.borrower →
    W.enacted a (S.presentation.moment advance.node)
      (S.presentation.history advance.history) = W.alpha_zero

namespace FiniteFiduciaryOriginationRow

/-- Compile finite issue/advance evidence into the general origination type. -/
theorem instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} (J : FiniteFiduciaryOriginationRow S) :
    FiduciaryOrigination J.terms J.issue.instantiate J.advance.instantiate := by
  refine
    { lender_is_issuer := J.lender_is_issuer
      money_matches := J.money_matches
      principal_matches := J.principal_matches
      history_matches := ?_
      advance_follows_issue := ?_
      nonparticipants_idle := J.nonparticipants_idle }
  · change S.presentation.history J.advance.history =
      S.presentation.history J.issue.history
    exact congrArg S.presentation.history J.history_matches
  · change S.presentation.moment J.advance.node =
      S.presentation.moment J.issue.nextNode
    exact congrArg S.presentation.moment J.advance_follows_issue

/-- The compiler emits the generic bank-ledger event consumed by the
ActionFrame-polymorphic balance-sheet accounting theorems. -/
def bankEvent {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} (J : FiniteFiduciaryOriginationRow S) :
    FiduciaryBankEvent W :=
  { terms := J.terms
    issuance := J.issue.instantiate
    advance := J.advance.instantiate
    origination := J.instantiate }

end FiniteFiduciaryOriginationRow

/-- An ordered journal of compiled issue/advance rows. List order records the
book's insertion sequence; each row compiles to one event in the generic
ActionFrame ledger. -/
structure FiniteFiduciaryBankJournal {W : ActionFrame} {T : FiniteTreeSpec}
    (S : FiniteEconomySpec W T) where
  entries : List (FiniteFiduciaryOriginationRow S)

namespace FiniteFiduciaryBankJournal

/-- Compile all rows into the ActionFrame-polymorphic bank ledger. -/
def instantiate {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} (J : FiniteFiduciaryBankJournal S) :
    FiduciaryBankLedger W :=
  ⟨J.entries.map FiniteFiduciaryOriginationRow.bankEvent⟩

/-- Generated balance-sheet totals inherit the generic ledger identity. -/
theorem loanAssets_eq_externalNoteLiability {W : ActionFrame} {T : FiniteTreeSpec}
    {S : FiniteEconomySpec W T} (J : FiniteFiduciaryBankJournal S) :
    J.instantiate.loanAssets = J.instantiate.externalNoteLiability :=
  J.instantiate.loanAssets_eq_externalNoteLiability

end FiniteFiduciaryBankJournal

end Praxeology

end
