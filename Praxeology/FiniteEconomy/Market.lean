/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Catallactics
public import Praxeology.FiniteEconomy.Execution

/-!
# Finite purposeful market compiler

Finite reservation rows provide an executable scan over candidate buyer and
seller pairs. Each row is anchored in an ActionFrame preference bracket and
observed cash balance. A selected row compiles into the generic purposeful
clearing theorem only when the corresponding exchange is enacted and
purposeful in that frame.
-/

@[expose] public section

namespace Praxeology

/-- One finite candidate pair with an ordinal reservation bracket and a cash
snapshot read from an arbitrary ActionFrame. -/
structure FiniteFundedReservationRow {W : ActionFrame}
    (M : MultilateralCohortMarket W.Agent W.Means)
    (moment : W.Moment) (history : W.History) where
  buyer : W.Agent
  seller : W.Agent
  buyerMember : buyer ∈ M.Buyers
  sellerMember : seller ∈ M.Sellers
  reservation : PurposefulReservationPair M buyer seller moment history
  snapshotCash : ℕ
  snapshotCash_eq : snapshotCash = W.omega buyer moment history M.m_money

namespace FiniteFundedReservationRow

/-- The candidate price is the seller's ordinal floor. -/
def ask {W : ActionFrame} {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (row : FiniteFundedReservationRow M moment history) : ℕ :=
  row.reservation.sellerFloor

/-- A pair clears when the seller floor fits under the buyer's cash-funded
reservation. -/
def feasible {W : ActionFrame} {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (row : FiniteFundedReservationRow M moment history) : Prop :=
  row.ask ≤ row.reservation.fundedBid row.snapshotCash

instance feasibleDecidable {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (row : FiniteFundedReservationRow M moment history) : Decidable row.feasible := by
  unfold feasible ask
  infer_instance

/-- Every feasible candidate price lies above the seller floor, below the
buyer ceiling, and below observed cash. -/
theorem ask_bracket {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (row : FiniteFundedReservationRow M moment history)
    (hfeasible : row.feasible) :
    row.reservation.sellerFloor ≤ row.ask ∧
    row.ask ≤ row.reservation.buyerCeiling ∧
    row.ask ≤ row.snapshotCash := by
  exact ⟨le_rfl,
    le_trans hfeasible (row.reservation.fundedBid_le_ceiling row.snapshotCash),
    le_trans hfeasible (row.reservation.fundedBid_le_cash row.snapshotCash)⟩

/-- At the chosen ask, both reservation policies prefer their matched actions
to idling. These preference policies are fields of the ActionFrame-grounded
reservation pair, not numeric assumptions about compiler data. -/
theorem ask_is_preferred {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (row : FiniteFundedReservationRow M moment history)
    (hfeasible : row.feasible) :
    Preference row.buyer moment history
      (End_of row.buyer
        (W.Accept row.buyer row.seller 1 M.m_good row.ask M.m_money)
        moment history)
      (End_of row.buyer α₀ moment history) ∧
    Preference row.seller moment history
      (End_of row.seller
        (W.Offer row.seller row.buyer 1 M.m_good row.ask M.m_money)
        moment history)
      (End_of row.seller α₀ moment history) := by
  have hbracket := row.ask_bracket hfeasible
  exact ⟨row.reservation.buyerPrefersAtOrBelow row.ask hbracket.2.1,
    row.reservation.sellerPrefersAtOrAbove row.ask hbracket.1⟩

end FiniteFundedReservationRow

/-- Linear scan for the first candidate whose ordinal seller floor fits under
its buyer's funded bid. The scenario generator controls and preserves row
order. -/
def firstFeasibleReservation? {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History} :
    List (FiniteFundedReservationRow M moment history) →
      Option (FiniteFundedReservationRow M moment history)
  | [] => none
  | row :: rest =>
      if row.feasible then some row else firstFeasibleReservation? rest

/-- Any selected row belongs to the input list and carries a feasible
preference/cash bracket. -/
theorem firstFeasibleReservation?_sound {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (rows : List (FiniteFundedReservationRow M moment history))
    (row : FiniteFundedReservationRow M moment history)
    (hselected : firstFeasibleReservation? rows = some row) :
    row ∈ rows ∧ row.feasible := by
  induction rows with
  | nil =>
      simp only [firstFeasibleReservation?] at hselected
      contradiction
  | cons head tail ih =>
      by_cases hhead : head.feasible
      · simp only [firstFeasibleReservation?, hhead] at hselected
        have hrow : head = row := Option.some.inj hselected
        subst row
        exact ⟨List.mem_cons_self, hhead⟩
      · simp only [firstFeasibleReservation?, hhead] at hselected
        obtain ⟨hmem, hfeasible⟩ := ih hselected
        exact ⟨List.mem_cons_of_mem _ hmem, hfeasible⟩

/-- Choose a feasible reservation pair with the least seller ask. Ties are
resolved in favor of the earlier row, so the result is deterministic while
the clearing price does not depend on the caller's candidate ordering. -/
def leastFeasibleReservation? {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History} :
    List (FiniteFundedReservationRow M moment history) →
      Option (FiniteFundedReservationRow M moment history)
  | [] => none
  | row :: rest =>
      if row.feasible then
        match leastFeasibleReservation? rest with
        | none => some row
        | some best => if row.ask ≤ best.ask then some row else some best
      else
        leastFeasibleReservation? rest

/-- The least-ask selector either finds no feasible row or returns a feasible
row that belongs to the book and has an ask no greater than any other
feasible candidate. -/
theorem leastFeasibleReservation?_spec {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (rows : List (FiniteFundedReservationRow M moment history)) :
    match leastFeasibleReservation? rows with
    | none => ∀ row ∈ rows, ¬ row.feasible
    | some best =>
        best ∈ rows ∧ best.feasible ∧
          ∀ row ∈ rows, row.feasible → best.ask ≤ row.ask := by
  induction rows with
  | nil =>
      simp [leastFeasibleReservation?]
  | cons head tail ih =>
      by_cases hhead : head.feasible
      · simp only [leastFeasibleReservation?, hhead]
        cases htail : leastFeasibleReservation? tail with
        | none =>
            have htail_none := ih
            rw [htail] at htail_none
            refine ⟨List.mem_cons_self, hhead, ?_⟩
            intro row hrow hfeasible
            rcases List.mem_cons.mp hrow with heq | hmem
            · simp [heq]
            · exact (htail_none row hmem hfeasible).elim
        | some best =>
            have htail_spec := ih
            rw [htail] at htail_spec
            rcases htail_spec with ⟨hbest_mem, hbest_feasible, hbest_least⟩
            by_cases hhead_le : head.ask ≤ best.ask
            · simp only [hhead_le]
              refine ⟨List.mem_cons_self, hhead, ?_⟩
              intro row hrow hfeasible
              rcases List.mem_cons.mp hrow with heq | hmem
              · simp [heq]
              · exact le_trans hhead_le (hbest_least row hmem hfeasible)
            · simp only [hhead_le]
              refine ⟨List.mem_cons_of_mem _ hbest_mem, hbest_feasible, ?_⟩
              intro row hrow hfeasible
              rcases List.mem_cons.mp hrow with heq | hmem
              · subst row
                exact Nat.le_of_not_ge hhead_le
              · exact hbest_least row hmem hfeasible
      · simp only [leastFeasibleReservation?, hhead]
        cases htail : leastFeasibleReservation? tail with
        | none =>
            have htail_none := ih
            rw [htail] at htail_none
            intro row hrow hfeasible
            rcases List.mem_cons.mp hrow with heq | hmem
            · subst row
              exact hhead hfeasible
            · exact htail_none row hmem hfeasible
        | some best =>
            have htail_spec := ih
            rw [htail] at htail_spec
            rcases htail_spec with ⟨hbest_mem, hbest_feasible, hbest_least⟩
            refine ⟨List.mem_cons_of_mem _ hbest_mem, hbest_feasible, ?_⟩
            intro row hrow hfeasible
            rcases List.mem_cons.mp hrow with heq | hmem
            · subst row
              exact (hhead hfeasible).elim
            · exact hbest_least row hmem hfeasible

/-- An executable book of candidate pairs for one market node. -/
structure FiniteFundedReservationBook {W : ActionFrame}
    (M : MultilateralCohortMarket W.Agent W.Means)
    (moment : W.Moment) (history : W.History) where
  rows : List (FiniteFundedReservationRow M moment history)

namespace FiniteFundedReservationBook

/-- Deterministically select a feasible pair with the least seller ask. -/
def select {W : ActionFrame} {M : MultilateralCohortMarket W.Agent W.Means}
    {moment : W.Moment} {history : W.History}
    (book : FiniteFundedReservationBook M moment history) :=
  leastFeasibleReservation? book.rows

end FiniteFundedReservationBook

/-- A finite selection becomes a general purposeful clearing round only when
the selected pair matches the frame's observed clearing event and the matched
exchange is certified by BilateralExchange. -/
structure FinitePurposefulClearingWitness {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means} where
  clearing : MultilateralClearingScenario M
  book : FiniteFundedReservationBook M clearing.moment clearing.history
  selected : FiniteFundedReservationRow M clearing.moment clearing.history
  selected_by_least_ask : book.select = some selected
  selected_buyer_matches : selected.buyer = clearing.buyer
  selected_seller_matches : selected.seller = clearing.seller
  selected_price_matches : selected.ask = clearing.price
  purposefulExchange : BilateralExchange clearing.seller clearing.buyer
    clearing.moment clearing.history 1 M.m_good clearing.price M.m_money

namespace FinitePurposefulClearingWitness

/-- Compile the finite selection into the generic ActionFrame-funded clearing
structure. Preference, cash, purposeful exchange, and deterrence remain
properties of the general theory. -/
def instantiate {W : ActionFrame} {M : MultilateralCohortMarket W.Agent W.Means}
    (C : FinitePurposefulClearingWitness (M := M)) :
    PurposefulFundedClearingRound M := by
  have hselected := leastFeasibleReservation?_spec C.book.rows
  have hselected_eq : leastFeasibleReservation? C.book.rows = some C.selected :=
    C.selected_by_least_ask
  change leastFeasibleReservation? C.book.rows = some C.selected at hselected_eq
  rw [hselected_eq] at hselected
  rcases hselected with ⟨_hselected_mem, hselected_feasible, _⟩
  refine
    { base := ⟨C.clearing, C.purposefulExchange⟩
      reservation :=
        { buyerCeiling := C.selected.reservation.buyerCeiling
          sellerFloor := C.selected.reservation.sellerFloor
          buyerCeiling_eq_value := by
            simpa [C.selected_buyer_matches] using
              C.selected.reservation.buyerCeiling_eq_value
          sellerFloor_eq_value := by
            simpa [C.selected_seller_matches] using
              C.selected.reservation.sellerFloor_eq_value
          buyerPrefersAtOrBelow := by
            intro p hp
            simpa [C.selected_buyer_matches, C.selected_seller_matches] using
              C.selected.reservation.buyerPrefersAtOrBelow p hp
          buyerDeterrenceAbove := by
            intro p hp
            simpa [C.selected_buyer_matches, C.selected_seller_matches] using
              C.selected.reservation.buyerDeterrenceAbove p hp
          sellerPrefersAtOrAbove := by
            intro p hp
            simpa [C.selected_buyer_matches, C.selected_seller_matches] using
              C.selected.reservation.sellerPrefersAtOrAbove p hp
          sellerDeterrenceBelow := by
            intro p hp
            simpa [C.selected_buyer_matches, C.selected_seller_matches] using
              C.selected.reservation.sellerDeterrenceBelow p hp }
      snapshotCash := C.selected.snapshotCash
      snapshotCash_eq := by
        simpa [C.selected_buyer_matches] using C.selected.snapshotCash_eq
      sellerFloor_le_price := by
        rw [← C.selected_price_matches]
        exact le_rfl
      price_le_fundedBid := by
        have hfeasible : C.selected.feasible := hselected_feasible
        rw [← C.selected_price_matches]
        change C.selected.reservation.sellerFloor ≤
          min C.selected.reservation.buyerCeiling C.selected.snapshotCash
        change C.selected.reservation.sellerFloor ≤
          min C.selected.reservation.buyerCeiling C.selected.snapshotCash at hfeasible
        exact hfeasible }

/-- Matched participants perform active purposeful actions. -/
theorem active_matched_pair {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    (C : FinitePurposefulClearingWitness (M := M)) :
    ActivePurposefulAct C.clearing.seller C.clearing.moment C.clearing.history
      (W.Offer C.clearing.seller C.clearing.buyer 1 M.m_good
        C.clearing.price M.m_money) ∧
    ActivePurposefulAct C.clearing.buyer C.clearing.moment C.clearing.history
      (W.Accept C.clearing.buyer C.clearing.seller 1 M.m_good
        C.clearing.price M.m_money) :=
by
  simpa [instantiate] using C.instantiate.base.matched_parties_active

/-- Extra-marginal participants cannot enact their supplied candidate actions
purposefully at the selected price. -/
theorem extra_marginal_deterrence {W : ActionFrame}
    {M : MultilateralCohortMarket W.Agent W.Means}
    (C : FinitePurposefulClearingWitness (M := M)) :
    (∀ b ∈ M.ExtraMarginalBuyers C.clearing.price,
      ¬ ActivePurposefulAct b C.clearing.moment C.clearing.history
        (C.clearing.buyerCandidateAction b)) ∧
    (∀ s ∈ M.ExtraMarginalSellers C.clearing.price,
      ¬ ActivePurposefulAct s C.clearing.moment C.clearing.history
        (C.clearing.sellerCandidateAction s)) :=
by
  simpa [instantiate] using C.instantiate.base.extra_marginal_deterrence

end FinitePurposefulClearingWitness

end Praxeology

end
