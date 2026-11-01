/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Entrepreneurship
public import Praxeology.BusinessCycle.Information
public import Praxeology.BusinessCycle.Clusters
public import Praxeology.BusinessCycle.Firms
public import Praxeology.BusinessCycle.Grounded

/-!
# Business Cycle

This module is the public synthesis layer. The general entrepreneur result is
proved in `Entrepreneurship`; the organized-firm specialization composes that
result with `Organization`, `FirmBoundary`, and `Catallactics` in
`BusinessCycle.Firms`. `BusinessCycle.Information` models observation-based
indistinguishability and shared response policies. `BusinessCycle.Clusters`
states conditional cohort results for shared-input shortages and common
factor-price responses, composing blockage with the existing contextual
regret theorem when each project's counterfactual evidence is supplied. These
results range over the existing `ActionFrame`; they do not introduce a
separate finite history model.
-/

@[expose] public section

namespace Praxeology

/-- A credit cohort with two distinct borrowers necessarily contains three
distinct ActionFrame agents: the common lender and both borrowers. This lower
bound is independent of any particular finite frame. -/
theorem CreditShockCohort.requires_three_agents {W : ActionFrame}
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur)
    {e₁ e₂ : Entrepreneur}
    (h₁ : e₁ ∈ C.entrepreneurs) (h₂ : e₂ ∈ C.entrepreneurs)
    (hne : e₁ ≠ e₂) : 3 ≤ Fintype.card W.Agent := by
  have h_lender₁ := C.lender_distinct_from_exposed_borrower h₁
  have h_lender₂ := C.lender_distinct_from_exposed_borrower h₂
  have h_borrowers : C.agent e₁ ≠ C.agent e₂ := by
    intro h
    exact hne (C.agent_injective h₁ h₂ h)
  let roles : Finset W.Agent := {C.commonLender, C.agent e₁, C.agent e₂}
  have h_roles_card : roles.card = 3 := by
    simp [roles, h_lender₁, h_lender₂, h_borrowers]
  calc
    3 = roles.card := h_roles_card.symm
    _ ≤ Fintype.card W.Agent := Finset.card_le_univ roles

/-- The cohort's injective borrower map and its separate common lender require
one more ActionFrame agent than the number of exposed entrepreneurs. -/
theorem CreditShockCohort.requires_one_more_agent_than_cohort {W : ActionFrame}
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) :
    C.entrepreneurs.card + 1 ≤ Fintype.card W.Agent := by
  let borrowers := C.entrepreneurs.image C.agent
  have hlender : C.commonLender ∉ borrowers := by
    intro hmem
    obtain ⟨e, he, hagent⟩ := Finset.mem_image.mp hmem
    exact (C.lender_distinct_from_exposed_borrower he) hagent.symm
  let roles := borrowers ∪ {C.commonLender}
  have h_roles_card : roles.card = C.entrepreneurs.card + 1 := by
    calc
      roles.card = borrowers.card + ({C.commonLender} : Finset W.Agent).card :=
        Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hlender)
      _ = C.entrepreneurs.card + 1 := by
        simp only [Finset.card_singleton]
        change (C.entrepreneurs.image C.agent).card + 1 =
          C.entrepreneurs.card + 1
        rw [Finset.card_image_of_injOn C.agent_injective]
  calc
    C.entrepreneurs.card + 1 = roles.card := h_roles_card.symm
    _ ≤ Fintype.card W.Agent := Finset.card_le_univ roles

/-- Neither two-agent ActionFrame used for the grounded entrepreneurial cycle
can itself host a cohort with two distinct borrowers and a separate lender. -/
theorem abct_grounded_frame_cannot_host_two_borrowers
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort ABCTGroundedActionFrame Context Entrepreneur)
    {e₁ e₂ : Entrepreneur}
    (h₁ : e₁ ∈ C.entrepreneurs) (h₂ : e₂ ∈ C.entrepreneurs)
    (hne : e₁ ≠ e₂) : False := by
  have hthree := C.requires_three_agents h₁ h₂ hne
  change 3 ≤ Fintype.card (Fin 2) at hthree
  norm_num at hthree

/-- The generic bilateral trade frame likewise lacks the third distinct agent
needed for two cohort borrowers and their shared lender. -/
theorem bilateral_frame_cannot_host_two_borrowers
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort BilateralTradeActionFrame Context Entrepreneur)
    {e₁ e₂ : Entrepreneur}
    (h₁ : e₁ ∈ C.entrepreneurs) (h₂ : e₂ ∈ C.entrepreneurs)
    (hne : e₁ ≠ e₂) : False := by
  have hthree := C.requires_three_agents h₁ h₂ hne
  change 3 ≤ Fintype.card (Fin 2) at hthree
  norm_num at hthree

/-- The existing three-agent workshop cannot instantiate a credit cohort with
two distinct exposed borrowers: its only purposeful offerers are the operator
at transfer and the entrepreneur at sale, so the lender role cannot be shared
across two distinct borrowers. -/
theorem workshop_credit_cohort_cannot_expose_two_borrowers
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort WorkshopActionFrame Context Entrepreneur)
    {e₁ e₂ : Entrepreneur}
    (h₁ : e₁ ∈ C.entrepreneurs) (h₂ : e₂ ∈ C.entrepreneurs)
    (hne : e₁ ≠ e₂) : False := by
  let T₁ : PawnLoanTerms WorkshopActionFrame :=
    (C.project e₁).funding.terms
  let T₂ : PawnLoanTerms WorkshopActionFrame :=
    (C.project e₂).funding.terms
  have A₁ : CreditAdvance T₁ := (C.project e₁).funding.advance
  have A₂ : CreditAdvance T₂ := (C.project e₂).funding.advance
  have h₁_lender : T₁.lender = C.commonLender :=
    (C.backedAdvance e₁ h₁).lender_is_issuer.trans C.common_lender_is_issuer
  have h₂_lender : T₂.lender = C.commonLender :=
    (C.backedAdvance e₂ h₂).lender_is_issuer.trans C.common_lender_is_issuer
  have h_borrowers_differ : T₁.borrower ≠ T₂.borrower := by
    intro hborrower
    apply hne
    apply C.agent_injective h₁ h₂
    calc
      C.agent e₁ = T₁.borrower := (C.credit_borrower_matches_agent e₁ h₁).symm
      _ = T₂.borrower := hborrower
      _ = C.agent e₂ := C.credit_borrower_matches_agent e₂ h₂
  have h_same_borrower := workshop_no_common_lender_distinct_borrowers
    A₁ A₂ (h₁_lender.trans h₂_lender.symm)
  exact h_borrowers_differ h_same_borrower

/-- The existing workshop cannot host even a single-member credit cohort:
cohort quotes require an actual repayment, while every purposeful advance in
this frame lacks a later repayment event. -/
theorem workshop_cannot_host_credit_shock_cohort
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    [Nonempty Entrepreneur]
    (C : CreditShockCohort WorkshopActionFrame Context Entrepreneur) : False := by
  obtain ⟨e⟩ := ‹Nonempty Entrepreneur›
  exact workshop_no_credit_repayment
    (C.project e).funding.terms
    (C.project e).funding.advance
    ⟨(C.rateQuotes e).creditRepayment⟩

/-- A shared-input cluster with at least two regretful projects requires two
distinct borrowers and their common lender in the underlying ActionFrame. -/
theorem shared_input_cluster_requires_three_agents {W : ActionFrame}
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    [DecidableEq W.Agent] (C : CreditShockCohort W Context Entrepreneur)
    (S : SharedInputShortage C) : 3 ≤ Fintype.card W.Agent := by
  obtain ⟨e₁, e₂, h₁, h₂, hne, _, _, _⟩ :=
    S.two_distinct_regretful_entrepreneurs
  exact C.requires_three_agents h₁ h₂ hne

/-- A price-squeeze cluster likewise requires two distinct borrowers and a
separate common lender in the underlying ActionFrame. -/
theorem price_squeeze_cluster_requires_three_agents {W : ActionFrame}
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort W Context Entrepreneur) {d : ℕ}
    (S : PriceSqueezeCohort C d) : 3 ≤ Fintype.card W.Agent := by
  obtain ⟨e₁, e₂, h₁, h₂, hne, _, _, _⟩ :=
    S.two_distinct_regretful_entrepreneurs
  exact C.requires_three_agents h₁ h₂ hne

end Praxeology
