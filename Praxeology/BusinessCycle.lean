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
public import Praxeology.BusinessCycle.Auctions
public import Praxeology.BusinessCycle.Regimes
public import Praxeology.BusinessCycle.FactorExecution
public import Praxeology.BusinessCycle.ProfileProgram
public import Praxeology.BusinessCycle.DefaultWitness
public import Praxeology.BusinessCycle.PhysicalSettlementWitness

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
`BusinessCycle.Auctions` supplies deterministic finite loan and factor price
mechanisms and the five-project reservation/price calculations; a complete
causal lifecycle also requires preference-grounded choices and earlier
production stages.
`BusinessCycle.Regimes` computes the fixed baseline, credit, and saving
scenario outcomes from explicitly accounted money and completion-factor
sources, and exposes a named policy from rate observations to expected factor
supply. The policy is an explicit behavioral premise; equal rate observations
do not determine it. `BusinessCycle.FactorExecution` applies the eligible
completion-factor purchases through matched physical transfers, including
the household's stated factor consumption and sales of offered factors. It
executes note issuance, the household cash transfer, funded principal advances,
completion operations, customer output sales, and auction-quoted repayments
for projects that complete. The earlier input and capital-production stage,
preference-grounded household and entrepreneur choices, default adjudication,
and legal foreclosure remain unmodeled.
`BusinessCycle.ProfileProgram` compiles the stated funding, factor, production,
sale, and repayment schedule into the recursive physical program and its
existing ActionFrame adapter. Loan capacity is cleared from bank money after
the executed issuance and household-transfer branches. Factor clearing uses
the advances that actually matched and the currently offered factor stock,
while preserving the model's initial-buffer participation rule and checking
physical affordability at each transfer. Later market rounds are computed
from the state reached on that branch; terms already assigned by a clearing
round are not revised automatically. Beliefs and preferences remain explicit
inputs to the adapter, and the named cycle does not derive purposeful
household saving or investment.
`BusinessCycle.DefaultWitness` adds a concrete unpaid-maturity branch to the
existing finite credit lifecycle. It derives the purposeful advance,
unmatched later acceptance, absence of an intervening repayment, and continued
physical collateral custody. The frame does not represent legal title, so this
result does not assert foreclosure.
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

/-- Conditional on repayment evidence, the workshop's available chronology
has no compatible later purposeful exchange. Cohort membership and origination
remain independent of repayment. -/
theorem workshop_repayment_evidence_is_incompatible_with_credit_shock_member
    {Context Entrepreneur : Type} [DecidableEq Entrepreneur]
    (C : CreditShockCohort WorkshopActionFrame Context Entrepreneur)
    {e : Entrepreneur} (_he : e ∈ C.entrepreneurs)
    (R : CreditRepayment (C.project e).funding.advance) : False := by
  exact workshop_repayment_evidence_incompatible
    (C.project e).funding.terms (C.project e).funding.advance R

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
