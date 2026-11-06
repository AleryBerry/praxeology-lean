/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Entrepreneurship

/-!
# A Two-Agent Complementary-Input Regret Witness

This finite witness reuses the bilateral exchange ActionFrame. The first agent
chooses a matched exchange under a deliberately specified objective, receives
an intermediate good, and later lacks a complementary input. A second valued
end makes the conditional regret comparison explicit.

This is an illustration of the conditional investment-regret theorem, not a
causal ABCT model: it has no loan contract, monetary expansion, loan market,
factor-price mechanism, or cohort of entrepreneurs. Its root and later
valuations are explicit scenario assumptions.
-/

@[expose] public section

namespace Praxeology

def ABCTGroundedEnd.projectedReturn : BilateralEnd := .quantity 1 1

def ABCTGroundedEnd.bustLiquidity : BilateralEnd := .quantity 0 2

def abctGroundedRequirement (e : BilateralEnd) (m : Fin 3) : ℕ :=
  bilateral_requirement e m

def abctGroundedValuedEnd (i : Fin 2) (t : BilateralMoment)
    (_h : Fin 4) (e : BilateralEnd) : Prop :=
  match i, t, e with
  | 0, .root, .quantity 1 1 => True
  | 0, .leaf3, .quantity 0 2 => True
  | _, _, _ => False

def abctGroundedPreference (i : Fin 2) (t : BilateralMoment) (h : Fin 4)
    (e₁ e₂ : BilateralEnd) : Prop :=
  match e₁, e₂ with
  | .bundle b₁, .bundle b₂ =>
      SubjectiveTeleologicalDominates abctGroundedRequirement
        (abctGroundedValuedEnd i t h) b₁ b₂
  | _, _ => False

@[reducible] instance ABCTGroundedActionFrame : ActionFrame :=
  { SubjectiveBilateralTradeActionFrame with
    requirement := abctGroundedRequirement
    ValuedEnd := abctGroundedValuedEnd
    valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
    MinPlausible := fun _ t => {bilateral_subjective_witness t}
    tau := fun _ t _ => t
    sigma := bilateral_sigma
    OutcomeOf := bilateral_subjective_outcome
    ExpectedMaturation := bilateral_subjective_maturation
    End_of := bilateral_subjective_end
    Preference := abctGroundedPreference
    Preference_bundle_invariant := by intro _ _ _ _ _ _; rfl
    pref_asymm := by
      intro i t h e₁ e₂ h₁₂ h₂₁
      cases e₁ <;> cases e₂ <;>
        simp only [abctGroundedPreference] at h₁₂ h₂₁
      rcases h₁₂ with ⟨_, ⟨S, hS, h_att₁, h_not₂⟩⟩
      exact h_not₂ (h₂₁.1 S hS h_att₁)
    doxastic_sure_thing_bridge := by
      intro i α β t h _h_app _h_weak h_strict
      rcases h_strict with ⟨h', hh', hpref⟩
      have heq : h' = bilateral_subjective_witness t := by
        change h' ∈ ({bilateral_subjective_witness t} : Set (Fin 4)) at hh'
        exact Set.mem_singleton_iff.mp hh'
      subst h'
      simpa [bilateral_subjective_end, bilateral_subjective_witness,
        bilateral_subjective_maturation, bilateral_subjective_outcome] using hpref
    doxastic_plausible_support := by
      intro i α β t h _h_app hpref
      refine ⟨bilateral_subjective_witness t, ?_, ?_⟩
      · change bilateral_subjective_witness t ∈
          ({bilateral_subjective_witness t} : Set (Fin 4))
        exact Set.mem_singleton _
      · simpa [bilateral_subjective_end, bilateral_subjective_witness,
          bilateral_subjective_maturation, bilateral_subjective_outcome] using hpref
    teleological_bundle_dominance_induces_preference := by
      intro _ _ _ b₁ b₂ hdom
      exact hdom }

def abctGroundedInvestment : ABCTGroundedActionFrame.Action :=
  ModelAction.offer (0 : Fin 2) 1 1 (0 : Fin 3) 1 (1 : Fin 3)

def abctGroundedCompletion : ABCTGroundedActionFrame.Action :=
  ModelAction.accept (1 : Fin 2) (0 : Fin 2) 1 (0 : Fin 3) 1 (2 : Fin 3)

def abctGroundedDecision : ABCTGroundedActionFrame.DecisionIndex :=
  ActionFrame.decisionIndex ABCTGroundedActionFrame BilateralMoment.root
    (3 : Fin 4) (by
      change bilateral_mem_hist BilateralMoment.root (3 : Fin 4)
      trivial)

theorem abctGroundedInvestment_purposeful :
    @PurposefulAct ABCTGroundedActionFrame (0 : Fin 2) BilateralMoment.root
      (3 : Fin 4) abctGroundedInvestment := by
  have hdom : SubjectiveTeleologicalDominates abctGroundedRequirement
      (abctGroundedValuedEnd (0 : Fin 2) BilateralMoment.root (3 : Fin 4))
      (bilateral_omega (0 : Fin 2) .leaf3 (3 : Fin 4))
      (bilateral_omega (0 : Fin 2) .leaf2 (2 : Fin 4)) := by
    classical
    apply subjective_teleological_dominates_of_unique_valued_end
      abctGroundedRequirement
      (abctGroundedValuedEnd (0 : Fin 2) BilateralMoment.root (3 : Fin 4))
      ABCTGroundedEnd.projectedReturn
      (bilateral_omega (0 : Fin 2) .leaf3 (3 : Fin 4))
      (bilateral_omega (0 : Fin 2) .leaf2 (2 : Fin 4))
    · intro e he
      cases e with
      | baseline => simp [abctGroundedValuedEnd] at he
      | bundle b => simp [abctGroundedValuedEnd] at he
      | quantity m q =>
          by_cases hm : m = 1
          · subst m
            by_cases hq : q = 1
            · subst q
              rfl
            · simp [abctGroundedValuedEnd, hq] at he
          · simp [abctGroundedValuedEnd, hm] at he
      | timed e τ => simp [abctGroundedValuedEnd] at he
    · simp [abctGroundedValuedEnd, ABCTGroundedEnd.projectedReturn]
    · intro m
      fin_cases m <;>
        norm_num [JointlyAttains, abctGroundedRequirement, bilateral_requirement,
          bilateral_omega, ABCTGroundedEnd.projectedReturn]
    · intro h_att
      have h_bad := h_att (1 : Fin 3)
      norm_num [JointlyAttains, abctGroundedRequirement, bilateral_requirement,
        bilateral_omega, ABCTGroundedEnd.projectedReturn] at h_bad
  have hpref := @ActionFrame.teleological_bundle_dominance_induces_preference
    ABCTGroundedActionFrame (0 : Fin 2) .root (3 : Fin 4)
    (bilateral_omega (0 : Fin 2) .leaf3 (3 : Fin 4))
    (bilateral_omega (0 : Fin 2) .leaf2 (2 : Fin 4)) hdom
  refine ⟨by decide, ⟨trivial, rfl⟩, Or.inr hpref, ?_⟩
  intro β hβ
  change β ∈ ({ModelAction.idle, abctGroundedInvestment} : Finset ModelAction) at hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · intro hrev
    exact ABCTGroundedActionFrame.pref_asymm
      (0 : Fin 2) .root (3 : Fin 4) hpref hrev
  · intro hself
    exact ActionFrame.pref_irrefl ABCTGroundedActionFrame
      (0 : Fin 2) .root (3 : Fin 4) _ hself

def abctGroundedInventoryStep :
    InventoryStep ABCTGroundedActionFrame (0 : Fin 2) (3 : Fin 4)
      .root .leaf3 := by
  refine .matchedOffer (j := (1 : Fin 2)) (qA := 1) (mA := (0 : Fin 3))
    (qB := 1) (mB := (1 : Fin 3)) ?_ ?_ ?_ ?_
  · decide
  · change ABCTGroundedActionFrame.enacted (0 : Fin 2) .root (3 : Fin 4) =
      abctGroundedInvestment
    rfl
  · decide
  · change IsNextMoment bilateral_prec bilateral_mem_hist .root .leaf3 (3 : Fin 4)
    refine ⟨trivial, rfl, trivial, ?_⟩
    intro τ hmem hbetween
    cases τ <;> simp [bilateral_prec] at hbetween

def abctGroundedCapitalFormation :
    EntrepreneurialCapitalFormation (W := ABCTGroundedActionFrame)
      (0 : Fin 2) (3 : Fin 4) .root .leaf3
      abctGroundedInvestment (1 : Fin 3) :=
  ⟨abctGroundedInventoryStep, rfl, by decide, by decide, by decide⟩

/-- Concrete two-agent instantiation of the conditional entrepreneur theorem.
The matched exchange is purposeful under the root valuation stipulated by
this frame; its receipt enters inventory, the complementary means remain
absent, and a deterministic context derives later regret from the specified
terminal valuation. This is not evidence that a credit expansion endogenously
causes a general business cycle. -/
theorem abct_grounded_action_frame_master :
    ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf3 (3 : Fin 4) (1 : Fin 3) = 1 ∧
    ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf3 (3 : Fin 4) (2 : Fin 3) = 0 ∧
    abctGroundedCompletion ∉
      ABCTGroundedActionFrame.A_feas (0 : Fin 2) .leaf3 (3 : Fin 4) ∧
    @PurposefulAct ABCTGroundedActionFrame (0 : Fin 2) .root
      (3 : Fin 4) abctGroundedInvestment ∧
    ContextMatchedRegret (F := ABCTGroundedActionFrame)
      ABCTGroundedActionFrame.deterministicCorrespondence
      (0 : Fin 2) abctGroundedDecision .leaf3 abctGroundedInvestment
      ABCTGroundedActionFrame.alpha_zero := by
  let C : ABCTGroundedActionFrame.ContextCorrespondence Unit :=
    ABCTGroundedActionFrame.deterministicCorrespondence
  have h_actual : C.admissible (0 : Fin 2) abctGroundedDecision ()
      abctGroundedInvestment (3 : Fin 4) .leaf3 := by
    change abctGroundedInvestment ∈ ABCTGroundedActionFrame.A_feas
        (0 : Fin 2) .root (3 : Fin 4) ∧
      (3 : Fin 4) = ABCTGroundedActionFrame.sigma
        (0 : Fin 2) .root abctGroundedInvestment (3 : Fin 4) ∧
      .leaf3 = ABCTGroundedActionFrame.ExpectedMaturation (0 : Fin 2)
        abctGroundedInvestment .root
        (ABCTGroundedActionFrame.sigma (0 : Fin 2) .root
          abctGroundedInvestment (3 : Fin 4))
    decide
  have h_safe : C.admissible (0 : Fin 2) abctGroundedDecision ()
      ABCTGroundedActionFrame.alpha_zero (2 : Fin 4) .leaf2 := by
    change ABCTGroundedActionFrame.alpha_zero ∈
        ABCTGroundedActionFrame.A_feas (0 : Fin 2) .root (3 : Fin 4) ∧
      (2 : Fin 4) = ABCTGroundedActionFrame.sigma (0 : Fin 2) .root
        ABCTGroundedActionFrame.alpha_zero (3 : Fin 4) ∧
      .leaf2 = ABCTGroundedActionFrame.ExpectedMaturation (0 : Fin 2)
        ABCTGroundedActionFrame.alpha_zero .root
        (ABCTGroundedActionFrame.sigma (0 : Fin 2) .root
          ABCTGroundedActionFrame.alpha_zero (3 : Fin 4))
    decide
  have h_bundle : SubjectiveTeleologicalDominates abctGroundedRequirement
      (abctGroundedValuedEnd (0 : Fin 2) .leaf3 (3 : Fin 4))
      (ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf2 (2 : Fin 4))
      (ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf3 (3 : Fin 4)) := by
    classical
    apply subjective_teleological_dominates_of_unique_valued_end
      abctGroundedRequirement
      (abctGroundedValuedEnd (0 : Fin 2) .leaf3 (3 : Fin 4))
      ABCTGroundedEnd.bustLiquidity
      (ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf2 (2 : Fin 4))
      (ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf3 (3 : Fin 4))
    · intro e he
      cases e with
      | baseline => simp [abctGroundedValuedEnd] at he
      | bundle b => simp [abctGroundedValuedEnd] at he
      | quantity m q =>
          by_cases hm : m = 0
          · subst m
            by_cases hq : q = 2
            · subst q
              rfl
            · simp [abctGroundedValuedEnd, hq] at he
          · simp [abctGroundedValuedEnd, hm] at he
      | timed e τ => simp [abctGroundedValuedEnd] at he
    · simp [abctGroundedValuedEnd, ABCTGroundedEnd.bustLiquidity]
    · intro m
      fin_cases m
      · change 2 ≤ bilateral_omega 0 .leaf2 2 0
        simp [bilateral_omega]
      · change 0 ≤ bilateral_omega 0 .leaf2 2 1
        exact Nat.zero_le _
      · change 0 ≤ bilateral_omega 0 .leaf2 2 2
        exact Nat.zero_le _
    · intro h_att
      have h_bad := h_att (0 : Fin 3)
      change 2 ≤ bilateral_omega 0 .leaf3 3 0 at h_bad
      simp [bilateral_omega] at h_bad
  let I : EntrepreneurialInvestment ABCTGroundedActionFrame := {
    i := (0 : Fin 2)
    naturalDecision := abctGroundedDecision
    x := abctGroundedDecision
    next := .leaf3
    actualMaturity := .leaf3
    safeMaturity := .leaf2
    safeHistory := (2 : Fin 4)
    investment := abctGroundedInvestment
    completion := abctGroundedCompletion
    safeAction := ABCTGroundedActionFrame.alpha_zero
    capital := (1 : Fin 3)
    complementary := (2 : Fin 3) }
  let S : EntrepreneurialCycleScenario ABCTGroundedActionFrame Unit := {
    investment := I
    formation := by simpa [I, abctGroundedDecision, ActionFrame.decisionIndex,
      ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment]
      using abctGroundedCapitalFormation
    evaluation := {
      correspondence := C
      safeFeasible := by decide
      context := ()
      contextCompatible := trivial
      actualAdmitted := by simpa [I, abctGroundedDecision, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment] using h_actual
      safeAdmitted := by simpa [I, abctGroundedDecision, ActionFrame.decisionIndex,
        ActionFrame.DecisionIndex.history, ActionFrame.DecisionIndex.moment] using h_safe
      physicalOutcomes := by intro _ _ _ _; rfl
      safeBundleDominates := by
        change SubjectiveTeleologicalDominates abctGroundedRequirement
          (abctGroundedValuedEnd 0 BilateralMoment.leaf3 3)
          (bilateral_omega 0 .leaf2 2) (bilateral_omega 0 .leaf3 3)
        exact h_bundle } }
  have h_starve :
      ABCTGroundedActionFrame.omega (0 : Fin 2) .leaf3 (3 : Fin 4) (2 : Fin 3) = 0 := by
    decide
  have h_req :
      0 < ABCTGroundedActionFrame.use_means abctGroundedCompletion (2 : Fin 3) := by
    decide
  have h_purp : PurposefulAct (0 : Fin 2) .root (3 : Fin 4) abctGroundedInvestment :=
    abctGroundedInvestment_purposeful
  have h_cycle := S.regret_of_starvation h_starve h_req h_purp
  exact ⟨h_cycle.1.capitalStockAfter, h_cycle.2, h_cycle.1.completionBlocked,
    h_cycle.1.purposefulInvestment, h_cycle.1.contextualRegret⟩

end Praxeology
