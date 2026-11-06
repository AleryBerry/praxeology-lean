/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Compiler

/-!
# Compiling a physical choice stage to an ActionFrame

This adapter turns the existing one-stage physical interpreter into an
`ActionFrame`. The two-level time tree and its branch histories are generated
from the choice stage. Preferences, valued ends, and reference histories stay
explicit inputs; the constructor does not infer those behavioral facts from
the inventory ledger. The information interpretation is the singleton
reference branch at the root and the observed branch after the choice. This is
an explicit certainty scenario, not a consequence of physical feasibility.
-/

@[expose] public section

namespace Praxeology

noncomputable instance finitePhysicalChoiceStageProfileFintype
    {Agent Means Operation : Type} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) : Fintype S.Profile where
  elems := S.profiles
  complete := S.mem_profiles

/-- The root and one successor moment for each generated profile. -/
abbrev FinitePhysicalChoiceMoment {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) := Option S.Profile

/-- Branch incidence in the one-stage choice tree. -/
def finitePhysicalChoiceIncidence {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) :
    FinitePhysicalChoiceMoment S → S.Profile → Prop
  | none, _ => True
  | some p, h => p = h

/-- The strict temporal order has the common root before each profile branch. -/
def finitePhysicalChoicePrecedence {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) :
    FinitePhysicalChoiceMoment S → FinitePhysicalChoiceMoment S → Prop
  | none, some _ => True
  | _, _ => False

instance finitePhysicalChoicePrecedenceDecidable
    {Agent Means Operation : Type} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) :
    DecidableRel (finitePhysicalChoicePrecedence S) := by
  intro t u
  cases t with
  | none =>
      cases u with
      | none => exact isFalse (by simp [finitePhysicalChoicePrecedence])
      | some _ => exact isTrue trivial
  | some _ =>
      cases u with
      | none => exact isFalse (by simp [finitePhysicalChoicePrecedence])
      | some _ => exact isFalse (by simp [finitePhysicalChoicePrecedence])

/-- Ends for a compiled stage: physical bundles, timed bundles, and primitive
quantity ends. -/
inductive FinitePhysicalChoiceEnd {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) where
  | bundle : (Means → ℕ) → FinitePhysicalChoiceEnd S
  | timed : FinitePhysicalChoiceEnd S → FinitePhysicalChoiceMoment S →
      FinitePhysicalChoiceEnd S
  | quantity : Means → ℕ → FinitePhysicalChoiceEnd S

noncomputable instance finitePhysicalChoiceEndDecidableEq
    {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FiniteChoiceStage Agent Means Operation) :
    DecidableEq (FinitePhysicalChoiceEnd S) := Classical.decEq _

/-- Requirement quantity represented by a compiled-stage end. -/
def finitePhysicalChoiceRequirement
    {Agent Means Operation : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    [DecidableEq Operation]
    {S : FiniteChoiceStage Agent Means Operation} :
    FinitePhysicalChoiceEnd S → Means → ℕ
  | .bundle b, m => b m
  | .timed e _, m => finitePhysicalChoiceRequirement e m
  | .quantity m' q, m => if m = m' then q else 0

/-- Requirements and preferences are the behavioral and teleological inputs
needed to complete the physical stage. They are stated as premises instead of
being synthesized from the inventory transition. -/
structure FinitePhysicalChoiceBehavior
    {Agent Means Operation Service : Type}
    [Fintype Agent] [DecidableEq Agent] [Fintype Means] [DecidableEq Means]
    [DecidableEq Operation]
    (S : FinitePhysicalChoiceStage Agent Means Operation Service) where
  /-- The single history treated as plausible by each agent at the root.
  `toActionFrame` specializes the information field to this singleton at the
  root and to the observed branch at terminal moments. -/
  referenceHistory : Agent → S.choices.Profile
  valuedEnd : Agent → FinitePhysicalChoiceMoment S.choices → S.choices.Profile →
    FinitePhysicalChoiceEnd S.choices → Prop
  valuedEnd_invariant : ∀ i t {h₁ h₂ : S.choices.Profile} e,
    finitePhysicalChoiceIncidence S.choices t h₁ →
    finitePhysicalChoiceIncidence S.choices t h₂ →
    (valuedEnd i t h₁ e ↔ valuedEnd i t h₂ e)
  preference : Agent → FinitePhysicalChoiceMoment S.choices → S.choices.Profile →
    FinitePhysicalChoiceEnd S.choices → FinitePhysicalChoiceEnd S.choices → Prop
  preference_invariant : ∀ i t {h₁ h₂ : S.choices.Profile},
    finitePhysicalChoiceIncidence S.choices t h₁ →
    finitePhysicalChoiceIncidence S.choices t h₂ →
    preference i t h₁ = preference i t h₂
  preference_asymmetric : ∀ i t h {e₁ e₂ : FinitePhysicalChoiceEnd S.choices},
    preference i t h e₁ e₂ → ¬ preference i t h e₂ e₁
  teleological_dominance_prefers : ∀ i t h b₁ b₂,
    SubjectiveTeleologicalDominates finitePhysicalChoiceRequirement
      (valuedEnd i t h) b₁ b₂ →
    preference i t h (.bundle b₁) (.bundle b₂)

namespace FinitePhysicalChoiceStage

variable {Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [Fintype Means]
  [DecidableEq Means] [DecidableEq Operation] [Nonempty Agent]

abbrev Moment (S : FinitePhysicalChoiceStage Agent Means Operation Service) :=
  FinitePhysicalChoiceMoment S.choices

abbrev History (S : FinitePhysicalChoiceStage Agent Means Operation Service) :=
  S.choices.Profile

abbrev End (S : FinitePhysicalChoiceStage Agent Means Operation Service) :=
  FinitePhysicalChoiceEnd S.choices

/-- Translate a moment to its physically computed state. -/
def stateAt (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (t : S.Moment) : PhysicalState Agent Means Service :=
  match t with
  | none => S.before
  | some p => S.advance p

/-- The moment-specific reference branch used by the supplied belief profile. -/
def referenceAt (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) (i : Agent) (t : S.Moment) : S.History :=
  match t with
  | none => B.referenceHistory i
  | some p => p

/-- Apply an actor's feasible unilateral choice to a root profile. At a leaf
there is no remaining choice, so the history is retained. -/
def selectAt (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (i : Agent) (t : S.Moment) (a : EconomyAction Agent Means Operation)
    (h : S.History) : S.History :=
  match t with
  | none => if ha : a ∈ S.choices.menu i then S.choices.replaceProfile h i a ha else h
  | some _ => h

/-- A root choice matures at the selected successor branch. At a terminal
branch it matures at the current node. -/
def maturationAt (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (_i : Agent) (t : S.Moment) (_a : EconomyAction Agent Means Operation)
    (h : S.History) : S.Moment :=
  match t with
  | none => some h
  | some p => some p

/-- The physical result at a maturation node is the actor's inventory there. -/
def outcomeAt (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (i : Agent) (t : S.Moment) : S.End :=
  FinitePhysicalChoiceEnd.bundle ((S.stateAt t).stock i)

/-- Intended ends use the supplied reference history to evaluate the same
physical selector used by expected maturation. -/
def intendedEnd (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) (i : Agent) (t : S.Moment)
    (a : EconomyAction Agent Means Operation) : S.End :=
  S.outcomeAt i (S.maturationAt i t a
    (S.selectAt i t a (S.referenceAt B i t)))

/-- Construct the ActionFrame whose temporal tree, menus, action realization,
and physical ledger follow the existing stage and interpreter. -/
@[reducible] noncomputable def toActionFrame
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) : ActionFrame where
  Agent := Agent
  instNonemptyAgent := inferInstance
  instFintypeAgent := inferInstance
  instDecidableEqAgent := inferInstance
  Moment := S.Moment
  instDecidableEqMoment := inferInstance
  History := S.History
  instDecidableEqHistory := inferInstance
  Action := EconomyAction Agent Means Operation
  instNonemptyAction := ⟨.idle⟩
  instDecidableEqAction := inferInstance
  Means := Means
  instDecidableEqMeans := inferInstance
  Ends := S.End
  instDecidableEqEnds := inferInstance
  alpha_zero := .idle
  Precedence := finitePhysicalChoicePrecedence S.choices
  moment_lt_irrefl := by
    intro t ht
    cases t <;> simp [finitePhysicalChoicePrecedence] at ht
  moment_lt_trans := by
    intro t₁ t₂ t₃ h₁₂ h₂₃
    cases t₁ <;> cases t₂ <;> cases t₃ <;>
      simp [finitePhysicalChoicePrecedence] at h₁₂ h₂₃
  backward_linearity := by
    intro t₁ t₂ t₃ h₁₃ h₂₃
    cases t₁ <;> cases t₂ <;> cases t₃ <;>
      simp_all [finitePhysicalChoicePrecedence]
  mem_hist := finitePhysicalChoiceIncidence S.choices
  moment_in_history := by
    intro t
    cases t with
    | none => exact ⟨⟨fun _ => .idle, S.choices.idle_mem⟩, trivial⟩
    | some p => exact ⟨p, rfl⟩
  histories_maximal_linear := by
    intro h
    constructor
    · intro t₁ t₂ ht₁ ht₂
      cases t₁ with
      | none =>
          cases t₂ with
          | none => exact Or.inr (Or.inl rfl)
          | some p => exact Or.inl trivial
      | some p =>
          have hp : p = h := by simpa [finitePhysicalChoiceIncidence] using ht₁
          subst p
          cases t₂ with
          | none => exact Or.inr (Or.inr trivial)
          | some q =>
              have hq : q = h := by simpa [finitePhysicalChoiceIncidence] using ht₂
              subst q
              exact Or.inr (Or.inl rfl)
    · intro s hs hsub t ht
      cases t with
      | none =>
          change finitePhysicalChoiceIncidence S.choices none h
          trivial
      | some p =>
          have hh : some h ∈ s :=
            hsub (show some h ∈ {t | finitePhysicalChoiceIncidence S.choices t h} by
              simp [finitePhysicalChoiceIncidence])
          rcases hs ht hh with hlt | heq | hgt
          · simp [finitePhysicalChoicePrecedence] at hlt
          · have hp : p = h := Option.some.inj heq
            subst p
            exact show some h ∈
              {t | finitePhysicalChoiceIncidence S.choices t h} by
              simp [finitePhysicalChoiceIncidence]
          · simp [finitePhysicalChoicePrecedence] at hgt
  histories_extensional := by
    intro h₁ h₂ heq
    have hleaf := (heq (some h₁)).mp (show
      finitePhysicalChoiceIncidence S.choices (some h₁) h₁ from rfl)
    exact hleaf
  divergent_futures_witness := by
    intro t h₁ h₂ ht₁ ht₂ hne
    cases t with
    | none =>
        refine ⟨some h₁, some h₂, rfl, rfl, trivial, trivial, ?_, ?_, ?_⟩
        · simp [finitePhysicalChoicePrecedence]
        · intro heq
          exact hne (Option.some.inj heq)
        · simp [finitePhysicalChoicePrecedence]
    | some p =>
        have h₁eq : p = h₁ := by simpa [finitePhysicalChoiceIncidence] using ht₁
        have h₂eq : p = h₂ := by simpa [finitePhysicalChoiceIncidence] using ht₂
        exact (hne (h₁eq.symm.trans h₂eq)).elim
  A_cont := fun i t _ => match t with
    | none => S.choices.menu i
    | some _ => {.idle}
  A_cont_bundle_invariant := by
    intro i t h₁ h₂ _ _
    cases t <;> rfl
  alpha_zero_cont := by
    intro i t h
    cases t with
    | none => exact S.choices.idle_mem i
    | some _ => simp
  omega := fun i t h m => (S.stateAt t).stock i m
  omega_bundle_invariant := by
    intro i t m h₁ h₂ hh₁ hh₂
    cases t with
    | none => rfl
    | some p =>
        have heq₁ : p = h₁ := by simpa [finitePhysicalChoiceIncidence] using hh₁
        have heq₂ : p = h₂ := by simpa [finitePhysicalChoiceIncidence] using hh₂
        subst h₁
        subst h₂
        rfl
  use_means := rawActionUse S.operations
  yield_means := rawActionYield S.operations
  use_means_alpha_zero := by intro m; rfl
  yield_means_alpha_zero := by intro m; rfl
  A_feas := fun i t _ => match t with
    | none => feasibleMenu S.operations S.before i (S.choices.menu i)
    | some _ => {.idle}
  A_feas_coupling := by
    intro i t h a
    cases t with
    | none =>
        change a ∈ feasibleMenu S.operations S.before i (S.choices.menu i) ↔
          a ∈ S.choices.menu i ∧
            ∀ m, rawActionUse S.operations a m ≤ S.before.stock i m
        simpa [actionAffordable] using
          (mem_feasibleMenu_iff S.operations S.before i (S.choices.menu i) a)
    | some p =>
        change a ∈ {EconomyAction.idle} ↔
          a ∈ {EconomyAction.idle} ∧
            ∀ m, rawActionUse S.operations a m ≤ (S.stateAt (some p)).stock i m
        constructor
        · intro ha
          have haEq : a = .idle := Finset.mem_singleton.mp ha
          subst a
          exact ⟨by simp, by intro m; simp [rawActionUse]⟩
        · rintro ⟨ha, _⟩
          have : a = .idle := by simpa using ha
          simp [this]
  enacted := fun i t h => match t with
    | none => h.1 i
    | some _ => .idle
  enacted_in_A_feas := by
    intro i t h hh
    cases t with
    | none =>
        apply (mem_feasibleMenu_iff S.operations S.before i
          (S.choices.menu i) (h.1 i)).2
        refine ⟨h.2 i, ?_⟩
        exact S.menu_affordable i (h.1 i) (h.2 i)
    | some p => simp
  no_choice_between_undivided := by
    intro i t u h₁ h₂ _ _ htu hu₁ hu₂
    cases t with
    | none =>
        cases u with
        | none => simp [finitePhysicalChoicePrecedence] at htu
        | some p =>
            have hh₁ : p = h₁ := by simpa [finitePhysicalChoiceIncidence] using hu₁
            have hh₂ : p = h₂ := by simpa [finitePhysicalChoiceIncidence] using hu₂
            rw [← hh₁, ← hh₂]
    | some p => simp [finitePhysicalChoicePrecedence] at htu
  sigma := S.selectAt
  sigma_realization := by
    intro i t h h' a ht ha ht'
    cases t with
    | none =>
        have hmenu : a ∈ S.choices.menu i :=
          (mem_feasibleMenu_iff S.operations S.before i
            (S.choices.menu i) a).1 ha |>.1
        refine ⟨trivial, ?_⟩
        simp [FinitePhysicalChoiceStage.selectAt, hmenu]
    | some p =>
        have haidle : a = .idle := by simpa using ha
        subst a
        have h'eq : p = h' := by simpa [finitePhysicalChoiceIncidence] using ht'
        subst h'
        exact ⟨rfl, rfl⟩
  sigma_centering := by
    intro i t h a ht ha
    cases t with
    | none =>
        have hact : h.1 i = a := by simpa using ha
        have hmenu : a ∈ S.choices.menu i := by simpa [hact] using h.2 i
        have hselect : S.selectAt i none a h =
            S.choices.replaceProfile h i a hmenu := by
          simp [FinitePhysicalChoiceStage.selectAt, hmenu]
        rw [hselect]
        apply Subtype.ext
        funext j
        by_cases hji : j = i
        · subst j
          simp [FiniteChoiceStage.replaceProfile, hact]
        · simp [FiniteChoiceStage.replaceProfile, hji]
    | some p => rfl
  sigma_co_agency := by
    intro i j t h h' a hne ht ha ht'
    cases t with
    | none =>
        have hmenu : a ∈ S.choices.menu i :=
          (mem_feasibleMenu_iff S.operations S.before i
            (S.choices.menu i) a).1 ha |>.1
        simpa [FinitePhysicalChoiceStage.selectAt, hmenu] using
          (S.choices.replaceProfile_other h' a hmenu hne.symm)
    | some _ => rfl
  Offer := EconomyAction.offer
  Accept := EconomyAction.accept
  use_means_offer := by intro; simp [rawActionUse]
  yield_means_offer := by intro; simp [rawActionYield]
  use_means_accept := by intro; simp [rawActionUse]
  yield_means_accept := by intro; simp [rawActionYield]
  offer_inj := by
    intro i₁ j₁ qA₁ mA₁ qB₁ mB₁ i₂ j₂ qA₂ mA₂ qB₂ mB₂ h
    exact EconomyAction.offer.inj h
  accept_inj := by
    intro j₁ i₁ qA₁ mA₁ qB₁ mB₁ j₂ i₂ qA₂ mA₂ qB₂ mB₂ h
    exact EconomyAction.accept.inj h
  offer_ne_accept := by
    intro i j qA mA qB mB j' i' qA' mA' qB' mB' h
    cases h
  alpha_zero_ne_offer := by
    intro i j qA mA qB mB h
    cases h
  alpha_zero_ne_accept := by
    intro j i qA mA qB mB h
    cases h
  IsTradeAction := fun a => match a with
    | .offer .. => True
    | .accept .. => True
    | _ => False
  is_trade_action_def := by intro a; cases a <;> simp
  law_in_re_transition := by
    intro i t t' h a m hnot ha hnext
    cases t with
    | some p =>
        have hfalse := hnext.2.2.1
        change False at hfalse
        exact False.elim hfalse
    | none =>
      cases t' with
      | none =>
          have hfalse := hnext.2.2.1
          change False at hfalse
          exact False.elim hfalse
      | some p =>
        have hp : p = h := by simpa [finitePhysicalChoiceIncidence] using hnext.2.1
        subst p
        change h.1 i = a at ha
        have hbal := S.advance_balance h i m
        cases a with
        | idle => simpa [rawActionUse, rawActionYield, effectiveUse,
            effectiveYield, stateAt, ha] using hbal
        | operate op => simpa [rawActionUse, rawActionYield, effectiveUse,
            effectiveYield, stateAt, ha] using hbal
        | offer seller buyer soldQuantity soldGood paidQuantity paidGood =>
            exact (hnot (by simp)).elim
        | accept buyer seller soldQuantity soldGood paidQuantity paidGood =>
            exact (hnot (by simp)).elim
  unilateral_offer_noop := by
    intro i j qA mA qB mB t t' h m hoffer hn hnext
    cases t with
    | some p =>
        have hfalse := hnext.2.2.1
        change False at hfalse
        exact False.elim hfalse
    | none =>
      cases t' with
      | none =>
          have hfalse := hnext.2.2.1
          change False at hfalse
          exact False.elim hfalse
      | some p =>
        have hp : p = h := by simpa [finitePhysicalChoiceIncidence] using hnext.2.1
        subst p
        have hi : h.1 i = .offer i j qA mA qB mB := by simpa using hoffer
        have hj : h.1 j ≠ .accept j i qA mA qB mB := by simpa using hn
        have hbal := S.advance_balance h i m
        have hzero : effectiveUse S.operations h.1 i m = 0 ∧
            effectiveYield S.operations h.1 i m = 0 := by
          simp [effectiveUse, effectiveYield, hi, hj]
        rw [hzero.1, hzero.2] at hbal
        simpa [stateAt] using hbal
  unilateral_accept_noop := by
    intro j i qA mA qB mB t t' h m haccept hn hnext
    cases t with
    | some p =>
        have hfalse := hnext.2.2.1
        change False at hfalse
        exact False.elim hfalse
    | none =>
      cases t' with
      | none =>
          have hfalse := hnext.2.2.1
          change False at hfalse
          exact False.elim hfalse
      | some p =>
        have hp : p = h := by simpa [finitePhysicalChoiceIncidence] using hnext.2.1
        subst p
        have hj : h.1 j = .accept j i qA mA qB mB := by simpa using haccept
        have hi : h.1 i ≠ .offer i j qA mA qB mB := by simpa using hn
        have hbal := S.advance_balance h j m
        have hzero : effectiveUse S.operations h.1 j m = 0 ∧
            effectiveYield S.operations h.1 j m = 0 := by
          simp [effectiveUse, effectiveYield, hj, hi]
        rw [hzero.1, hzero.2] at hbal
        simpa [stateAt] using hbal
  bilateral_transfer_law := by
    intro i j qA mA qB mB t t' h m hne hoff haccept hnext
    cases t with
    | some p =>
        have hfalse := hnext.2.2.1
        change False at hfalse
        exact False.elim hfalse
    | none =>
      cases t' with
      | none =>
          have hfalse := hnext.2.2.1
          change False at hfalse
          exact False.elim hfalse
      | some p =>
        have hp : p = h := by simpa [finitePhysicalChoiceIncidence] using hnext.2.1
        subst p
        have hi : h.1 i = .offer i j qA mA qB mB := by simpa using hoff
        have hj : h.1 j = .accept j i qA mA qB mB := by simpa using haccept
        have hbi := S.advance_balance h i m
        have hbj := S.advance_balance h j m
        have hbi' := hbi
        have hbj' := hbj
        simp only [effectiveUse, effectiveYield, hi, hj] at hbi' hbj'
        exact ⟨by simpa [stateAt] using hbi', by simpa [stateAt] using hbj'⟩
  MinPlausible := fun i t => {referenceAt S B i t}
  min_plausible_nonempty := by intro i t; exact ⟨referenceAt S B i t, by simp⟩
  tau := fun _ t _ => t
  min_plausible_node_incidence := by
    intro i t h hh
    have hEq : h = referenceAt S B i t := by simpa using hh
    cases t <;> simp [finitePhysicalChoiceIncidence, hEq, referenceAt]
  tau_centering := by intro i t h hmem; rfl
  requirement := finitePhysicalChoiceRequirement
  ValuedEnd := B.valuedEnd
  valued_end_bundle_invariant := B.valuedEnd_invariant
  OutcomeOf := fun i _ _ t' _ => S.outcomeAt i t'
  ExpectedMaturation := fun i a t h => S.maturationAt i t a h
  expected_maturation_mem_future := by
    intro i a t h hmem ha
    cases t with
    | none => exact ⟨rfl, Or.inr trivial⟩
    | some p =>
        exact ⟨hmem, Or.inl rfl⟩
  End_of := fun i a t _ => S.intendedEnd B i t a
  End_of_bundle_invariant := by intro i a t h₁ h₂ hm₁ hm₂; rfl
  Preference := B.preference
  Preference_bundle_invariant := B.preference_invariant
  pref_asymm := B.preference_asymmetric
  doxastic_sure_thing_bridge := by
    intro i a b t h _ _ hbetter
    rcases hbetter with ⟨h', hh', hpref⟩
    have hEq : h' = S.referenceAt B i t := by
      simpa [FinitePhysicalChoiceStage.referenceAt] using hh'
    subst h'
    change B.preference i t h (S.intendedEnd B i t a) (S.intendedEnd B i t b)
    exact hpref
  doxastic_plausible_support := by
    intro i a b t h _ hpref
    refine ⟨S.referenceAt B i t, by simp, ?_⟩
    change B.preference i t h (S.intendedEnd B i t a) (S.intendedEnd B i t b)
    exact hpref
  BundleEnd := FinitePhysicalChoiceEnd.bundle
  teleological_bundle_dominance_induces_preference := B.teleological_dominance_prefers
  TimedEnd := FinitePhysicalChoiceEnd.timed
  QuantityEnd := FinitePhysicalChoiceEnd.quantity
  timed_end_inj := by
    intro e₁ t₁ e₂ t₂ h
    exact FinitePhysicalChoiceEnd.timed.inj h
  quantity_end_inj := by
    intro m₁ q₁ m₂ q₂ h
    exact FinitePhysicalChoiceEnd.quantity.inj h

/-- The generated frame reads every inventory from the stage's existing
pre-state or interpreter-derived successor state. -/
@[simp] theorem toActionFrame_omega
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) (i : Agent) (t : S.Moment)
    (h : S.History) (m : Means) :
    (S.toActionFrame B).omega i t h m = (S.stateAt t).stock i m := rfl

/-- At the root, the frame enacts the complete profile recorded by the chosen
history branch. -/
@[simp] theorem toActionFrame_enacted_root
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) (i : Agent) (h : S.History) :
    (S.toActionFrame B).enacted i none h = h.1 i := rfl

/-- A terminal moment has no later action, so the frame enacts the existing
idle baseline there. -/
@[simp] theorem toActionFrame_enacted_leaf
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (B : FinitePhysicalChoiceBehavior S) (i : Agent) (p h : S.History) :
    (S.toActionFrame B).enacted i (some p) h = .idle := rfl

end FinitePhysicalChoiceStage

end Praxeology

end
