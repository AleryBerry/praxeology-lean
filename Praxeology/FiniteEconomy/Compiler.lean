/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Physical
public import Mathlib.Data.Finset.Pi

/-!
# Finite economy compiler foundations

This module begins the recipe-side compiler interface. A stage stores only
finite per-agent menus. The complete profile set is the dependent product of
those menus, so unilateral alternatives are closed by construction instead
of being listed by hand.
-/

@[expose] public section

namespace Praxeology

/-- One decision stage with finite contemplated menus and sparse activity.
Agents outside `activeAgents` can only idle. The activity bound is an explicit
scenario parameter, normally set to two for generated economic recipes. -/
structure FiniteChoiceStage (Agent Means Operation : Type)
    [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation] where
  menu : Agent → Finset (EconomyAction Agent Means Operation)
  idle_mem : ∀ i, .idle ∈ menu i
  activeAgents : Finset Agent
  active_iff : ∀ i, i ∈ activeAgents ↔
    ∃ α ∈ menu i, α ≠ EconomyAction.idle
  maxActiveAgents : ℕ
  activity_bound : activeAgents.card ≤ maxActiveAgents
  menu_wellFormed : ∀ i α, α ∈ menu i → EconomyAction.WellFormed i α

namespace FiniteChoiceStage

variable {Agent Means Operation : Type}
variable [Fintype Agent] [DecidableEq Agent] [DecidableEq Means]
  [DecidableEq Operation]

/-- The terminal choice context contains only the already-required passive
action. -/
def idleOnly : FiniteChoiceStage Agent Means Operation where
  menu := fun _ => {EconomyAction.idle}
  idle_mem := by intro i; simp
  activeAgents := ∅
  active_iff := by
    intro i
    simp
  maxActiveAgents := 0
  activity_bound := by simp
  menu_wellFormed := by
    intro i α hα
    simp only [Finset.mem_singleton] at hα
    subst α
    simp [EconomyAction.WellFormed]

/-- Build a sparse finite menu around one selected complete profile. Agents
listed in `activeAgents` may either enact their selected action or idle;
everyone else can only idle. This constructor is useful for compiler-generated
spines whose unselected menu alternatives must remain explicit branches. -/
def ofProfile (profile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation)) (activeAgents : Finset Agent)
    (profile_nonidle : ∀ i ∈ activeAgents, profile i ≠ EconomyAction.idle)
    (profile_wellFormed : ∀ i, EconomyAction.WellFormed i (profile i)) :
    FiniteChoiceStage Agent Means Operation where
  menu i := if i ∈ activeAgents then {EconomyAction.idle, profile i}
    else {EconomyAction.idle}
  idle_mem := by
    intro i
    by_cases hi : i ∈ activeAgents <;> simp [hi]
  activeAgents := activeAgents
  active_iff := by
    intro i
    constructor
    · intro hi
      exact ⟨profile i, by simp [hi], profile_nonidle i hi⟩
    · rintro ⟨α, hα, hα_ne⟩
      by_cases hi : i ∈ activeAgents
      · exact hi
      · have hαeq : α = EconomyAction.idle := by
          simpa [hi] using hα
        subst α
        exact (hα_ne rfl).elim
  maxActiveAgents := activeAgents.card
  activity_bound := le_rfl
  menu_wellFormed := by
    intro i α hα
    by_cases hi : i ∈ activeAgents
    · rw [ite_eq_left hi] at hα
      simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with hα | hα
      · subst α
        simp [EconomyAction.WellFormed]
      · subst α
        exact profile_wellFormed i
    · rw [ite_eq_right hi] at hα
      simp only [Finset.mem_singleton] at hα
      subst α
      simp [EconomyAction.WellFormed]

/-- A dependent full-agent profile with one action selected from every
agent's menu. -/
def Profile (S : FiniteChoiceStage Agent Means Operation) :=
  {p : ActionProfile (Agent := Agent) (Means := Means) (Operation := Operation) //
    ∀ i, p i ∈ S.menu i}

instance profileDecidableEq (S : FiniteChoiceStage Agent Means Operation) :
    DecidableEq S.Profile := by
  unfold Profile
  infer_instance

/-- Turn one member of the dependent finite product into a typed profile. -/
def profileOf (S : FiniteChoiceStage Agent Means Operation)
    (f : {p : (i : Agent) → i ∈ Finset.univ → EconomyAction Agent Means Operation //
      p ∈ Finset.univ.pi S.menu}) : S.Profile :=
  ⟨fun i => f.1 i (Finset.mem_univ i), fun i =>
    (Finset.mem_pi.mp f.2) i (Finset.mem_univ i)⟩

/-- Enumerate every simultaneous choice profile by taking the dependent
product of the individual finite menus. No `Fintype` instance for the
potentially infinite action type is needed. -/
def profiles (S : FiniteChoiceStage Agent Means Operation) : Finset S.Profile :=
  (Finset.univ.pi S.menu).attach.image S.profileOf

/-- Every pointwise menu profile is represented in the enumerated product. -/
theorem mem_profiles (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) : p ∈ S.profiles := by
  rw [profiles, Finset.mem_image]
  refine ⟨⟨fun i _ => p.1 i, Finset.mem_pi.mpr (fun i _ => p.2 i)⟩,
    Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  funext i
  rfl

/-- Every stage has at least one complete profile: all agents may choose idle. -/
theorem profiles_nonempty (S : FiniteChoiceStage Agent Means Operation) :
    S.profiles.Nonempty := by
  let p : S.Profile := ⟨fun _ => EconomyAction.idle, S.idle_mem⟩
  exact ⟨p, S.mem_profiles p⟩

/-- An inactive agent's menu consists exactly of the idle action. -/
theorem inactive_menu_eq_idle (S : FiniteChoiceStage Agent Means Operation)
    {i : Agent} (hi : i ∉ S.activeAgents) :
    S.menu i = {EconomyAction.idle} := by
  ext α
  simp only [Finset.mem_singleton]
  constructor
  · intro hα
    by_contra hne
    exact hi ((S.active_iff i).2 ⟨α, hα, hne⟩)
  · intro hα
    subst α
    exact S.idle_mem i

/-- Any generated profile is correctly owned by its actor and has no
self-trade, by the stage's local menu validation. -/
theorem profile_wellFormed (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) (i : Agent) :
    EconomyAction.WellFormed i (p.1 i) :=
  S.menu_wellFormed i (p.1 i) (p.2 i)

/-- Replace one actor's choice while holding every other actor's action fixed. -/
def replaceProfile (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) (i : Agent)
    (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) : S.Profile :=
  ⟨Function.update p.1 i α, by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hα
    · simpa [Function.update, hji] using p.2 j⟩

@[simp]
theorem replaceProfile_self (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) (i : Agent)
    (α : EconomyAction Agent Means Operation) (_hα : α ∈ S.menu i) :
    (S.replaceProfile p i α _hα).1 i = α := by
  simp [replaceProfile]

theorem replaceProfile_other (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) {i j : Agent}
    (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i)
    (hji : j ≠ i) :
    (S.replaceProfile p i α hα).1 j = p.1 j := by
  simp [replaceProfile, hji]

/-- Construct a complete profile where one agent chooses a listed action and
every other agent chooses the already required idle action. -/
def unilateralProfile (S : FiniteChoiceStage Agent Means Operation)
    (i : Agent) (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) :
    S.Profile :=
  S.replaceProfile ⟨fun _ => EconomyAction.idle, S.idle_mem⟩ i α hα

@[simp]
theorem unilateralProfile_self (S : FiniteChoiceStage Agent Means Operation)
    (i : Agent) (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) :
    (S.unilateralProfile i α hα).1 i = α := by
  exact S.replaceProfile_self _ _ _ _

theorem unilateralProfile_other (S : FiniteChoiceStage Agent Means Operation)
    (i j : Agent) (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i)
    (hji : j ≠ i) :
    (S.unilateralProfile i α hα).1 j = EconomyAction.idle := by
  simp [unilateralProfile, replaceProfile, hji]

/-- Every listed individual action occurs in a complete profile where all
other agents idle. Thus independent-choice stages explicitly retain unilateral
alternatives; this follows from `idle_mem` and the full menu product. -/
theorem unilateralProfile_mem_profiles (S : FiniteChoiceStage Agent Means Operation)
    (i : Agent) (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) :
    S.unilateralProfile i α hα ∈ S.profiles :=
  S.mem_profiles (S.unilateralProfile i α hα)

/-- Existential form of the unilateral-profile construction, exposing both
the selected action and the idle choices of every other agent. -/
theorem exists_unilateral_profile (S : FiniteChoiceStage Agent Means Operation)
    (i : Agent) (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) :
    ∃ p ∈ S.profiles, p.1 i = α ∧
      ∀ j, j ≠ i → p.1 j = EconomyAction.idle := by
  refine ⟨S.unilateralProfile i α hα, S.unilateralProfile_mem_profiles i α hα,
    S.unilateralProfile_self i α hα, ?_⟩
  intro j hji
  exact S.unilateralProfile_other i j α hα hji

/-- Independent-choice closure: every contemplated unilateral replacement of
a generated profile is itself a generated profile. -/
theorem replaceProfile_mem_profiles (S : FiniteChoiceStage Agent Means Operation)
    (p : S.Profile) (i : Agent)
    (α : EconomyAction Agent Means Operation) (hα : α ∈ S.menu i) :
    S.replaceProfile p i α hα ∈ S.profiles :=
  S.mem_profiles (S.replaceProfile p i α hα)

end FiniteChoiceStage

/-- A choice stage tied to one physical pre-state. Individual menu actions
must be affordable from that pre-state; complete profiles then execute with
the shared exact physical interpreter. -/
structure FinitePhysicalChoiceStage (Agent Means Operation Service : Type)
    [Fintype Agent] [DecidableEq Agent] [Fintype Means]
    [DecidableEq Means] [DecidableEq Operation] where
  choices : FiniteChoiceStage Agent Means Operation
  operations : OperationSemantics Operation Means Service
  before : PhysicalState Agent Means Service
  menu_affordable : ∀ actor α, α ∈ choices.menu actor →
    actionAffordable operations before actor α

namespace FinitePhysicalChoiceStage

variable {Agent Means Operation Service : Type}
variable [Fintype Agent] [DecidableEq Agent] [Fintype Means]
  [DecidableEq Means] [DecidableEq Operation]

/-- Execute one generated profile. Raw affordability is checked against the
same pre-transition state for every actor, so incoming transfers cannot fund
their own transition. -/
def advance (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : S.choices.Profile) : PhysicalState Agent Means Service :=
  advanceState S.operations S.before profile.1
    (SolventProfile.ofAffordable S.operations S.before profile.1
      (fun actor m => S.menu_affordable actor (profile.1 actor)
        (profile.2 actor) m))

/-- The executable interpreter selects the same transition as the physical
choice stage whenever a profile is drawn from its individually affordable
menus. -/
theorem advanceIfAffordable_eq_some_advance
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : S.choices.Profile) :
    advanceIfAffordable S.operations S.before profile.1 = some (S.advance profile) := by
  have hAffordable : ∀ actor, actionAffordable S.operations S.before actor
      (profile.1 actor) := by
    intro actor m
    exact S.menu_affordable actor (profile.1 actor) (profile.2 actor) m
  have hScan : profileAffordable? S.operations S.before profile.1 = true :=
    decide_eq_true_eq.mpr (by
      intro actor m
      exact hAffordable actor m)
  unfold advanceIfAffordable
  simp only [dite_eq_left hScan]
  congr 1

/-- Every generated physical choice stage satisfies exact additive inventory
accounting. -/
theorem advance_balance
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : S.choices.Profile) (actor : Agent) (m : Means) :
    (S.advance profile).stock actor m +
        effectiveUse S.operations profile.1 actor m =
      S.before.stock actor m + effectiveYield S.operations profile.1 actor m :=
  advanceState_balance S.operations S.before profile.1
    (SolventProfile.ofAffordable S.operations S.before profile.1
      (fun a n => S.menu_affordable a (profile.1 a) (profile.2 a) n)) actor m

/-- Services accumulate by the same fixed rule for every generated profile. -/
theorem advance_service_balance
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : S.choices.Profile) (actor : Agent) (s : Service) :
    (S.advance profile).services actor s =
      S.before.services actor s + effectiveServiceYield S.operations profile.1 actor s :=
  advanceState_service_balance S.operations S.before profile.1
    (SolventProfile.ofAffordable S.operations S.before profile.1
      (fun a n => S.menu_affordable a (profile.1 a) (profile.2 a) n)) actor s

/-- In a unilateral profile, every other agent's physical and service
inventories are unchanged. This follows from the existing idle action and
matched-transfer interpreter: an idle counterparty cannot complete a trade.
-/
theorem unilateralProfile_other_state_eq
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (actor other : Agent) (α : EconomyAction Agent Means Operation)
    (hα : α ∈ S.choices.menu actor) (hother : other ≠ actor) :
    (∀ m, (S.advance (S.choices.unilateralProfile actor α hα)).stock other m =
      S.before.stock other m) ∧
    (∀ service,
      (S.advance (S.choices.unilateralProfile actor α hα)).services other service =
        S.before.services other service) := by
  have h_idle :
      (S.choices.unilateralProfile actor α hα).1 other = EconomyAction.idle :=
    S.choices.unilateralProfile_other actor other α hα hother
  constructor
  · intro m
    have hbalance := S.advance_balance
      (S.choices.unilateralProfile actor α hα) other m
    simpa [effectiveUse, effectiveYield, h_idle] using hbalance
  · intro service
    have hbalance := S.advance_service_balance
      (S.choices.unilateralProfile actor α hα) other service
    simpa [effectiveServiceYield, h_idle] using hbalance

/-- An offer made while every other agent idles is unmatched, so it changes
no agent's stock or service inventory. The counterparty is distinct by the
existing menu well-formedness law; the result follows from the exact-match
physical interpreter. -/
theorem unilateral_offer_state_eq
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (seller buyer : Agent) (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means)
    (hoff : EconomyAction.offer seller buyer soldQuantity soldGood
        paidQuantity paidGood ∈ S.choices.menu seller) :
    ∀ actor,
      (∀ m,
        (S.advance (S.choices.unilateralProfile seller
          (EconomyAction.offer seller buyer soldQuantity soldGood
            paidQuantity paidGood) hoff)).stock actor m =
          S.before.stock actor m) ∧
      (∀ service,
        (S.advance (S.choices.unilateralProfile seller
          (EconomyAction.offer seller buyer soldQuantity soldGood
            paidQuantity paidGood) hoff)).services actor service =
          S.before.services actor service) := by
  let α : EconomyAction Agent Means Operation :=
    EconomyAction.offer seller buyer soldQuantity soldGood paidQuantity paidGood
  let profile := S.choices.unilateralProfile seller α hoff
  have hwell := S.choices.menu_wellFormed seller α hoff
  have hdistinct : seller ≠ buyer := by
    simpa [α, EconomyAction.WellFormed] using hwell.2
  have hoff_self : profile.1 seller = α :=
    S.choices.unilateralProfile_self seller α hoff
  have hidle_buyer : profile.1 buyer = EconomyAction.idle :=
    S.choices.unilateralProfile_other seller buyer α hoff hdistinct.symm
  intro actor
  constructor
  · intro m
    have hbalance := S.advance_balance profile actor m
    by_cases hself : actor = seller
    · subst actor
      simpa [effectiveUse, effectiveYield, hoff_self, hidle_buyer, α] using hbalance
    · have hidle : profile.1 actor = EconomyAction.idle :=
        S.choices.unilateralProfile_other seller actor α hoff hself
      simpa [effectiveUse, effectiveYield, hidle] using hbalance
  · intro service
    have hbalance := S.advance_service_balance profile actor service
    by_cases hself : actor = seller
    · subst actor
      simpa [effectiveServiceYield, hoff_self, α] using hbalance
    · have hidle : profile.1 actor = EconomyAction.idle :=
        S.choices.unilateralProfile_other seller actor α hoff hself
      simpa [effectiveServiceYield, hidle] using hbalance

/-- A unilateral acceptance is likewise unmatched when its prospective seller
idles, so it changes no agent's stock or service inventory. -/
theorem unilateral_accept_state_eq
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (buyer seller : Agent) (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means)
    (haccept : EconomyAction.accept buyer seller soldQuantity soldGood
        paidQuantity paidGood ∈ S.choices.menu buyer) :
    ∀ actor,
      (∀ m,
        (S.advance (S.choices.unilateralProfile buyer
          (EconomyAction.accept buyer seller soldQuantity soldGood
            paidQuantity paidGood) haccept)).stock actor m =
          S.before.stock actor m) ∧
      (∀ service,
        (S.advance (S.choices.unilateralProfile buyer
          (EconomyAction.accept buyer seller soldQuantity soldGood
            paidQuantity paidGood) haccept)).services actor service =
          S.before.services actor service) := by
  let α : EconomyAction Agent Means Operation :=
    EconomyAction.accept buyer seller soldQuantity soldGood paidQuantity paidGood
  let profile := S.choices.unilateralProfile buyer α haccept
  have hwell := S.choices.menu_wellFormed buyer α haccept
  have hdistinct : buyer ≠ seller := by
    simpa [α, EconomyAction.WellFormed] using hwell.2
  have haccept_self : profile.1 buyer = α :=
    S.choices.unilateralProfile_self buyer α haccept
  have hidle_seller : profile.1 seller = EconomyAction.idle :=
    S.choices.unilateralProfile_other buyer seller α haccept hdistinct.symm
  intro actor
  constructor
  · intro m
    have hbalance := S.advance_balance profile actor m
    by_cases hself : actor = buyer
    · subst actor
      simpa [effectiveUse, effectiveYield, haccept_self, hidle_seller, α] using hbalance
    · have hidle : profile.1 actor = EconomyAction.idle :=
        S.choices.unilateralProfile_other buyer actor α haccept hself
      simpa [effectiveUse, effectiveYield, hidle] using hbalance
  · intro service
    have hbalance := S.advance_service_balance profile actor service
    by_cases hself : actor = buyer
    · subst actor
      simpa [effectiveServiceYield, haccept_self, α] using hbalance
    · have hidle : profile.1 actor = EconomyAction.idle :=
        S.choices.unilateralProfile_other buyer actor α haccept hself
      simpa [effectiveServiceYield, hidle] using hbalance

/-- The profile remains well-formed after its physical transition is assembled. -/
theorem profile_wellFormed
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (profile : S.choices.Profile) (actor : Agent) :
    EconomyAction.WellFormed actor (profile.1 actor) :=
  S.choices.menu_wellFormed actor (profile.1 actor) (profile.2 actor)

/-- Every listed individual action has a physically executable unilateral
profile. All other agents use idle, and stock accounting for the resulting
transition follows from the same stage interpreter as simultaneous profiles.
-/
theorem exists_unilateral_action_transition
    (S : FinitePhysicalChoiceStage Agent Means Operation Service)
    (actor : Agent) (α : EconomyAction Agent Means Operation)
    (hα : α ∈ S.choices.menu actor) :
    ∃ profile ∈ S.choices.profiles,
      profile.1 actor = α ∧
      (∀ other, other ≠ actor → profile.1 other = EconomyAction.idle) ∧
      (∀ m, (S.advance profile).stock actor m +
        effectiveUse S.operations profile.1 actor m =
          S.before.stock actor m + effectiveYield S.operations profile.1 actor m) ∧
      (∀ service, (S.advance profile).services actor service =
        S.before.services actor service +
          effectiveServiceYield S.operations profile.1 actor service) := by
  obtain ⟨profile, hprofile, hactor, hothers⟩ :=
    S.choices.exists_unilateral_profile actor α hα
  exact ⟨profile, hprofile, hactor, hothers,
    fun m => S.advance_balance profile actor m,
    fun service => S.advance_service_balance profile actor service⟩

end FinitePhysicalChoiceStage

end Praxeology

end
