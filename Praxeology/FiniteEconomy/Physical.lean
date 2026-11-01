/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.ExactNat
public import Praxeology.Frame.Core
public import Praxeology.FiniteEconomy.Tree

/-!
# Executable physical economy semantics

This module defines actions and inventory transitions independently of
`InventoryStep`.  It can therefore be used to build the physical fields of an
`ActionFrame`; the `InventoryStep` adapter lives downstream of `Frame`.
-/

@[expose] public section

namespace Praxeology

/-- Common finite-economy actions.  The action type need not be finite: menus
are finite even though trade quantities range over all natural numbers. -/
inductive EconomyAction (Agent Means Operation : Type)
    where
  | idle
  | operate (operation : Operation)
  | offer (seller buyer : Agent)
      (soldQuantity : ℕ) (soldGood : Means)
      (paidQuantity : ℕ) (paidGood : Means)
  | accept (buyer seller : Agent)
      (soldQuantity : ℕ) (soldGood : Means)
      (paidQuantity : ℕ) (paidGood : Means)
  deriving DecidableEq

namespace EconomyAction

variable {Agent Means Operation : Type}

/-- An action profile may contain only offers made by their seller and
acceptances made by their buyer. Self-trades are excluded at the data boundary. -/
def WellFormed [DecidableEq Agent]
    (actor : Agent) : EconomyAction Agent Means Operation → Prop
  | .idle => True
  | .operate _ => True
  | .offer seller buyer _ _ _ _ => actor = seller ∧ seller ≠ buyer
  | .accept buyer seller _ _ _ _ => actor = buyer ∧ buyer ≠ seller

end EconomyAction

/-- Physical and service consequences of a productive operation. -/
structure OperationSemantics (Operation Means Service : Type) where
  input : Operation → Means → ℕ
  output : Operation → Means → ℕ
  service : Operation → Service → ℕ

/-- Physical and service stocks at one node. -/
structure PhysicalState (Agent Means Service : Type) where
  stock : Agent → Means → ℕ
  services : Agent → Service → ℕ

namespace PhysicalState

variable {Agent Means Service : Type}

/-- A total inventory ledger with no services. -/
def zeroServices (stock : Agent → Means → ℕ) : PhysicalState Agent Means Service :=
  ⟨stock, fun _ _ => 0⟩

end PhysicalState

variable {Agent Means Operation Service : Type}

/-- An enacted profile at one decision node. -/
abbrev ActionProfile := Agent → EconomyAction Agent Means Operation

/-- Raw pre-transition requirements, including operation inputs and the full
requirements of contemplated offers and acceptances. An incoming transfer
never finances an action in the same transition. -/
def rawActionUse [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (α : EconomyAction Agent Means Operation) (m : Means) : ℕ :=
  match α with
  | .idle => 0
  | .operate op => operations.input op m
  | .offer _ _ q good _ _ => if m = good then q else 0
  | .accept _ _ _ _ q good => if m = good then q else 0

/-- Raw productive and contemplated-trade outputs. An unmatched trade does
not realize these outputs. -/
def rawActionYield [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (α : EconomyAction Agent Means Operation) (m : Means) : ℕ :=
  match α with
  | .idle => 0
  | .operate op => operations.output op m
  | .offer _ _ _ _ q good => if m = good then q else 0
  | .accept _ _ q good _ _ => if m = good then q else 0

/-- The offer and its exact matching acceptance agree on parties, quantities,
and both goods. -/
def OfferMatched (profile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation)) (seller buyer : Agent)
    (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means) : Prop :=
  profile buyer = .accept buyer seller soldQuantity soldGood paidQuantity paidGood

/-- The acceptance and its exact matching offer agree on parties, quantities,
and both goods. -/
def AcceptMatched (profile : ActionProfile (Agent := Agent) (Means := Means)
    (Operation := Operation)) (buyer seller : Agent)
    (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means) : Prop :=
  profile seller = .offer seller buyer soldQuantity soldGood paidQuantity paidGood

/-- Effective input for an enacted action. A trade has a physical effect only
when the counterparty enacts the exactly matching action in this profile. -/
def effectiveUse [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) (actor : Agent) (m : Means) : ℕ :=
  match profile actor with
  | .idle => 0
  | .operate op => operations.input op m
  | .offer seller buyer soldQuantity soldGood paidQuantity paidGood =>
      if actor = seller ∧
          profile buyer = .accept buyer seller soldQuantity soldGood paidQuantity paidGood
      then if m = soldGood then soldQuantity else 0
      else 0
  | .accept buyer seller soldQuantity soldGood paidQuantity paidGood =>
      if actor = buyer ∧
          profile seller = .offer seller buyer soldQuantity soldGood paidQuantity paidGood
      then if m = paidGood then paidQuantity else 0
      else 0

/-- Effective output symmetric to `effectiveUse`. -/
def effectiveYield [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) (actor : Agent) (m : Means) : ℕ :=
  match profile actor with
  | .idle => 0
  | .operate op => operations.output op m
  | .offer seller buyer soldQuantity soldGood paidQuantity paidGood =>
      if actor = seller ∧
          profile buyer = .accept buyer seller soldQuantity soldGood paidQuantity paidGood
      then if m = paidGood then paidQuantity else 0
      else 0
  | .accept buyer seller soldQuantity soldGood paidQuantity paidGood =>
      if actor = buyer ∧
          profile seller = .offer seller buyer soldQuantity soldGood paidQuantity paidGood
      then if m = soldGood then soldQuantity else 0
      else 0

/-- Services are yielded by productive operations; trades and idling do not
create consumption services. -/
def effectiveServiceYield (operations : OperationSemantics Operation Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) (actor : Agent) (s : Service) : ℕ :=
  match profile actor with
  | .operate op => operations.service op s
  | _ => 0

/-- Effective matched-trade use never exceeds the action's raw pre-transition
requirement; productive inputs are counted exactly. -/
theorem effectiveUse_le_rawActionUse [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) (actor : Agent) (m : Means) :
    effectiveUse operations profile actor m ≤
      rawActionUse operations (profile actor) m := by
  cases hα : profile actor with
  | idle => simp [effectiveUse, rawActionUse, hα]
  | operate op => simp [effectiveUse, rawActionUse, hα]
  | offer seller buyer soldQuantity soldGood paidQuantity paidGood =>
      by_cases hmatch : actor = seller ∧
          profile buyer = .accept buyer seller soldQuantity soldGood paidQuantity paidGood
      · rcases hmatch with ⟨howner, hpeer⟩
        have hSeller : profile seller =
            .offer seller buyer soldQuantity soldGood paidQuantity paidGood := by
          simpa [howner] using hα
        simp [effectiveUse, rawActionUse, hSeller, howner, hpeer]
      · simp [effectiveUse, rawActionUse, hα, hmatch]
  | accept buyer seller soldQuantity soldGood paidQuantity paidGood =>
      by_cases hmatch : actor = buyer ∧
          profile seller = .offer seller buyer soldQuantity soldGood paidQuantity paidGood
      · rcases hmatch with ⟨howner, hpeer⟩
        have hBuyer : profile buyer =
            .accept buyer seller soldQuantity soldGood paidQuantity paidGood := by
          simpa [howner] using hα
        simp [effectiveUse, rawActionUse, hBuyer, howner, hpeer]
      · simp [effectiveUse, rawActionUse, hα, hmatch]

/-- Test feasibility against raw requirements and the pre-transition stock.
An incoming transfer cannot fund the same transition. -/
def actionAffordable [Fintype Means] [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service) (actor : Agent)
    (α : EconomyAction Agent Means Operation) : Prop :=
  ∀ m, rawActionUse operations α m ≤ state.stock actor m

instance actionAffordableDecidable [Fintype Means] [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service) (actor : Agent)
    (α : EconomyAction Agent Means Operation) :
    Decidable (actionAffordable operations state actor α) := by
  unfold actionAffordable rawActionUse
  infer_instance

/-- Filter a finite contemplated menu by its raw pre-transition requirements.
Unaffordable contemplated actions remain available as separate evidence in
the caller's original menu. -/
def feasibleMenu [Fintype Means] [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service) (actor : Agent)
    (contemplated : Finset (EconomyAction Agent Means Operation)) :
    Finset (EconomyAction Agent Means Operation) :=
  contemplated.filter fun α => actionAffordable operations state actor α

theorem mem_feasibleMenu_iff [Fintype Means] [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service) (actor : Agent)
    (contemplated : Finset (EconomyAction Agent Means Operation))
    (α : EconomyAction Agent Means Operation) :
    α ∈ feasibleMenu operations state actor contemplated ↔
      α ∈ contemplated ∧ actionAffordable operations state actor α := by
  simp [feasibleMenu]

/-- A physically solvent action profile. Solvency is evaluated separately for
each actor using the actual matched-trade flow. -/
structure SolventProfile [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) where
  solvent : ∀ actor m, effectiveUse operations profile actor m ≤ state.stock actor m

/-- Raw affordability of every selected action certifies that its matched
physical flow is solvent. -/
theorem SolventProfile.ofAffordable [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (hAffordable : ∀ actor, actionAffordable operations state actor (profile actor)) :
    SolventProfile operations state profile where
  solvent := by
    intro actor m
    exact le_trans (effectiveUse_le_rawActionUse operations profile actor m)
      (hAffordable actor m)

/-- Apply one complete profile. The exact remainder certificate, rather than
truncated subtraction as an unproved calculation, supplies every next stock. -/
def advanceState [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (solvent : SolventProfile operations state profile) :
    PhysicalState Agent Means Service :=
  { stock := fun actor m =>
      (NatRemainder.ofLE (state.stock actor m)
        (effectiveUse operations profile actor m) (solvent.solvent actor m)).remaining
        + effectiveYield operations profile actor m
    services := fun actor s =>
      state.services actor s + effectiveServiceYield operations profile actor s }

/-- Exact additive physical accounting for every means coordinate. -/
theorem advanceState_balance [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (solvent : SolventProfile operations state profile)
    (actor : Agent) (m : Means) :
    (advanceState operations state profile solvent).stock actor m
        + effectiveUse operations profile actor m =
      state.stock actor m + effectiveYield operations profile actor m := by
  have h := (NatRemainder.ofLE (state.stock actor m)
    (effectiveUse operations profile actor m) (solvent.solvent actor m)).balance
  dsimp [advanceState]
  omega

/-- Service accumulation follows the same fixed transition rule for every
profile. -/
theorem advanceState_service_balance [DecidableEq Agent] [DecidableEq Means]
    [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (solvent : SolventProfile operations state profile)
    (actor : Agent) (s : Service) :
    (advanceState operations state profile solvent).services actor s =
      state.services actor s + effectiveServiceYield operations profile actor s := rfl

/-- Decide raw affordability of a complete profile by scanning the finite
agent and means types. This uses executable boolean reflection rather than
generating one tactic goal for each pair. -/
def profileAffordable? [Fintype Agent] [Fintype Means] [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) : Bool :=
  decide (∀ actor m, rawActionUse operations (profile actor) m ≤ state.stock actor m)

/-- A positive result from the finite affordability scan yields the proof
needed to execute the exact transition. -/
theorem profileAffordable_of_true [Fintype Agent] [Fintype Means]
    [DecidableEq Means]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (h : profileAffordable? operations state profile = true) :
    ∀ actor, actionAffordable operations state actor (profile actor) := by
  have hAll : ∀ actor m,
      rawActionUse operations (profile actor) m ≤ state.stock actor m :=
    of_decide_eq_true h
  intro actor m
  exact hAll actor m

/-- Execute one complete profile if all raw requirements fit the pre-state.
The failure branch is explicit, and success carries the exact solvent proof. -/
def advanceIfAffordable [Fintype Agent] [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) : Option (PhysicalState Agent Means Service) :=
  if h : profileAffordable? operations state profile = true then
    some (advanceState operations state profile
      (SolventProfile.ofAffordable operations state profile
        (profileAffordable_of_true operations state profile h)))
  else none

/-- Every successful executable profile transition satisfies exact additive
inventory accounting for all agents and means. -/
theorem advanceIfAffordable_sound [Fintype Agent] [Fintype Means]
    [DecidableEq Agent] [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state next : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (hstep : advanceIfAffordable operations state profile = some next) :
    ∀ actor m, next.stock actor m + effectiveUse operations profile actor m =
      state.stock actor m + effectiveYield operations profile actor m := by
  unfold advanceIfAffordable at hstep
  split_ifs at hstep with ha
  · have hnext := Option.some.inj hstep
    subst next
    intro actor m
    exact advanceState_balance operations state profile
      (SolventProfile.ofAffordable operations state profile
        (profileAffordable_of_true operations state profile ha)) actor m

/-- Declarative finite physical execution data. The specification records only
the root state and the complete enacted profile at each node and history;
later stocks are computed by the recursive parent fold below. -/
structure FinitePhysicalProgram (T : FiniteTreeSpec)
    (Agent Means Operation Service : Type)
    [Fintype Agent] [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation] where
  operations : OperationSemantics Operation Means Service
  initialState : PhysicalState Agent Means Service
  actionProfile : T.History → T.Node →
    ActionProfile (Agent := Agent) (Means := Means) (Operation := Operation)
  profile_wellFormed : ∀ h t actor, (actionProfile h t actor).WellFormed actor
  profile_bundle_invariant : ∀ t h₁ h₂, T.MemHist t h₁ → T.MemHist t h₂ →
    actionProfile h₁ t = actionProfile h₂ t

namespace FinitePhysicalProgram

variable {T : FiniteTreeSpec} {Agent Means Operation Service : Type}
variable [Fintype Agent] [Fintype Means] [DecidableEq Agent]
  [DecidableEq Means] [DecidableEq Operation]

/-- Run to a node by following its unique parent chain. Each edge scans the
complete profile against the pre-state; an unaffordable profile produces
`none` and cannot use same-transition inflows to pass the check. -/
def runAt (P : FinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) : (t : T.Node) →
      Option (PhysicalState Agent Means Service)
  | t =>
      if _ht : t = 0 then some P.initialState
      else
        match runAt P h (T.parent t) with
        | none => none
        | some state =>
            advanceIfAffordable P.operations state
              (P.actionProfile h (T.parent t))
termination_by t => t.val
decreasing_by
  exact T.parent_decreases t _ht

/-- The root run starts at the declared primitive endowment. -/
theorem runAt_root (P : FinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) : P.runAt h 0 = some P.initialState := by
  simp [runAt]

/-- At any node shared by two histories, the compiled physical state is
identical. Prefix-consistent profiles and deterministic transitions guarantee
that branching cannot change stocks in the common past. -/
theorem runAt_bundle_invariant (P : FinitePhysicalProgram T Agent Means Operation Service)
    {t : T.Node} {h₁ h₂ : T.History}
    (hmem₁ : T.MemHist t h₁) (hmem₂ : T.MemHist t h₂) :
    P.runAt h₁ t = P.runAt h₂ t := by
  have haux : ∀ n, ∀ (t : T.Node), t.val = n →
      ∀ {h₁ h₂ : T.History}, T.MemHist t h₁ → T.MemHist t h₂ →
        P.runAt h₁ t = P.runAt h₂ t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t ht h₁ h₂ hmem₁ hmem₂
        by_cases ht0 : t = 0
        · subst t
          simp [runAt]
        · have hp_lt : (T.parent t).val < n := by
            rw [← ht]
            exact T.parent_decreases t ht0
          have hparent₁ : T.MemHist (T.parent t) h₁ := by
            exact T.ancestor_trans
              (T.ancestor_of_parent ht0 (T.ancestor_refl (T.parent t))) hmem₁
          have hparent₂ : T.MemHist (T.parent t) h₂ := by
            exact T.ancestor_trans
              (T.ancestor_of_parent ht0 (T.ancestor_refl (T.parent t))) hmem₂
          have hrun := ih (T.parent t).val hp_lt (T.parent t) rfl hparent₁ hparent₂
          have hprofile := P.profile_bundle_invariant (T.parent t) h₁ h₂
            hparent₁ hparent₂
          conv_lhs => rw [runAt]
          conv_rhs => rw [runAt]
          simp only [dite_eq_right ht0, hrun, hprofile]
  exact haux t.val t rfl hmem₁ hmem₂

/-- A successful parent-to-child run has exact physical accounting for every
agent and means coordinate. -/
theorem runAt_edge_balance (P : FinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) {t : T.Node} (ht0 : t ≠ 0)
    {before after : PhysicalState Agent Means Service}
    (hbefore : P.runAt h (T.parent t) = some before)
    (hafter : P.runAt h t = some after) :
    ∀ actor m,
      after.stock actor m + effectiveUse P.operations
        (P.actionProfile h (T.parent t)) actor m =
      before.stock actor m + effectiveYield P.operations
        (P.actionProfile h (T.parent t)) actor m := by
  have hrun := hafter
  rw [runAt] at hrun
  simp only [dite_eq_right ht0, hbefore] at hrun
  exact advanceIfAffordable_sound P.operations before after
    (P.actionProfile h (T.parent t)) hrun

end FinitePhysicalProgram

/-- A profile is correctly owned and contains no self-trade. -/
def WellFormedProfile [DecidableEq Agent]
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) : Prop :=
  ∀ actor, (profile actor).WellFormed actor

end Praxeology

end
