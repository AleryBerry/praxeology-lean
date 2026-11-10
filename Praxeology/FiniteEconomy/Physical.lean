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

/-- Transfer an existing physical stock without a victim action. The step is
rejected when the parties coincide or the victim lacks the requested stock.
This is a physical transition, not evidence that the transfer is lawful or
that the victim consented. -/
def seize [DecidableEq Agent] [DecidableEq Means]
    (S : PhysicalState Agent Means Service) (actor victim : Agent)
    (good : Means) (quantity : ℕ) : PhysicalState Agent Means Service :=
  if actor ≠ victim ∧ quantity ≤ S.stock victim good then
    { S with stock := Function.update
        (Function.update S.stock victim
          (Function.update (S.stock victim) good (S.stock victim good - quantity)))
        actor (Function.update (S.stock actor) good (S.stock actor good + quantity)) }
  else S

/-- A successful unilateral transfer reduces the victim's stock by the
transferred quantity. No action by the victim is an input to the transition. -/
theorem seize_victim_balance [DecidableEq Agent] [DecidableEq Means]
    (S : PhysicalState Agent Means Service) (actor victim : Agent)
    (good : Means) (quantity : ℕ)
    (hne : actor ≠ victim) (hstock : quantity ≤ S.stock victim good) :
    (S.seize actor victim good quantity).stock victim good + quantity =
      S.stock victim good := by
  simp [seize, hne, hne.symm, hstock, Nat.sub_add_cancel hstock]

/-- The same transition credits the aggressor with the quantity removed. -/
theorem seize_actor_balance [DecidableEq Agent] [DecidableEq Means]
    (S : PhysicalState Agent Means Service) (actor victim : Agent)
    (good : Means) (quantity : ℕ)
    (hne : actor ≠ victim) (hstock : quantity ≤ S.stock victim good) :
    (S.seize actor victim good quantity).stock actor good =
      S.stock actor good + quantity := by
  simp [seize, hne, hstock]

/-- The two agents' aggregate stock is conserved by the transfer. -/
theorem seize_conserves_pair [DecidableEq Agent] [DecidableEq Means]
    (S : PhysicalState Agent Means Service) (actor victim : Agent)
    (good : Means) (quantity : ℕ)
    (hne : actor ≠ victim) (hstock : quantity ≤ S.stock victim good) :
    (S.seize actor victim good quantity).stock victim good +
      (S.seize actor victim good quantity).stock actor good =
      S.stock victim good + S.stock actor good := by
  have hv := S.seize_victim_balance actor victim good quantity hne hstock
  have ha := S.seize_actor_balance actor victim good quantity hne hstock
  omega

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

/-- A successful profile with exactly matched offer and acceptance actions
obeys the bilateral inventory equations. If both sides trade the same good,
the equations record both flows on that coordinate. -/
theorem advanceIfAffordable_matchedTransfer_balance
    [Fintype Agent] [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state next : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (seller buyer : Agent) (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means)
    (hstep : advanceIfAffordable operations state profile = some next)
    (hoff : profile seller =
      EconomyAction.offer seller buyer soldQuantity soldGood paidQuantity paidGood)
    (haccept : profile buyer =
      EconomyAction.accept buyer seller soldQuantity soldGood paidQuantity paidGood) :
    (∀ m, next.stock seller m + (if m = soldGood then soldQuantity else 0) =
      state.stock seller m + (if m = paidGood then paidQuantity else 0)) ∧
    (∀ m, next.stock buyer m + (if m = paidGood then paidQuantity else 0) =
      state.stock buyer m + (if m = soldGood then soldQuantity else 0)) := by
  have hbalances := advanceIfAffordable_sound operations state next profile hstep
  constructor
  · intro m
    simpa [effectiveUse, effectiveYield, hoff, haccept] using
      hbalances seller m
  · intro m
    simpa [effectiveUse, effectiveYield, hoff, haccept] using
      hbalances buyer m

/-- A successful matched bilateral transfer preserves the two parties'
combined stock of every good. This holds when the sold and paid goods are the
same as well as when they differ. -/
theorem advanceIfAffordable_matchedTransfer_pair_conservation
    [Fintype Agent] [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation]
    (operations : OperationSemantics Operation Means Service)
    (state next : PhysicalState Agent Means Service)
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation))
    (seller buyer : Agent) (soldQuantity : ℕ) (soldGood : Means)
    (paidQuantity : ℕ) (paidGood : Means)
    (hstep : advanceIfAffordable operations state profile = some next)
    (hoff : profile seller =
      EconomyAction.offer seller buyer soldQuantity soldGood paidQuantity paidGood)
    (haccept : profile buyer =
      EconomyAction.accept buyer seller soldQuantity soldGood paidQuantity paidGood) :
    ∀ m, next.stock seller m + next.stock buyer m =
      state.stock seller m + state.stock buyer m := by
  intro m
  obtain ⟨hseller, hbuyer⟩ := advanceIfAffordable_matchedTransfer_balance
    operations state next profile seller buyer soldQuantity soldGood paidQuantity
    paidGood hstep hoff haccept
  have hseller := hseller m
  have hbuyer := hbuyer m
  omega

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

namespace FinitePhysicalProgram

variable {T : FiniteTreeSpec} {Agent Means Operation Service : Type}
variable [Fintype Agent] [Fintype Means] [DecidableEq Agent]
  [DecidableEq Means] [DecidableEq Operation]

/-- If the parent and child runs both succeed, the enacted profile passed the
interpreter's affordability check. -/
theorem edge_affordable_of_successful_child
    (P : FinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) {t : T.Node} (ht0 : t ≠ 0)
    {before after : PhysicalState Agent Means Service}
    (hbefore : P.runAt h (T.parent t) = some before)
    (hafter : P.runAt h t = some after) :
    profileAffordable? P.operations before
      (P.actionProfile h (T.parent t)) = true := by
  rw [FinitePhysicalProgram.runAt.eq_1, dite_eq_right ht0, hbefore] at hafter
  unfold advanceIfAffordable at hafter
  by_cases ha : profileAffordable? P.operations before
      (P.actionProfile h (T.parent t)) = true
  · exact ha
  · simp [ha] at hafter

end FinitePhysicalProgram

/-- A solvent finite physical execution. Its local edge-affordability
certificate lets the existing interpreter generate a state at every node of
every history; it adds no transition rule or economic assumption. -/
structure SolventFinitePhysicalProgram (T : FiniteTreeSpec)
    (Agent Means Operation Service : Type)
    [Fintype Agent] [Fintype Means] [DecidableEq Agent]
    [DecidableEq Means] [DecidableEq Operation] where
  execution : FinitePhysicalProgram T Agent Means Operation Service
  /-- Every enacted parent-to-child profile is affordable from the state
  already generated at its parent. -/
  edge_affordable : ∀ h t (_ht : T.MemHist t h) (_ht0 : t ≠ 0) state,
    execution.runAt h (T.parent t) = some state →
    profileAffordable? execution.operations state
      (execution.actionProfile h (T.parent t)) = true

namespace SolventFinitePhysicalProgram

variable {T : FiniteTreeSpec} {Agent Means Operation Service : Type}
variable [Fintype Agent] [Fintype Means] [DecidableEq Agent]
  [DecidableEq Means] [DecidableEq Operation]

/-- Package an all-history successful run. Local affordability then follows
from the interpreter's rule for accepting a parent-to-child transition. -/
def ofSuccessfulAt
    (execution : FinitePhysicalProgram T Agent Means Operation Service)
    (successful_at : ∀ h t, T.MemHist t h →
      ∃ state, execution.runAt h t = some state) :
    SolventFinitePhysicalProgram T Agent Means Operation Service where
  execution := execution
  edge_affordable := by
    intro h t _ht ht0 state hbefore
    obtain ⟨after, hafter⟩ := successful_at h t _ht
    exact execution.edge_affordable_of_successful_child h ht0 hbefore hafter

/-- The edge-affordability certificate recursively guarantees a physical
state along every history prefix. -/
theorem successful_at
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) (t : T.Node) (ht : T.MemHist t h) :
    ∃ state, P.execution.runAt h t = some state := by
  have haux : ∀ n, ∀ (t : T.Node), t.val = n → ∀ h : T.History,
      T.MemHist t h → ∃ state, P.execution.runAt h t = some state := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t htval h hmem
        by_cases ht0 : t = 0
        · subst t
          exact ⟨P.execution.initialState, P.execution.runAt_root h⟩
        · have hparent_lt : (T.parent t).val < n := by
            rw [← htval]
            exact T.parent_decreases t ht0
          have hparent_mem : T.MemHist (T.parent t) h := by
            exact T.ancestor_trans
              (T.ancestor_of_parent ht0 (T.ancestor_refl (T.parent t))) hmem
          obtain ⟨parentState, hparent_run⟩ :=
            ih (T.parent t).val hparent_lt (T.parent t) rfl h hparent_mem
          have hprofile := P.edge_affordable h t hmem ht0 parentState hparent_run
          have hchild_run : P.execution.runAt h t = some
              (advanceState P.execution.operations parentState
                (P.execution.actionProfile h (T.parent t))
                (SolventProfile.ofAffordable P.execution.operations parentState
                  (P.execution.actionProfile h (T.parent t))
                  (profileAffordable_of_true P.execution.operations parentState
                    (P.execution.actionProfile h (T.parent t)) hprofile))) := by
            simp only [FinitePhysicalProgram.runAt, dite_eq_right ht0,
              hparent_run, advanceIfAffordable, hprofile, dite_true]
          exact ⟨_, hchild_run⟩
  exact haux t.val t rfl h ht

/-- Read the generated physical state after edge affordability has established
that the interpreter returns one. -/
def stateAt
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) (t : T.Node) (ht : T.MemHist t h) :
    PhysicalState Agent Means Service :=
  (P.execution.runAt h t).get (by
    cases hrun : P.execution.runAt h t with
    | none =>
        obtain ⟨state, hstate⟩ := P.successful_at h t ht
        simp [hrun] at hstate
    | some _ => rfl)

/-- The total state view is exactly the state returned by the original
affordability-checked interpreter. -/
theorem runAt_stateAt
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) (t : T.Node) (ht : T.MemHist t h) :
    P.execution.runAt h t = some (P.stateAt h t ht) := by
  cases hrun : P.execution.runAt h t with
  | none =>
      obtain ⟨state, hstate⟩ := P.successful_at h t ht
      simp [hrun] at hstate
  | some state => simp [stateAt, hrun]

/-- The generated root state is the declared initial state. -/
theorem stateAt_root
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) (hroot : T.MemHist 0 h) :
    P.stateAt h 0 hroot = P.execution.initialState := by
  have hrun := P.runAt_stateAt h 0 hroot
  rw [P.execution.runAt_root] at hrun
  exact Option.some.inj hrun.symm

/-- Histories that share a node have the same generated physical state there.
This is inherited from prefix-consistent action profiles in the interpreter.
-/
theorem stateAt_bundle_invariant
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    {t : T.Node} {h₁ h₂ : T.History}
    (hmem₁ : T.MemHist t h₁) (hmem₂ : T.MemHist t h₂) :
    P.stateAt h₁ t hmem₁ = P.stateAt h₂ t hmem₂ := by
  have h₁run := P.runAt_stateAt h₁ t hmem₁
  have h₂run := P.runAt_stateAt h₂ t hmem₂
  have hsame := P.execution.runAt_bundle_invariant hmem₁ hmem₂
  exact Option.some.inj (h₁run.symm.trans (hsame.trans h₂run))

/-- Every generated parent-child transition has the interpreter's exact
inventory balance for each agent and means coordinate. -/
theorem stateAt_edge_balance
    (P : SolventFinitePhysicalProgram T Agent Means Operation Service)
    (h : T.History) {t : T.Node} (ht : T.MemHist t h) (ht0 : t ≠ 0) :
    ∀ actor m,
      (P.stateAt h t ht).stock actor m +
          effectiveUse P.execution.operations
            (P.execution.actionProfile h (T.parent t)) actor m =
        (P.stateAt h (T.parent t) (by
          exact T.ancestor_trans
            (T.ancestor_of_parent ht0 (T.ancestor_refl (T.parent t))) ht)).stock actor m +
          effectiveYield P.execution.operations
            (P.execution.actionProfile h (T.parent t)) actor m := by
  have hparent_mem : T.MemHist (T.parent t) h := by
    exact T.ancestor_trans
      (T.ancestor_of_parent ht0 (T.ancestor_refl (T.parent t))) ht
  apply P.execution.runAt_edge_balance h ht0
  · exact P.runAt_stateAt h (T.parent t) hparent_mem
  · exact P.runAt_stateAt h t ht

end SolventFinitePhysicalProgram

/-- A profile is correctly owned and contains no self-trade. -/
def WellFormedProfile [DecidableEq Agent]
    (profile : ActionProfile (Agent := Agent) (Means := Means)
      (Operation := Operation)) : Prop :=
  ∀ actor, (profile actor).WellFormed actor

end Praxeology

end
