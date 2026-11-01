/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action

/-!
# Epistemic Ability: Knowledge, Belief, and Action

This module formalizes the epistemic foundations of purposeful action,
including subjective knowledge, ability, and decision-making under uncertainty.
-/

@[expose] public section


namespace Praxeology

/-- An equivalence relation on decision indices or signals. -/
structure KnowledgeRelation (V Index : Type) where
  indistinguishable : V → Index → Index → Prop
  refl : ∀ i x, indistinguishable i x x
  symm : ∀ i x y, indistinguishable i x y → indistinguishable i y x
  trans : ∀ i x y z, indistinguishable i x y → indistinguishable i y z → indistinguishable i x z

/-- `P` holds at every index indistinguishable from `x`. -/
def Knows {V Index : Type}
    (K : KnowledgeRelation V Index)
    (i : V) (x : Index) (P : Index → Prop) : Prop :=
  ∀ y, K.indistinguishable i x y → P y

section ActionFrameAbility

variable [W : ActionFrame]

/-- Action α guarantees P in ActionFrame W exactly when α is feasible and P holds
on all decision indices in the choice cell of α. -/
def Guarantees (i : W.Agent) (x : W.DecisionIndex) (α : W.Action)
    (P : W.DecisionIndex → Prop) : Prop :=
  α ∈ W.A_feas i x.moment x.history ∧
  ∀ y : W.DecisionIndex, y.moment = x.moment → W.enacted i y.moment y.history = α → P y

/-- Some feasible action in ActionFrame W guarantees P. -/
def CausalAbility (i : W.Agent) (x : W.DecisionIndex) (P : W.DecisionIndex → Prop) : Prop :=
  ∃ α, Guarantees i x α P

/-- An agent with knowledge relation K has KnowHow for P at decision index x if
there is a single action α that guarantees P at every index indistinguishable from x. -/
def KnowHow (K : KnowledgeRelation W.Agent W.DecisionIndex)
    (i : W.Agent) (x : W.DecisionIndex) (P : W.DecisionIndex → Prop) : Prop :=
  ∃ α, ∀ y, K.indistinguishable i x y → Guarantees i y α P

theorem knowHow_implies_causalAbility
    (K : KnowledgeRelation W.Agent W.DecisionIndex)
    (i : W.Agent) (x : W.DecisionIndex) (P : W.DecisionIndex → Prop)
    (h : KnowHow K i x P) : CausalAbility i x P := by
  rcases h with ⟨α, hα⟩
  exact ⟨α, hα x (K.refl i x)⟩

theorem knowHow_implies_knows_causalAbility
    (K : KnowledgeRelation W.Agent W.DecisionIndex)
    (i : W.Agent) (x : W.DecisionIndex) (P : W.DecisionIndex → Prop)
    (h : KnowHow K i x P) : Knows K i x (fun y => CausalAbility i y P) := by
  rcases h with ⟨α, hα⟩
  intro y hxy
  exact ⟨α, hα y hxy⟩

end ActionFrameAbility

end Praxeology
