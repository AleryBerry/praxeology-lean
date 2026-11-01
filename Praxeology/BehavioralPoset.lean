/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Catallactics
public import Praxeology.EconometricLimits
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.FinCases

/-!
# Behavioral Poset: Reconciling Behavioral Anomalies with Praxeological Posets

This module formalizes contextual framing, loss aversion, hyperbolic discounting,
and precommitment mechanisms, proving that behavioral anomalies are mathematically
compatible with strict partial orders (posets) when grounded in `ActionFrame` decision nodes.
-/

@[expose] public section

namespace Praxeology

/-- A strict asymmetric preference structure on alternatives. -/
structure StrictPreference (α : Type) where
  lt : α → α → Prop
  irrefl : ∀ e, ¬ lt e e
  asymm : ∀ e₁ e₂, lt e₁ e₂ → ¬ lt e₂ e₁

/-- A transitive strict poset on alternatives. -/
structure StrictPoset (α : Type) extends StrictPreference α where
  trans : ∀ e₁ e₂ e₃, lt e₁ e₂ → lt e₂ e₃ → lt e₁ e₃

/-- In any ActionFrame, the subjective preference relation of an agent at a decision node
induces a strict preference structure on ends. -/
def action_frame_strict_preference (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h : W.History) :
    StrictPreference W.Ends where
  lt := W.Preference i t h
  irrefl := fun e => W.pref_irrefl i t h e
  asymm := fun _ _ h1 => W.pref_asymm i t h h1

/-- In an ActionFrame where preferences are transitive, they induce a StrictPoset. -/
def action_frame_strict_poset (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h : W.History)
    (h_trans : ∀ e₁ e₂ e₃, W.Preference i t h e₁ e₂ → W.Preference i t h e₂ e₃ →
      W.Preference i t h e₁ e₃) :
    StrictPoset W.Ends where
  toStrictPreference := action_frame_strict_preference W i t h
  trans := h_trans

/-- Every purposeful action is mathematically governed by a strict preference structure. -/
theorem purposeful_act_instantiates_strict_preference
    [W : ActionFrame] (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action)
    (h_purp : PurposefulAct i t h α) :
    ∃ P : StrictPreference W.Ends,
      P.lt = W.Preference i t h ∧
      (α = W.alpha_zero ∨ P.lt (W.End_of i α t h) (W.End_of i W.alpha_zero t h)) ∧
      (∀ β ∈ W.A_feas i t h, ¬ P.lt (W.End_of i β t h) (W.End_of i α t h)) :=
  ⟨action_frame_strict_preference W i t h, rfl, h_purp.2.2.1, h_purp.2.2.2⟩

/-- Framing reversals: an apparent reversal of preference between two ends requires that
the decision contexts (moment or history) be distinct. -/
theorem framing_reversal_requires_context_distinction
    (W : ActionFrame) (i : W.Agent) (t₁ t₂ : W.Moment) (h₁ h₂ : W.History)
    (e₁ e₂ : W.Ends)
    (h_pref1 : W.Preference i t₁ h₁ e₁ e₂)
    (h_pref2 : W.Preference i t₂ h₂ e₂ e₁) :
    t₁ ≠ t₂ ∨ h₁ ≠ h₂ := by
  by_cases ht : t₁ = t₂
  · by_cases hh : h₁ = h₂
    · subst ht hh
      exact False.elim (W.pref_asymm i t₁ h₁ h_pref1 h_pref2)
    · exact Or.inr hh
  · exact Or.inl ht

/-- Hyperbolic discounting: predictable intertemporal preference shifts between delayed and
immediate consumption ends are compatible with poset asymmetry because they occur
across distinct moments. -/
theorem hyperbolic_reversal_requires_distinct_moments
    (W : ActionFrame) (i : W.Agent) (t₁ t₂ : W.Moment) (h₁ h₂ : W.History)
    (e_delayed e_immediate : W.Ends)
    (h_pref_t1 : W.Preference i t₁ h₁ e_delayed e_immediate)
    (h_pref_t2 : W.Preference i t₂ h₂ e_immediate e_delayed) :
    t₁ ≠ t₂ ∨ h₁ ≠ h₂ :=
  framing_reversal_requires_context_distinction W i t₁ t₂ h₁ h₂
    e_delayed e_immediate h_pref_t1 h_pref_t2

/-- Precommitment mechanism: committing at an earlier moment prunes the temptation choice
from the downstream feasible menu. -/
theorem precommitment_prunes_temptation
    [W : ActionFrame] (i : W.Agent) (t₂ : W.Moment) (h_commit h_uncommitted : W.History)
    (α_consume α_save : W.Action)
    (h_acts_distinct : α_consume ≠ α_save)
    (h_menu_commit : W.A_feas i t₂ h_commit = {α_save})
    (h_menu_uncommitted : W.A_feas i t₂ h_uncommitted = {α_save, α_consume}) :
    α_consume ∉ W.A_feas i t₂ h_commit ∧
    α_consume ∈ W.A_feas i t₂ h_uncommitted := by
  rw [h_menu_commit, h_menu_uncommitted]
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_singleton]
    exact h_acts_distinct
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr trivial

/-- An action frame with precommitment prunes downstream temptation while preserving earlier
intertemporal choice. -/
theorem precommitment_pruning_witness :
    ∃ (W : ActionFrame) (i : W.Agent) (t_uncommitted t_commit : W.Moment) (h : W.History)
      (α_consume : W.Action),
      α_consume ∉ W.A_feas i t_commit h ∧
      α_consume ∈ W.A_feas i t_uncommitted h := by
  let W : ActionFrame := FiniteBranchingModel
  let i : W.Agent := (0 : Fin 2)
  let t_uncommitted : W.Moment := (0 : Fin 4)
  let t_commit : W.Moment := (1 : Fin 4)
  let h : W.History := (0 : Fin 3)
  refine ⟨W, i, t_uncommitted, t_commit, h, ModelAction.consume, ?_, ?_⟩
  · change ModelAction.consume ∉ (if (0 : Fin 2) = 0 ∧ (1 : Fin 4) = 0 then _
      else {ModelAction.idle})
    simp
  · change ModelAction.consume ∈ (if (0 : Fin 2) = 0 ∧ (0 : Fin 4) = 0
      then {ModelAction.idle, ModelAction.consume, ModelAction.defer} else _)
    simp

/-- Loss aversion embedding: reference-dependent valuation is an instance of ActionFrame
contextual valuation across histories with differing initial endowments. -/
theorem loss_aversion_endowment_distinction
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h_gain h_loss : W.History)
    (m : W.Means)
    (h_endow_gain : W.omega i t h_gain m > W.omega i t h_loss m) :
    h_gain ≠ h_loss := by
  rintro rfl
  exact lt_irrefl _ h_endow_gain

/-- Every contextual preference relation in an ActionFrame induces a strict preference structure. -/
theorem contextual_frame_induces_strict_preference
    (W : ActionFrame) (i : W.Agent) (t : W.Moment) (h : W.History) :
    ∃ P : StrictPreference W.Ends, P.lt = W.Preference i t h :=
  ⟨action_frame_strict_preference W i t h, rfl⟩

/-- Bounded contemplation: an action α is purposeful within the feasible menu
(a subset of the finite contemplated menu A_cont) even if an uncontemplated action γ ∉ A_cont
would have yielded a strictly preferred end. -/
theorem bounded_contemplation_purposeful_act
    [W : ActionFrame] (i : W.Agent) (t : W.Moment) (h : W.History) (α : W.Action)
    (h_purp : PurposefulAct i t h α)
    (γ : W.Action) (h_not_cont : γ ∉ W.A_cont i t h) :
    γ ∉ W.A_feas i t h ∧
    (∀ β ∈ W.A_feas i t h, ¬ W.Preference i t h (W.End_of i β t h) (W.End_of i α t h)) := by
  constructor
  · intro h_feas
    have h_cont := ((W.A_feas_coupling i t h γ).mp h_feas).1
    exact h_not_cont h_cont
  · exact h_purp.2.2.2

def p1_rel : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 0, 2 => true
  | _, _ => false

def p2_rel : Fin 3 → Fin 3 → Bool
  | 1, 2 => true
  | 2, 0 => true
  | 1, 0 => true
  | _, _ => false

def p3_rel : Fin 3 → Fin 3 → Bool
  | 2, 0 => true
  | 0, 1 => true
  | 2, 1 => true
  | _, _ => false

def p1_lt (a b : Fin 3) : Prop := p1_rel a b = true
def p2_lt (a b : Fin 3) : Prop := p2_rel a b = true
def p3_lt (a b : Fin 3) : Prop := p3_rel a b = true

instance (a b : Fin 3) : Decidable (p1_lt a b) := inferInstanceAs (Decidable (p1_rel a b = true))
instance (a b : Fin 3) : Decidable (p2_lt a b) := inferInstanceAs (Decidable (p2_rel a b = true))
instance (a b : Fin 3) : Decidable (p3_lt a b) := inferInstanceAs (Decidable (p3_rel a b = true))

/-- First transitive voter preference order for the Condorcet cycle. -/
def CondorcetP1 : StrictPoset (Fin 3) where
  lt := p1_lt
  irrefl := by intro e; fin_cases e <;> decide
  asymm := by intro e₁ e₂; fin_cases e₁ <;> fin_cases e₂ <;> decide
  trans := by intro e₁ e₂ e₃; fin_cases e₁ <;> fin_cases e₂ <;> fin_cases e₃ <;> decide

/-- Second transitive voter preference order for the Condorcet cycle. -/
def CondorcetP2 : StrictPoset (Fin 3) where
  lt := p2_lt
  irrefl := by intro e; fin_cases e <;> decide
  asymm := by intro e₁ e₂; fin_cases e₁ <;> fin_cases e₂ <;> decide
  trans := by intro e₁ e₂ e₃; fin_cases e₁ <;> fin_cases e₂ <;> fin_cases e₃ <;> decide

/-- Third transitive voter preference order for the Condorcet cycle. -/
def CondorcetP3 : StrictPoset (Fin 3) where
  lt := p3_lt
  irrefl := by intro e; fin_cases e <;> decide
  asymm := by intro e₁ e₂; fin_cases e₁ <;> fin_cases e₂ <;> decide
  trans := by intro e₁ e₂ e₃; fin_cases e₁ <;> fin_cases e₂ <;> fin_cases e₃ <;> decide

/-- Majority preference between two alternatives across three strict posets on a type `α`. -/
def MajorityPref {α : Type} (P₁ P₂ P₃ : StrictPoset α) (e₁ e₂ : α) : Prop :=
  (P₁.lt e₁ e₂ ∧ P₂.lt e₁ e₂) ∨ (P₁.lt e₁ e₂ ∧ P₃.lt e₁ e₂) ∨ (P₂.lt e₁ e₂ ∧ P₃.lt e₁ e₂)

/-- Constructive witness of the Condorcet Paradox: three individual transitive strict posets
whose pairwise majority preference relation contains a strict cycle. -/
theorem condorcet_majority_cycle_of_strict_posets :
    ∃ (α : Type) (P₁ P₂ P₃ : StrictPoset α) (e₀ e₁ e₂ : α),
      MajorityPref P₁ P₂ P₃ e₀ e₁ ∧
      MajorityPref P₁ P₂ P₃ e₁ e₂ ∧
      MajorityPref P₁ P₂ P₃ e₂ e₀ := by
  refine ⟨Fin 3, CondorcetP1, CondorcetP2, CondorcetP3, (0 : Fin 3), (1 : Fin 3), (2 : Fin 3), ?_⟩
  refine ⟨Or.inr (Or.inl ⟨rfl, rfl⟩),
          Or.inl ⟨rfl, rfl⟩,
          Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- Majority preference across three agents within an ActionFrame. -/
def ActionFrameMajorityPref [W : ActionFrame] (t : W.Moment) (h : W.History)
    (i₁ i₂ i₃ : W.Agent) (e₁ e₂ : W.Ends) : Prop :=
  (W.Preference i₁ t h e₁ e₂ ∧ W.Preference i₂ t h e₁ e₂) ∨
  (W.Preference i₁ t h e₁ e₂ ∧ W.Preference i₃ t h e₁ e₂) ∨
  (W.Preference i₂ t h e₁ e₂ ∧ W.Preference i₃ t h e₁ e₂)

/-- An ActionFrame majority preference over ends coincides with the majority preference
    over the induced individual strict posets. -/
theorem action_frame_majority_pref_of_strict_posets
    [W : ActionFrame] (t : W.Moment) (h : W.History)
    (i₁ i₂ i₃ : W.Agent)
    (h_trans₁ : ∀ e₁ e₂ e₃,
      W.Preference i₁ t h e₁ e₂ → W.Preference i₁ t h e₂ e₃ → W.Preference i₁ t h e₁ e₃)
    (h_trans₂ : ∀ e₁ e₂ e₃,
      W.Preference i₂ t h e₁ e₂ → W.Preference i₂ t h e₂ e₃ → W.Preference i₂ t h e₁ e₃)
    (h_trans₃ : ∀ e₁ e₂ e₃,
      W.Preference i₃ t h e₁ e₂ → W.Preference i₃ t h e₂ e₃ → W.Preference i₃ t h e₁ e₃)
    (e₁ e₂ : W.Ends) :
    ActionFrameMajorityPref (W := W) t h i₁ i₂ i₃ e₁ e₂ ↔
      MajorityPref (action_frame_strict_poset W i₁ t h h_trans₁)
                   (action_frame_strict_poset W i₂ t h h_trans₂)
                   (action_frame_strict_poset W i₃ t h h_trans₃) e₁ e₂ := by
  rfl

/-- Autonomous precommitment vs external menu stripping:
an agent's own prior precommitment prunes temptation from their own menu,
whereas external invasion by another agent contracts clean-title stocks
and strips previously feasible actions from the victim's choice menu. -/
theorem self_precommitment_vs_external_menu_stripping
    [W : ActionFrame] {i j : W.Agent} {t t' : W.Moment} {h : W.History}
    (α_tax : W.Action)
    (h_invasive : EndogenouslyInvasiveJ i j t t' h α_tax) :
    (∃ m : W.Means, W.omega i t' (jointBranch i j t h W.alpha_zero α_tax) m <
      W.omega i t h m) := by
  exact h_invasive

end Praxeology
