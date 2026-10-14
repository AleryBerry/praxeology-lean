module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.deprecated false

/-!
# Praxeology.StrictAction

Formulation of Praxeology via Strict Action Axiom & Doxastic Horizon
(Zero Neoclassical Assumptions).

This module contains ZERO `axiom` declarations.

## Scientific Objective & Architectural Innovations
Previous formalizations relied on neoclassical convenience assumptions:
1. `end_of_injective`: Assumed distinct actions cannot share the same best end.
   This was an artificial patch to avoid inconsistency in strict demonstrated preference
   under Buridan's Ass ties.
2. Global `pref_trans` and `pref_connected`: Imposed universal comparability/completeness
   over all unchosen counterfactual options, importing cardinal-like linear orderings.
3. Global `positive_time_preference` axiom: Imposed an ungrounded postulate rather than
   grounding time preference praxeologically in bounded mortal agency.

`StrictAction.lean` reconstructs Praxeology strictly from Purposeful Action and Bounded Mortality:
1. **Section 1: Minimalist Demonstrated Preference (Undominated Choice & Distinct-End Dominance):**
   - Replaces the biconditional `demonstrated_preference` with `UndominatedAct`.
   - Proves full consistency with Buridan ties and incomparable foregone alternatives.
2. **Section 2: Minimalist Set-Valued Opportunity Cost (`OCSet`):**
   - Defines `OCSet` as the undominated subset of `ForegoneEnds`.
   - Proves non-emptiness for pure revealed star-orders and for any finite strict partial order
     without requiring `pref_connected`.
   - Proves classical uniqueness (`OCSet.card = 1`) as a special case when connectedness holds.
3. **Section 3: Time Preference via Avenue B (Doxastic Open Horizon & Demonstrated Time Preference):**
   - Impossibility of immediate consumption under universal negative time preference (Theorem B.1).
   - Demonstrated non-negative time preference from enacted consumption (Theorem B.2).
   - Demonstrated positive time preference from distinct-end dominant consumption (Theorem B.3).
4. **Section 4: Mengerian Marginal Economizing Without Neoclassical Utility:**
   - Proves the existence of an undominated least-urgent end on any finite non-empty set of
     fulfilled independent ends without requiring preference completeness or utility functions.
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- Poset Induction Lemmas for Finite Sets (Zero Global Axioms)
-- =========================================================================

/-- Strong induction auxiliary: on any finite non-empty set S with an irreflexive,
    transitive relation R, there exists an undominated (maximal) element m ∈ S. -/
theorem exists_undominated_aux {α : Type} [DecidableEq α] (n : ℕ) :
    ∀ (S : Finset α), S.card = n → S.Nonempty →
      ∀ (R : α → α → Prop) [∀ a b, Decidable (R a b)],
        (∀ x ∈ S, ¬ R x x) →
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) →
        ∃ m ∈ S, ∀ x ∈ S, ¬ R x m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S h_card h_ne R _ h_irrefl h_trans
    obtain ⟨a, ha⟩ := h_ne
    by_cases h_all : ∀ x ∈ S, ¬ R x a
    · exact ⟨a, ha, h_all⟩
    · push Not at h_all
      obtain ⟨b, hb_in, hba⟩ := h_all
      let S' := S.filter (fun x => R x a)
      have hb_in_S' : b ∈ S' := Finset.mem_filter.mpr ⟨hb_in, hba⟩
      have hS'_ne : S'.Nonempty := ⟨b, hb_in_S'⟩
      have h_sub : S' ⊆ S := Finset.filter_subset _ _
      have ha_notin : a ∉ S' := by
        intro ha_in
        have hra : R a a := (Finset.mem_filter.mp ha_in).2
        exact h_irrefl a ha hra
      have h_card_lt : S'.card < n := by
        have h_sub_erase : S' ⊆ S.erase a := by
          intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun h_eq => ha_notin (h_eq ▸ hx), h_sub hx⟩
        have h1 : S'.card ≤ (S.erase a).card := Finset.card_le_card h_sub_erase
        have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
        rw [h_card] at h2
        have h_pos : 0 < n := by
          rw [← h_card]
          exact Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have h_irrefl' : ∀ x ∈ S', ¬ R x x := fun x hx => h_irrefl x (h_sub hx)
      have h_trans' : ∀ x ∈ S', ∀ y ∈ S', ∀ z ∈ S', R x y → R y z → R x z :=
        fun x hx y hy z hz => h_trans x (h_sub hx) y (h_sub hy) z (h_sub hz)
      obtain ⟨m, hm_in_S', hm_undom⟩ :=
        ih S'.card h_card_lt S' rfl hS'_ne R h_irrefl' h_trans'
      have hm_in_S : m ∈ S := h_sub hm_in_S'
      have hm_ra : R m a := (Finset.mem_filter.mp hm_in_S').2
      refine ⟨m, hm_in_S, ?_⟩
      intro y hy hym
      have hya : R y a := h_trans y hy m hm_in_S a ha hym hm_ra
      have hy_in_S' : y ∈ S' := Finset.mem_filter.mpr ⟨hy, hya⟩
      exact hm_undom y hy_in_S' hym

/-- Poset Maximality Theorem:
    Any non-empty finite set S equipped with an irreflexive, transitive relation R
    has at least one undominated element m ∈ S. Does NOT require connectedness/completeness. -/
theorem exists_undominated_of_finite_poset {α : Type} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    (R : α → α → Prop) [∀ a b, Decidable (R a b)]
    (h_irrefl : ∀ x ∈ S, ¬ R x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) :
    ∃ m ∈ S, ∀ x ∈ S, ¬ R x m :=
  exists_undominated_aux S.card S rfl hS R h_irrefl h_trans

/-- Strong induction auxiliary: on any finite non-empty set S with an irreflexive,
    transitive relation R, there exists a minimal (least-urgent) element m ∈ S. -/
theorem exists_least_urgent_aux {α : Type} [DecidableEq α] (n : ℕ) :
    ∀ (S : Finset α), S.card = n → S.Nonempty →
      ∀ (R : α → α → Prop) [∀ a b, Decidable (R a b)],
        (∀ x ∈ S, ¬ R x x) →
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) →
        ∃ m ∈ S, ∀ x ∈ S, ¬ R m x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S h_card h_ne R _ h_irrefl h_trans
    obtain ⟨a, ha⟩ := h_ne
    by_cases h_all : ∀ x ∈ S, ¬ R a x
    · exact ⟨a, ha, h_all⟩
    · push Not at h_all
      obtain ⟨b, hb_in, hab⟩ := h_all
      let S' := S.filter (fun x => R a x)
      have hb_in_S' : b ∈ S' := Finset.mem_filter.mpr ⟨hb_in, hab⟩
      have hS'_ne : S'.Nonempty := ⟨b, hb_in_S'⟩
      have h_sub : S' ⊆ S := Finset.filter_subset _ _
      have ha_notin : a ∉ S' := by
        intro ha_in
        have hra : R a a := (Finset.mem_filter.mp ha_in).2
        exact h_irrefl a ha hra
      have h_card_lt : S'.card < n := by
        have h_sub_erase : S' ⊆ S.erase a := by
          intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun h_eq => ha_notin (h_eq ▸ hx), h_sub hx⟩
        have h1 : S'.card ≤ (S.erase a).card := Finset.card_le_card h_sub_erase
        have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
        rw [h_card] at h2
        have h_pos : 0 < n := by
          rw [← h_card]
          exact Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have h_irrefl' : ∀ x ∈ S', ¬ R x x := fun x hx => h_irrefl x (h_sub hx)
      have h_trans' : ∀ x ∈ S', ∀ y ∈ S', ∀ z ∈ S', R x y → R y z → R x z :=
        fun x hx y hy z hz => h_trans x (h_sub hx) y (h_sub hy) z (h_sub hz)
      obtain ⟨m, hm_in_S', hm_undom⟩ :=
        ih S'.card h_card_lt S' rfl hS'_ne R h_irrefl' h_trans'
      have hm_in_S : m ∈ S := h_sub hm_in_S'
      have ham : R a m := (Finset.mem_filter.mp hm_in_S').2
      refine ⟨m, hm_in_S, ?_⟩
      intro y hy hmy
      have hay : R a y := h_trans a ha m hm_in_S y hy ham hmy
      have hy_in_S' : y ∈ S' := Finset.mem_filter.mpr ⟨hy, hay⟩
      exact hm_undom y hy_in_S' hmy

/-- Poset Minimality Theorem:
    Any non-empty finite set S equipped with an irreflexive, transitive relation R
    has at least one minimal (least-urgent) element m ∈ S. Does NOT require connectedness. -/
theorem exists_least_urgent_of_finite_poset {α : Type} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    (R : α → α → Prop) [∀ a b, Decidable (R a b)]
    (h_irrefl : ∀ x ∈ S, ¬ R x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) :
    ∃ m ∈ S, ∀ x ∈ S, ¬ R m x :=
  exists_least_urgent_aux S.card S rfl hS R h_irrefl h_trans

-- =========================================================================
-- Section 1: Minimalist Demonstrated Preference & Strict Action
-- =========================================================================

/-- StrictActionModel:
    Core mathematical structure representing purposeful human action without
    neoclassical completeness, global transitivity, or teleological injectivity. -/
structure StrictActionModel (Agent Moment History Action Means Ends : Type) where
  α₀ : Action
  A_feas : Agent → Moment → History → Finset Action
  alpha_zero_mem : ∀ i t h, α₀ ∈ A_feas i t h
  End_of : Agent → Action → Moment → History → Ends
  Pref : Agent → Moment → History → Ends → Ends → Prop
  pref_irrefl_zero : ∀ i t h, ¬ Pref i t h (End_of i α₀ t h) (End_of i α₀ t h)
  Exec : Agent → Moment → Action → History → Prop
  exec_disjoint : ∀ i t h α β, α ≠ β → ¬ (Exec i t α h ∧ Exec i t β h)

/-- UndominatedAct:
    Minimalist purposeful action predicate:
    (a) Feasibility: α* is in the feasible action menu.
    (b) Execution: α* is actually enacted at ⟨t, h⟩.
    (c) Felt Unease: α* strictly improves upon the passive status quo baseline α₀.
    (d) Undominated Optimality: no feasible alternative action β is strictly preferred to α*. -/
def UndominatedAct {Agent Moment History Action Means Ends : Type}
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ M.A_feas i t h ∧
  M.Exec i t α_star h ∧
  M.Pref i t h (M.End_of i α_star t h) (M.End_of i M.α₀ t h) ∧
  ∀ β ∈ M.A_feas i t h, ¬ M.Pref i t h (M.End_of i β t h) (M.End_of i α_star t h)

/-- DistinctEndDominantAct:
    Strengthened purposeful action predicate where the chosen action α* strictly
    dominates all alternatives that achieve a distinct end.
    Allows Buridan ties (actions achieving the same end need not dominate each other). -/
def DistinctEndDominantAct {Agent Moment History Action Means Ends : Type}
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ M.A_feas i t h ∧
  M.Exec i t α_star h ∧
  M.Pref i t h (M.End_of i α_star t h) (M.End_of i M.α₀ t h) ∧
  ∀ β ∈ M.A_feas i t h, M.End_of i β t h ≠ M.End_of i α_star t h →
    M.Pref i t h (M.End_of i α_star t h) (M.End_of i β t h)

/-- Theorem 1.1 (Undominated Action is Non-Passive):
    Any purposeful action α* is distinct from the passive baseline α₀,
    and achieves an end distinct from the status quo end. -/
theorem undominated_act_non_passive {Agent Moment History Action Means Ends : Type}
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : UndominatedAct M i t h α_star) :
    α_star ≠ M.α₀ ∧ M.End_of i α_star t h ≠ M.End_of i M.α₀ t h := by
  have h_pref := h_act.2.2.1
  have h_not_end : M.End_of i α_star t h ≠ M.End_of i M.α₀ t h := by
    intro h_eq
    rw [h_eq] at h_pref
    exact M.pref_irrefl_zero i t h h_pref
  have h_not_act : α_star ≠ M.α₀ := by
    intro h_eq
    subst h_eq
    exact h_not_end rfl
  exact ⟨h_not_act, h_not_end⟩

/-- Theorem 1.2 (Unique Execution of Purposeful Action):
    Execution cell disjointness uniquely determines the enacted action without
    requiring teleological injectivity (end_of_injective). -/
theorem undominated_act_unique_execution {Agent Moment History Action Means Ends : Type}
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α₁ α₂ : Action)
    (h1 : UndominatedAct M i t h α₁)
    (h2 : UndominatedAct M i t h α₂) :
    α₁ = α₂ := by
  by_contra hne
  have h_disj := M.exec_disjoint i t h α₁ α₂ hne
  exact h_disj ⟨h1.2.1, h2.2.1⟩

-- =========================================================================
-- Buridan Tie Consistency & Incomparable Options Consistency Witnesses
-- =========================================================================

def BuridanStrictMenu : Finset (Fin 3) := {0, 1, 2}

/-- Concrete Buridan's Ass Model:
    Two distinct non-inertial actions (1 and 2) achieve the same optimal end e = 1.
    Action 1 is chosen and enacted. -/
def BuridanStrictModel : StrictActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1) (Fin 2) where
  α₀ := 0
  A_feas _ _ _ := BuridanStrictMenu
  alpha_zero_mem _ _ _ := by decide
  End_of _ α _ _ := if α = 0 then 0 else 1
  Pref _ _ _ a b := a = 1 ∧ b = 0
  pref_irrefl_zero _ _ _ := by
    intro ⟨h1, _⟩
    exact absurd h1 (by decide)
  Exec _ _ α _ := α = 1
  exec_disjoint _ _ _ α β hne := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl

/-- Theorem 1.3 (Buridan Tie Consistency):
    UndominatedAct is completely consistent with Buridan ties:
    two distinct actions α₁ ≠ α₂ achieve the exact same end (End_of α₁ = End_of α₂),
    yet α₁ is purposefully executed under UndominatedAct.
    Demonstrates that end_of_injective was an artificial patch required only by
    the flawed biconditional strict demonstrated preference. -/
theorem undominated_act_buridan_tie_consistent :
    ∃ (M : StrictActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1) (Fin 2)) (α₁ α₂ : Fin 3),
      α₁ ≠ α₂ ∧
      M.End_of 0 α₁ 0 0 = M.End_of 0 α₂ 0 0 ∧
      UndominatedAct M 0 0 0 α₁ := by
  use BuridanStrictModel, 1, 2
  refine ⟨by decide, rfl, ?_⟩
  dsimp [UndominatedAct]
  refine ⟨by decide, rfl, ⟨rfl, rfl⟩, ?_⟩
  intro β _ h_pref
  fin_cases β
  · exact absurd h_pref.1 (by decide)
  · exact absurd h_pref.2 (by decide)
  · exact absurd h_pref.2 (by decide)

def IncompStrictMenu : Finset (Fin 4) := {0, 1, 2, 3}

/-- Concrete Model with Incomparable Foregone Alternatives:
    Action 1 is chosen over baseline 0 and alternatives 2 and 3.
    Alternatives 2 and 3 are mutually incomparable. -/
def IncompStrictModel : StrictActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 4) (Fin 1) (Fin 4) where
  α₀ := 0
  A_feas _ _ _ := IncompStrictMenu
  alpha_zero_mem _ _ _ := by decide
  End_of _ α _ _ := α
  Pref _ _ _ a b := (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3)
  pref_irrefl_zero _ _ _ := by
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
  Exec _ _ α _ := α = 1
  exec_disjoint _ _ _ α β hne := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl

/-- Theorem 1.4 (Incomparable Alternatives Consistency):
    UndominatedAct holds even when unchosen foregone alternatives are mutually incomparable,
    proving that human action does not require neoclassical preference completeness (pref_connected). -/
theorem undominated_act_incomparable_consistent :
    ∃ (M : StrictActionModel (Fin 1) (Fin 1) (Fin 1) (Fin 4) (Fin 1) (Fin 4)) (α_star : Fin 4) (e₂ e₃ : Fin 4),
      UndominatedAct M 0 0 0 α_star ∧
      e₂ ∈ (IncompStrictMenu.erase α_star).image (M.End_of 0 · 0 0) ∧
      e₃ ∈ (IncompStrictMenu.erase α_star).image (M.End_of 0 · 0 0) ∧
      ¬ M.Pref 0 0 0 e₂ e₃ ∧
      ¬ M.Pref 0 0 0 e₃ e₂ := by
  use IncompStrictModel, 1, 2, 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [UndominatedAct]
    refine ⟨by decide, rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro β _ h_pref
    dsimp [IncompStrictModel] at h_pref
    fin_cases β
    · rcases h_pref with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · rcases h_pref with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
    · rcases h_pref with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · rcases h_pref with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · dsimp [IncompStrictModel, IncompStrictMenu]
    decide
  · dsimp [IncompStrictModel, IncompStrictMenu]
    decide
  · intro h
    dsimp [IncompStrictModel] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · intro h
    dsimp [IncompStrictModel] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

-- =========================================================================
-- Section 2: Minimalist Set-Valued Opportunity Cost (OCSet)
-- =========================================================================

/-- Foregone alternative actions when choosing α_star. -/
def ForegoneActions {Agent Moment History Action Means Ends : Type} [DecidableEq Action]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Action :=
  (M.A_feas i t h).erase α_star

/-- Foregone ends corresponding to the foregone alternative actions.
    Deduplicated via Finset.image; does NOT require teleological injectivity. -/
def ForegoneEnds {Agent Moment History Action Means Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Ends :=
  (ForegoneActions M i t h α_star).image (M.End_of i · t h)

/-- Minimalist Opportunity Cost Set (OCSet):
    The set of all undominated foregone ends (ends in ForegoneEnds that are not
    strictly dominated by any other foregone end). -/
def OCSet {Agent Moment History Action Means Ends : Type} [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (α_star : Action) : Finset Ends :=
  (ForegoneEnds M i t h α_star).filter (fun e =>
    ∀ e' ∈ ForegoneEnds M i t h α_star, ¬ M.Pref i t h e' e)

/-- Theorem 2.1 (Star-Order Non-Emptiness):
    In a pure revealed star-order (where purposeful action reveals preferences involving
    the chosen end, but reveals no strict preferences among unchosen foregone ends),
    OCSet is identical to ForegoneEnds, and is strictly non-empty whenever ForegoneEnds is non-empty. -/
theorem ocset_nonempty_of_star_order {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (α_star : Action)
    (h_star : ∀ e ∈ ForegoneEnds M i t h α_star, ∀ e' ∈ ForegoneEnds M i t h α_star, ¬ M.Pref i t h e' e)
    (h_ne : (ForegoneEnds M i t h α_star).Nonempty) :
    OCSet M i t h α_star = ForegoneEnds M i t h α_star ∧
    (OCSet M i t h α_star).Nonempty := by
  have h_eq : OCSet M i t h α_star = ForegoneEnds M i t h α_star := by
    ext e
    dsimp [OCSet]
    rw [Finset.mem_filter]
    constructor
    · intro h_in; exact h_in.1
    · intro he_in
      refine ⟨he_in, fun e' he'_in => h_star e he_in e' he'_in⟩
  exact ⟨h_eq, h_eq.symm ▸ h_ne⟩

/-- Theorem 2.2 (Strict Partial Order Non-Emptiness):
    For ANY finite non-empty set of foregone ends equipped with an irreflexive,
    transitive preference relation, OCSet is guaranteed to be non-empty (OCSet.Nonempty).
    Proves that Opportunity Cost exists without requiring preference connectedness (pref_connected)
    or teleological injectivity (end_of_injective). -/
theorem ocset_nonempty_of_irrefl_trans {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (α_star : Action)
    (h_ne : (ForegoneEnds M i t h α_star).Nonempty)
    (h_irrefl : ∀ e ∈ ForegoneEnds M i t h α_star, ¬ M.Pref i t h e e)
    (h_trans : ∀ e1 ∈ ForegoneEnds M i t h α_star, ∀ e2 ∈ ForegoneEnds M i t h α_star, ∀ e3 ∈ ForegoneEnds M i t h α_star,
      M.Pref i t h e1 e2 → M.Pref i t h e2 e3 → M.Pref i t h e1 e3) :
    (OCSet M i t h α_star).Nonempty := by
  obtain ⟨m, hm_in, hm_undom⟩ := exists_undominated_of_finite_poset
    (ForegoneEnds M i t h α_star) h_ne (M.Pref i t h) h_irrefl h_trans
  use m
  dsimp [OCSet]
  rw [Finset.mem_filter]
  exact ⟨hm_in, hm_undom⟩

/-- Theorem 2.3a (Card Le One Under Connectedness):
    When preference is connected over distinct foregone ends, OCSet contains at most 1 element. -/
theorem ocset_card_le_one_of_connected {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (α_star : Action)
    (h_conn : ∀ e1 ∈ ForegoneEnds M i t h α_star, ∀ e2 ∈ ForegoneEnds M i t h α_star, e1 ≠ e2 →
      M.Pref i t h e1 e2 ∨ M.Pref i t h e2 e1) :
    (OCSet M i t h α_star).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  dsimp [OCSet] at ha hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  rcases h_conn a ha.1 b hb.1 hne with hab | hba
  · exact hb.2 a ha.1 hab
  · exact ha.2 b hb.1 hba

/-- Theorem 2.3b (Classical Subsumption: Unique Singleton Opportunity Cost):
    When preference is connected, irreflexive, and transitive over a non-empty set of foregone ends,
    OCSet has cardinality exactly 1 (recovering unique classical Opportunity Cost as a special case). -/
theorem ocset_singleton_of_connected {Agent Moment History Action Means Ends : Type}
    [DecidableEq Action] [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (α_star : Action)
    (h_ne : (ForegoneEnds M i t h α_star).Nonempty)
    (h_irrefl : ∀ e ∈ ForegoneEnds M i t h α_star, ¬ M.Pref i t h e e)
    (h_trans : ∀ e1 ∈ ForegoneEnds M i t h α_star, ∀ e2 ∈ ForegoneEnds M i t h α_star, ∀ e3 ∈ ForegoneEnds M i t h α_star,
      M.Pref i t h e1 e2 → M.Pref i t h e2 e3 → M.Pref i t h e1 e3)
    (h_conn : ∀ e1 ∈ ForegoneEnds M i t h α_star, ∀ e2 ∈ ForegoneEnds M i t h α_star, e1 ≠ e2 →
      M.Pref i t h e1 e2 ∨ M.Pref i t h e2 e1) :
    (OCSet M i t h α_star).card = 1 := by
  have h_nonempty := ocset_nonempty_of_irrefl_trans M i t h α_star h_ne h_irrefl h_trans
  have h_le := ocset_card_le_one_of_connected M i t h α_star h_conn
  have h_pos : 0 < (OCSet M i t h α_star).card := Finset.card_pos.mpr h_nonempty
  omega

-- =========================================================================
-- Section 3: Time Preference via Avenue B (Doxastic Open Horizon)
-- =========================================================================

/-- StrictTemporalModel:
    Extends StrictActionModel with discrete temporal order (<), bounded mortal lifespan (T_max),
    post-horizon singleton menu, subjective plausibility set (Plausible), and timed end evaluation. -/
structure StrictTemporalModel (Agent Moment History Action Means Ends : Type) [Preorder Moment]
    extends StrictActionModel Agent Moment History Action Means Ends where
  T_max : Agent → History → Moment
  post_horizon_singleton : ∀ i t h, T_max i h < t → A_feas i t h = {α₀}
  Plausible : Agent → Moment → History → Finset History
  plausible_nonempty : ∀ i t h, (Plausible i t h).Nonempty
  TimedEnd : Ends → Moment → Ends

/-- Strict Universal Negative Time Preference:
    Agent systematically prefers future satisfaction to earlier satisfaction. -/
def StrictUniversalNegativeTimePreference {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (h : History) (e : Ends) : Prop :=
  ∀ τ1 τ2 : Moment, τ1 < τ2 → M.Pref i τ1 h (M.TimedEnd e τ2) (M.TimedEnd e τ1)

namespace StrictAction
abbrev UniversalNegativeTimePreference := @StrictUniversalNegativeTimePreference
end StrictAction

/-- Doxastic Open Epistemic Horizon:
    At active moment τ, across plausible histories, the agent believes τ is strictly before mortality T_max,
    and whenever immediate consumption α_e is feasible, there exists a feasible deferral action α_defer
    aiming at realization at some strictly later moment τ' > τ. -/
def DoxasticOpenHorizon {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action) : Prop :=
  α_e ∈ M.A_feas i τ h →
  M.End_of i α_e τ h = M.TimedEnd e τ →
  (∀ h' ∈ M.Plausible i τ h, τ < M.T_max i h') ∧
  ∃ (α_defer : Action) (τ' : Moment),
    α_defer ∈ M.A_feas i τ h ∧
    τ < τ' ∧
    M.End_of i α_defer τ h = M.TimedEnd e τ'

/-- Theorem B.1 (Avenue B: Impossibility of Action Under Universal Negative Time Preference):
    Under UndominatedAct and DoxasticOpenHorizon, an agent holding UniversalNegativeTimePreference
    can NEVER purposefully execute immediate consumption α_e at any active moment.
    Notice: Requires ZERO transitivity, ZERO completeness, and ZERO teleological injectivity! -/
theorem avenue_b_impossibility_of_negative_time_pref
    {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : M.End_of i α_e τ h = M.TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon M i τ h e α_e)
    (h_neg : StrictUniversalNegativeTimePreference M i h e) :
    ¬ UndominatedAct M.toStrictActionModel i τ h α_e := by
  intro h_act
  have h_feas := h_act.1
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_feas h_end
  have h_pref_defer := h_neg τ τ' h_lt
  rw [← h_end_defer, ← h_end] at h_pref_defer
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  exact h_undom h_pref_defer

/-- Post-Horizon Inactivity:
    Beyond mortal lifespan T_max, no purposeful action can ever be executed,
    because the feasible action menu collapses to the singleton passive baseline {α₀}. -/
theorem post_horizon_no_action
    {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History) (α : Action)
    (h_past : M.T_max i h < t) :
    ¬ UndominatedAct M.toStrictActionModel i t h α := by
  intro h_act
  have h_feas := h_act.1
  rw [M.post_horizon_singleton i t h h_past] at h_feas
  have h_eq : α = M.α₀ := Finset.mem_singleton.mp h_feas
  have h_np := undominated_act_non_passive M.toStrictActionModel i t h α h_act
  exact h_np.1 h_eq

/-- Theorem B.2 (Constructive Converse: Enacted Consumption Demonstrates Non-Negative Time Preference):
    If an agent DOES purposefully execute immediate consumption α_e at moment τ under DoxasticOpenHorizon,
    then there exists a future moment τ' > τ such that the agent demonstrates Non-Negative Time Preference:
    deferral is NOT strictly preferred to immediate consumption. -/
theorem enacted_consumption_demonstrates_nonneg_time_pref
    {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : M.End_of i α_e τ h = M.TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon M i τ h e α_e)
    (h_act : UndominatedAct M.toStrictActionModel i τ h α_e) :
    ∃ τ' : Moment, τ < τ' ∧ ¬ M.Pref i τ h (M.TimedEnd e τ') (M.TimedEnd e τ) := by
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_undom := h_act.2.2.2 α_defer h_defer_feas
  rw [h_end_defer, h_end] at h_undom
  exact ⟨τ', h_lt, h_undom⟩

/-- Theorem B.3 (Enacted Consumption Demonstrates Positive Time Preference):
    If an agent executes a Distinct-End Dominant Act to consume α_e at τ under DoxasticOpenHorizon,
    with injective time indexing (τ ≠ τ' → TimedEnd e τ ≠ TimedEnd e τ'),
    then the agent strictly demonstrates Positive Time Preference:
    earlier consumption is strictly preferred to later consumption! -/
theorem enacted_consumption_demonstrates_strict_time_pref
    {Agent Moment History Action Means Ends : Type} [Preorder Moment]
    (M : StrictTemporalModel Agent Moment History Action Means Ends)
    (i : Agent) (τ : Moment) (h : History) (e : Ends) (α_e : Action)
    (h_end : M.End_of i α_e τ h = M.TimedEnd e τ)
    (h_oeh : DoxasticOpenHorizon M i τ h e α_e)
    (h_act : DistinctEndDominantAct M.toStrictActionModel i τ h α_e)
    (h_timed_inj : ∀ τ1 τ2 : Moment, τ1 ≠ τ2 → M.TimedEnd e τ1 ≠ M.TimedEnd e τ2) :
    ∃ τ' : Moment, τ < τ' ∧ M.Pref i τ h (M.TimedEnd e τ) (M.TimedEnd e τ') := by
  obtain ⟨_, α_defer, τ', h_defer_feas, h_lt, h_end_defer⟩ := h_oeh h_act.1 h_end
  have h_ne_mom : τ ≠ τ' := ne_of_lt h_lt
  have h_ne_timed : M.TimedEnd e τ ≠ M.TimedEnd e τ' := h_timed_inj τ τ' h_ne_mom
  have h_ne_ends : M.End_of i α_defer τ h ≠ M.End_of i α_e τ h := by
    rw [h_end_defer, h_end]
    exact h_ne_timed.symm
  have h_dom := h_act.2.2.2 α_defer h_defer_feas h_ne_ends
  rw [h_end, h_end_defer] at h_dom
  exact ⟨τ', h_lt, h_dom⟩

-- =========================================================================
-- Section 4: Mengerian Marginal Economizing Without Neoclassical Utility
-- =========================================================================

/-- Minimal (least-urgent) end in a set of fulfilled ends:
    no other fulfilled end in S is less urgent than e_min. -/
def IsLeastUrgentEnd {Ends : Type} (Pref : Ends → Ends → Prop) (S : Finset Ends) (e_min : Ends) : Prop :=
  e_min ∈ S ∧ ∀ e ∈ S, ¬ Pref e_min e

/-- Theorem 4.1 (Mengerian Marginal Economizing Without Utility):
    On any finite non-empty set of fulfilled independent ends S, equipped with an irreflexive
    and transitive preference relation, there exists a least-urgent end e_min ∈ S.
    When a unit of scarce means is lost, purposeful economizing sacrifices this least-urgent end,
    without requiring preference completeness/connectedness (pref_connected) or cardinal utility. -/
theorem mengerian_least_urgent_end_exists {Ends : Type} [DecidableEq Ends]
    (S : Finset Ends) (hS : S.Nonempty)
    (Pref : Ends → Ends → Prop) [∀ a b, Decidable (Pref a b)]
    (h_irrefl : ∀ x ∈ S, ¬ Pref x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Pref x y → Pref y z → Pref x z) :
    ∃ e_min ∈ S, IsLeastUrgentEnd Pref S e_min := by
  obtain ⟨e_min, hm_in, hm_min⟩ := exists_least_urgent_of_finite_poset S hS Pref h_irrefl h_trans
  exact ⟨e_min, hm_in, ⟨hm_in, hm_min⟩⟩

/-- Theorem 4.2 (Mengerian Marginal Sacrifice in StrictActionModel):
    Within any StrictActionModel, given any finite non-empty set of fulfilled ends S,
    an undominated least-urgent end exists whenever preference is irreflexive and transitive on S. -/
theorem mengerian_marginal_sacrifice_exists {Agent Moment History Action Means Ends : Type}
    [DecidableEq Ends]
    (M : StrictActionModel Agent Moment History Action Means Ends)
    (i : Agent) (t : Moment) (h : History)
    (S : Finset Ends) (hS : S.Nonempty)
    [∀ a b, Decidable (M.Pref i t h a b)]
    (h_irrefl : ∀ x ∈ S, ¬ M.Pref i t h x x)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, M.Pref i t h x y → M.Pref i t h y z → M.Pref i t h x z) :
    ∃ e_min ∈ S, ∀ e ∈ S, ¬ M.Pref i t h e_min e := by
  obtain ⟨e_min, hm_in, hm_least⟩ := mengerian_least_urgent_end_exists S hS (M.Pref i t h) h_irrefl h_trans
  exact ⟨e_min, hm_in, hm_least.2⟩

end Praxeology

end
