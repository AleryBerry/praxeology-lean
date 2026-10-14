module

public import Praxeology.Frame
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Praxeology.Action

Formalization of the core action theory of praxeology, following `spec/02_action_and_preference.md`.

## Contents
1. Physical Endowment, Production Requirements, and Resource Scarcity.
2. Ends of Actions and Ordinal Preference (Strict Partial Order, Connected over Feasible Ends).
3. Causal Temporal Realization Modality.
4. Axiom 1' (Purposeful Human Action): Choice Nodes, Felt Unease, Causal Belief, and Deliberative STIT Execution.
5. Axiom 2(3)' (Demonstrated Preference): Repaired internal quantifier scope.
6. Theorem 1.1' (Dialectical Undeniability / Performative Consistency): Distinguishing Utter from Assert.
7. Theorem 1.2 (Existence and Uniqueness of Opportunity Cost): Finite strict linear maximum and counterfactual exclusivity.
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- 1. Physical Endowment, Requirements, and Scarcity
-- =========================================================================

/-- Physical endowment function ω : Agent → Moment → History → Means → ℕ₀. -/
axiom endowment : Agent → Moment → History → Means → ℕ

/-- Production requirement function ρ : Ends → Means → ℕ₀.
    Specifies minimum discrete units of means required to instantiate an end. -/
axiom requirement : Ends → Means → ℕ

/-- Scarcity predicate:
    Means m is scarce for agent i at ⟨t, h⟩ if the available endowment is insufficient
    to satisfy the requirements of some contemplated end. -/
def Scarce (i : Agent) (t : Moment) (h : History) (m : Means) : Prop :=
  ∃ e : Ends, endowment i t h m < requirement e m

-- =========================================================================
-- 2. Ends of Actions and Ordinal Preference
-- =========================================================================

/-- Teleological mapping associating each action with its intended end. -/
axiom End_of : Agent → Action → Moment → History → Ends

/-- Distinct feasible actions in a choice situation aim at distinct ends. -/
axiom end_of_injective (i : Agent) (t : Moment) (h : History)
    {α β : Action} (hα : α ∈ A_feas i t h) (hβ : β ∈ A_feas i t h) :
    α ≠ β → End_of i α t h ≠ End_of i β t h

/-- Strict ordinal preference relation ≻_{i,t,h} over ends.
    No cardinal utility is assumed; evaluation is purely ordinal and subjective. -/
axiom Preference (i : Agent) (t : Moment) (h : History) : Ends → Ends → Prop

/-- Preference is strictly irreflexive: no end is strictly preferred to itself. -/
axiom pref_irrefl (i : Agent) (t : Moment) (h : History) (e : Ends) :
  ¬(Preference i t h e e)

/-- Preference is transitive. -/
axiom pref_trans (i : Agent) (t : Moment) (h : History) {e1 e2 e3 : Ends} :
  Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3

/-- Preference is asymmetric (derived from irreflexivity and transitivity). -/
theorem pref_asymm (i : Agent) (t : Moment) (h : History) {e1 e2 : Ends}
    (h1 : Preference i t h e1 e2) (h2 : Preference i t h e2 e1) : False :=
  pref_irrefl i t h e1 (pref_trans i t h h1 h2)

/-- Strict linearity / connectedness over feasible ends:
    Any two distinct feasible ends are strictly ranked. -/
axiom pref_connected (i : Agent) (t : Moment) (h : History) {e1 e2 : Ends}
    (h1 : e1 ∈ (A_feas i t h).image (End_of i · t h))
    (h2 : e2 ∈ (A_feas i t h).image (End_of i · t h))
    (hne : e1 ≠ e2) :
    Preference i t h e1 e2 ∨ Preference i t h e2 e1

-- =========================================================================
-- 3. Temporal Realization Predicate
-- =========================================================================

/-- Temporal event predicate: end e is eventually realized on history h. -/
axiom FutureRealizes (e : Ends) : History → Prop

-- =========================================================================
-- 4. Axiom 1' (Axiom of Purposeful Human Action)
-- =========================================================================

/-- ChoiceNode(i, t, h):
    1. Feasible action menu contains at least two distinct alternatives (|A_feas| ≥ 2).
    2. Agent believes that some non-inertial action α improves upon the passive baseline α₀. -/
def ChoiceNode (i : Agent) (t : Moment) (h : History) : Prop :=
  (A_feas i t h).card ≥ 2 ∧
  ∃ α ∈ (A_feas i t h).erase α₀,
    Belief i t (fun _ =>
      DynamicBox i t α₀ (FutureRealizes (End_of i α₀ t h)) ∧
      DynamicBox i t α (FutureRealizes (End_of i α t h)) ∧
      Preference i t h (End_of i α t h) (End_of i α₀ t h))

/-- Act_i(t, h, α*): Purposeful action predicate containing:
    1. Felt unease & causal belief: agent expects α* to yield an improvement over passive state α₀.
    2. Deliberative STIT execution: agent deliberatively brings about α*.
    3. Comparative superiority: agent expects α* to be strictly preferred to all alternatives. -/
def Act (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  Belief i t (fun _ =>
    DynamicBox i t α₀ (FutureRealizes (End_of i α₀ t h)) ∧
    DynamicBox i t α_star (FutureRealizes (End_of i α_star t h)) ∧
    Preference i t h (End_of i α_star t h) (End_of i α₀ t h)) ∧
  dstit i t (Exec i t α_star) h ∧
  Belief i t (fun _ =>
    ∀ β ∈ (A_feas i t h).erase α_star,
      DynamicBox i t β (FutureRealizes (End_of i β t h)) →
      Preference i t h (End_of i α_star t h) (End_of i β t h))

/-- PA_i(t, h): Purposeful Action principle.
    At every choice node, there exists a unique action α* that is purposefully enacted. -/
def PA (i : Agent) (t : Moment) (h : History) : Prop :=
  ChoiceNode i t h → ∃! α_star : Action, α_star ∈ A_feas i t h ∧ Act i t h α_star

/-- Axiom 1' (Axiom of Purposeful Human Action):
    Every agent at every moment and history satisfies the Purposeful Action principle. -/
axiom axiom_1_prime (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) : PA i t h

-- =========================================================================
-- 5. Axiom 2(3)' (Demonstrated Preference - Repaired Prenex Quantifier Scope)
-- =========================================================================

/-- Axiom 2(3)' (Demonstrated Preference):
    Deliberative execution of α* is logically equivalent to α* being strictly preferred
    to every available alternative.
    Guardrail: The universal quantifier over alternative actions β is placed
    INSIDE the right-hand side of the biconditional. -/
axiom demonstrated_preference (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_feas : α_star ∈ A_feas i t h) :
    dstit i t (Exec i t α_star) h ↔
      ∀ β ∈ (A_feas i t h).erase α_star, Preference i t h (End_of i α_star t h) (End_of i β t h)

-- =========================================================================
-- 6. Theorem 1.1' (Dialectical Undeniability / Performative Consistency)
-- =========================================================================

/-- Acoustic utterance: physical sound emission without intentional semantic assertion. -/
axiom Utter (i : Agent) (t : Moment) (h : History) (content : String) : Prop

/-- Intentional assertion: teleological communication of a proposition p. -/
axiom Asserts (i : Agent) (t : Moment) (h : History) (p : Prop) : Prop

/-- Axiom of Assertoric Action:
    Asserting a proposition is an intentional act using scarce communicative means
    to attain a communicative end. Therefore, assertion is purposeful action. -/
axiom assertion_is_action (i : Agent) (t : Moment) (h : History) (p : Prop) :
  Asserts i t h p → ∃ α ∈ A_feas i t h, Act i t h α

/-- The proposition denying the presence of any purposeful action at ⟨t, h⟩. -/
def DenialOfAction (i : Agent) (t : Moment) (h : History) : Prop :=
  ¬ ∃ α ∈ A_feas i t h, Act i t h α

/-- Theorem 1.1' (Dialectical Undeniability / Performative Consistency):
    Asserting the negation of purposeful action at ⟨t, h⟩ while denying local action yields False.
    Any attempt to verbally or dialectically deny purposeful action performatively refutes itself. -/
theorem dialectical_undeniability (i : Agent) (t : Moment) (h : History)
    (h_assert : Asserts i t h (DenialOfAction i t h))
    (h_denial : DenialOfAction i t h) : False := by
  have h_act : ∃ α ∈ A_feas i t h, Act i t h α :=
    assertion_is_action i t h (DenialOfAction i t h) h_assert
  exact h_denial h_act

-- =========================================================================
-- 7. Theorem 1.2 (Existence and Uniqueness of Opportunity Cost)
-- =========================================================================

/-- Foregone alternative actions when choosing α_star. -/
noncomputable def foregone_actions (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Action :=
  (A_feas i t h).erase α_star

/-- Foregone ends corresponding to the foregone alternative actions. -/
noncomputable def foregone_ends (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Ends :=
  (foregone_actions i t h α_star).image (End_of i · t h)

/-- At a choice node, the foregone actions set is non-empty. -/
theorem foregone_actions_nonempty {i : Agent} {t : Moment} {h : History} {α_star : Action}
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) :
    (foregone_actions i t h α_star).Nonempty := by
  dsimp [foregone_actions]
  rw [Finset.nonempty_iff_ne_empty]
  intro h_empty
  have h_card := Finset.card_erase_of_mem h_feas
  have h_zero : ((A_feas i t h).erase α_star).card = 0 := by rw [h_empty, Finset.card_empty]
  have h_node_card := h_node.1
  omega

/-- At a choice node, the foregone ends set is non-empty. -/
theorem foregone_ends_nonempty {i : Agent} {t : Moment} {h : History} {α_star : Action}
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) :
    (foregone_ends i t h α_star).Nonempty := by
  obtain ⟨β, hβ⟩ := foregone_actions_nonempty h_node h_feas
  use End_of i β t h
  exact Finset.mem_image_of_mem (End_of i · t h) hβ

/-- Predicate characterizing the opportunity cost:
    The foregone end that is strictly preferred to every other foregone end. -/
def IsOpportunityCost (i : Agent) (t : Moment) (h : History) (α_star : Action) (e : Ends) : Prop :=
  e ∈ foregone_ends i t h α_star ∧
  ∀ e' ∈ (foregone_ends i t h α_star).erase e, Preference i t h e e'

/-- Uniqueness of the maximum over foregone ends under strict partial order. -/
theorem opportunity_cost_unique (i : Agent) (t : Moment) (h : History) (α_star : Action)
    {e1 e2 : Ends}
    (h1 : IsOpportunityCost i t h α_star e1)
    (h2 : IsOpportunityCost i t h α_star e2) :
    e1 = e2 := by
  by_contra hne
  have he2_in : e2 ∈ (foregone_ends i t h α_star).erase e1 :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, h2.1⟩
  have he1_in : e1 ∈ (foregone_ends i t h α_star).erase e2 :=
    Finset.mem_erase.mpr ⟨hne, h1.1⟩
  have hr12 := h1.2 e2 he2_in
  have hr21 := h2.2 e1 he1_in
  have hr11 := pref_trans i t h hr12 hr21
  exact pref_irrefl i t h e1 hr11

/-- Lemma: All elements of foregone_ends belong to the feasible ends image. -/
theorem foregone_ends_subset_feasible (i : Agent) (t : Moment) (h : History) (α_star : Action) :
    ∀ e ∈ foregone_ends i t h α_star, e ∈ (A_feas i t h).image (End_of i · t h) := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨β, hβ, rfl⟩
  have hβ_feas : β ∈ A_feas i t h := Finset.mem_of_mem_erase hβ
  exact Finset.mem_image_of_mem (End_of i · t h) hβ_feas

/-- Inductive existence of the strict maximum on any non-empty sub-finset of feasible ends. -/
theorem strict_max_foregone_exists (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (s : Finset Ends) (hs_sub : ∀ e ∈ s, e ∈ (A_feas i t h).image (End_of i · t h))
    (hs_ne : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s.erase m, Preference i t h m x := by
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.Nonempty.ne_empty hs_ne rfl)
  | @insert a tail ha ih =>
    by_cases ht : tail.Nonempty
    · have ht_sub : ∀ e ∈ tail, e ∈ (A_feas i t h).image (End_of i · t h) :=
        fun e he => hs_sub e (Finset.mem_insert_of_mem he)
      obtain ⟨m, hm_in, hm_max⟩ := ih ht_sub ht
      have hne : a ≠ m := fun h_eq => ha (h_eq ▸ hm_in)
      have ha_feas : a ∈ (A_feas i t h).image (End_of i · t h) :=
        hs_sub a (Finset.mem_insert_self a tail)
      have hm_feas : m ∈ (A_feas i t h).image (End_of i · t h) :=
        ht_sub m hm_in
      rcases pref_connected i t h ha_feas hm_feas hne with h_am | h_ma
      · -- a strictly preferred to m
        use a
        refine ⟨Finset.mem_insert_self a tail, ?_⟩
        intro x hx
        have hx_tail : x ∈ tail := by
          have hx_in : x ∈ insert a tail := (Finset.mem_erase.mp hx).2
          cases Finset.mem_insert.mp hx_in with
          | inl h_eq => exact False.elim ((Finset.mem_erase.mp hx).1 h_eq)
          | inr h_in => exact h_in
        by_cases hxm : x = m
        · subst hxm; exact h_am
        · have hx_erase : x ∈ tail.erase m := Finset.mem_erase.mpr ⟨hxm, hx_tail⟩
          exact pref_trans i t h h_am (hm_max x hx_erase)
      · -- m strictly preferred to a
        use m
        refine ⟨Finset.mem_insert_of_mem hm_in, ?_⟩
        intro x hx
        have hx_in : x ∈ insert a tail := (Finset.mem_erase.mp hx).2
        cases Finset.mem_insert.mp hx_in with
        | inl hxa =>
          subst hxa; exact h_ma
        | inr hxt =>
          have hxm : x ≠ m := (Finset.mem_erase.mp hx).1
          exact hm_max x (Finset.mem_erase.mpr ⟨hxm, hxt⟩)
    · have ht_empty : tail = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst ht_empty
      use a
      refine ⟨Finset.mem_singleton_self a, ?_⟩
      intro x hx
      simp at hx

/-- Theorem 1.2 (Existence and Uniqueness of Opportunity Cost):
    At any choice node, there exists a unique opportunity cost end. -/
theorem opportunity_cost_exists_unique (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) :
    ∃! e : Ends, IsOpportunityCost i t h α_star e := by
  have hs_ne := foregone_ends_nonempty h_node h_feas
  have hs_sub := foregone_ends_subset_feasible i t h α_star
  obtain ⟨m, hm_in, hm_max⟩ := strict_max_foregone_exists i t h α_star
    (foregone_ends i t h α_star) hs_sub hs_ne
  refine ⟨m, ⟨hm_in, hm_max⟩, ?_⟩
  intro y hy
  exact opportunity_cost_unique i t h α_star hy ⟨hm_in, hm_max⟩

/-- Classical definite description construction of OpportunityCost. -/
noncomputable def OpportunityCost (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) : Ends :=
  Classical.choose (opportunity_cost_exists_unique i t h α_star h_node h_feas).exists

/-- The constructed OpportunityCost satisfies the IsOpportunityCost specification. -/
theorem opportunity_cost_spec (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) :
    IsOpportunityCost i t h α_star (OpportunityCost i t h α_star h_node h_feas) :=
  Classical.choose_spec (opportunity_cost_exists_unique i t h α_star h_node h_feas).exists

/-- Theorem 1.2 (Domination over Opportunity Cost):
    The realized action's end is strictly preferred to the opportunity cost end:
    End(α*) ≻ OpportunityCost(α*). -/
theorem action_dominates_opportunity_cost (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h)
    (h_dstit : dstit i t (Exec i t α_star) h) :
    Preference i t h (End_of i α_star t h) (OpportunityCost i t h α_star h_node h_feas) := by
  have h_pref_all := (demonstrated_preference i t h α_star h_feas).mp h_dstit
  have h_spec := opportunity_cost_spec i t h α_star h_node h_feas
  rcases Finset.mem_image.mp h_spec.1 with ⟨β, hβ, h_beta_end⟩
  rw [← h_beta_end]
  exact h_pref_all β hβ

/-- Theorem 1.2 (Counterfactual Exclusivity Condition):
    Realizing the chosen action α* counterfactually and physically excludes
    the realization of the foregone action yielding the opportunity cost. -/
theorem counterfactual_exclusivity (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_node : ChoiceNode i t h) (h_feas : α_star ∈ A_feas i t h) :
    ∃ β ∈ foregone_actions i t h α_star,
      End_of i β t h = OpportunityCost i t h α_star h_node h_feas ∧
      Disjoint (ChoicePartition i t α_star) (ChoicePartition i t β) ∧
      ∀ h' : History, ¬ (Exec i t α_star h' ∧ Exec i t β h') := by
  have h_spec := opportunity_cost_spec i t h α_star h_node h_feas
  rcases Finset.mem_image.mp h_spec.1 with ⟨β, hβ, h_beta_eq⟩
  have h_beta_feas : β ∈ A_feas i t h := Finset.mem_of_mem_erase hβ
  have h_ne : β ≠ α_star := (Finset.mem_erase.mp hβ).1
  have h_disj := choice_partition_disjoint i t h h_feas h_beta_feas (Ne.symm h_ne)
  refine ⟨β, hβ, h_beta_eq, h_disj, ?_⟩
  intro h' ⟨h_exec_α, h_exec_β⟩
  exact Set.disjoint_left.mp h_disj h_exec_α h_exec_β

end Praxeology

end
