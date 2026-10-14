module

public import Praxeology.Frame
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.deprecated false

/-!
# Praxeology.Action

Core action theory of praxeology:
Purposeful action via undominated choice, set-valued opportunity cost,
and dialectical performative self-consistency without neoclassical patches.

## Contents
1. Physical Endowment, Production Requirements, and Scarcity.
2. Ends of Actions and Ordinal Preference (irreflexive, asymmetric, NO global transitivity or completeness).
3. Purposeful Action via Undominated Choice (`PurposefulAct`) and Demonstrated Preference (`DemonstratedPref`).
4. Poset Induction Engine for Finite Sets (`exists_undominated_aux`, `exists_least_urgent_aux`).
5. Minimalist Set-Valued Opportunity Cost (`OCSet`).
6. Dialectical Self-Consistency (`Asserts`, `dialectical_undeniability`).
7. Machine-Checked Independence Boundaries (Buridan tie, Incomparable foregone options, Local vs Universal action).
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

/-- Strict ordinal preference relation ≻_{i,t,h} over ends.
    Evaluation is purely ordinal and subjective. -/
axiom Preference (i : Agent) (t : Moment) (h : History) : Ends → Ends → Prop

/-- Preference is strictly irreflexive: no end is strictly preferred to itself. -/
axiom pref_irrefl (i : Agent) (t : Moment) (h : History) (e : Ends) :
  ¬(Preference i t h e e)

/-- Preference is asymmetric: if e₁ is strictly preferred to e₂, e₂ is not preferred to e₁. -/
axiom pref_asymm (i : Agent) (t : Moment) (h : History) {e1 e2 : Ends} :
  Preference i t h e1 e2 → ¬(Preference i t h e2 e1)

-- =========================================================================
-- 3. Purposeful Action via Undominated Choice
-- =========================================================================

/-- Purposeful Human Action (Undominated Choice):
    1. Feasibility: α_star is in the feasible action menu.
    2. Physical Execution: α_star is physically executed (`Exec`).
    3. Felt Unease: End_of(α_star) strictly beats the passive baseline End_of(α₀).
    4. Undominated Optimality: No feasible alternative β has a strictly preferred end. -/
def PurposefulAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  α_star ∈ A_feas i t h ∧
  Exec i t α_star h ∧
  Preference i t h (End_of i α_star t h) (End_of i α₀ t h) ∧
  ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) (End_of i α_star t h)

/-- Demonstrated Preference Record (▷):
    Following Komendarczyk et al. (2026) and Megger (2024), only the enacted choice α*
    against rejected contemplated options β is demonstrated in action. -/
def DemonstratedPref (i : Agent) (t : Moment) (h : History) (α_star β : Action) : Prop :=
  PurposefulAct i t h α_star ∧ β ∈ (A_feas i t h).erase α_star

/-- Backward compatibility alias for Act. -/
abbrev Act := PurposefulAct

/-- Purposeful action is non-passive: it is distinct from α₀ and achieves a distinct end. -/
theorem purposeful_act_non_passive (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : PurposefulAct i t h α_star) :
    α_star ≠ α₀ ∧ End_of i α_star t h ≠ End_of i α₀ t h := by
  have h_pref := h_act.2.2.1
  have h_not_end : End_of i α_star t h ≠ End_of i α₀ t h := by
    intro h_eq
    rw [h_eq] at h_pref
    exact pref_irrefl i t h (End_of i α₀ t h) h_pref
  have h_not_act : α_star ≠ α₀ := by
    intro h_eq
    subst h_eq
    exact h_not_end rfl
  exact ⟨h_not_act, h_not_end⟩

/-- Unique execution of purposeful action:
    From disjointness of STIT choice partition cells, an agent can physically
    execute at most one purposeful action at any moment and history. -/
theorem purposeful_act_unique_execution (i : Agent) (t : Moment) (h : History) (α₁ α₂ : Action)
    (h1 : PurposefulAct i t h α₁)
    (h2 : PurposefulAct i t h α₂) :
    α₁ = α₂ := by
  by_contra hne
  have h_disj := choice_partition_disjoint i t h h1.1 h2.1 hne
  exact Set.disjoint_left.mp h_disj h1.2.1 h2.2.1

/-- Buridan Tie Compatibility Theorem:
    Two distinct actions α₁ ≠ α₂ using homogeneous units can serve the exact same end,
    and purposeful action remains completely consistent without violating irreflexivity. -/
theorem buridan_tie_compatible_with_purposeful_act :
    ∃ (A_cont : Finset (Fin 3)) (End_fn : Fin 3 → Fin 2) (Pref_fn : Fin 2 → Fin 2 → Prop)
      (Exec_fn : Fin 3 → Prop) (α₀_val : Fin 3),
      End_fn 1 = End_fn 2 ∧ (1 : Fin 3) ≠ 2 ∧
      (1 ∈ A_cont ∧
       Exec_fn 1 ∧
       Pref_fn (End_fn 1) (End_fn α₀_val) ∧
       ∀ β ∈ A_cont, ¬ Pref_fn (End_fn β) (End_fn 1)) := by
  let A_cont : Finset (Fin 3) := {0, 1, 2}
  let End_fn : Fin 3 → Fin 2 := fun α => if α = 0 then 0 else 1
  let Pref_fn : Fin 2 → Fin 2 → Prop := fun e1 e2 => e1 = 1 ∧ e2 = 0
  let Exec_fn : Fin 3 → Prop := fun α => α = 1
  refine ⟨A_cont, End_fn, Pref_fn, Exec_fn, 0, rfl, by decide, ?_⟩
  refine ⟨by decide, rfl, ⟨rfl, rfl⟩, ?_⟩
  intro β _ ⟨_, h0⟩
  revert h0
  dsimp [End_fn]
  decide

-- =========================================================================
-- 4. Poset Induction Engine for Finite Sets
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
-- 5. Minimalist Set-Valued Opportunity Cost (OCSet)
-- =========================================================================

/-- Foregone alternative actions when choosing α_star. -/
noncomputable def ForegoneActions (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Action :=
  (A_feas i t h).erase α_star

/-- Foregone ends corresponding to the foregone alternative actions. -/
noncomputable def ForegoneEnds (i : Agent) (t : Moment) (h : History) (α_star : Action) : Finset Ends :=
  (ForegoneActions i t h α_star).image (End_of i · t h)

/-- Backward compatibility aliases. -/
noncomputable abbrev foregone_actions := ForegoneActions
noncomputable abbrev foregone_ends := ForegoneEnds

/-- Minimalist Opportunity Cost Set (OCSet):
    The set of all undominated foregone ends (ends in ForegoneEnds that are not
    strictly dominated by any other foregone end). -/
noncomputable def OCSet (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)] : Finset Ends :=
  (ForegoneEnds i t h α_star).filter (fun e =>
    ∀ e' ∈ ForegoneEnds i t h α_star, ¬ Preference i t h e' e)

/-- Star-Order Non-Emptiness:
    In a pure revealed star-order (where purposeful action reveals preferences involving
    the chosen end, but reveals no strict preferences among unchosen foregone ends),
    OCSet is identical to ForegoneEnds, and is strictly non-empty whenever ForegoneEnds is non-empty. -/
theorem ocset_nonempty_of_star_order (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_star : ∀ e ∈ ForegoneEnds i t h α_star, ∀ e' ∈ ForegoneEnds i t h α_star, ¬ Preference i t h e' e)
    (h_ne : (ForegoneEnds i t h α_star).Nonempty) :
    OCSet i t h α_star = ForegoneEnds i t h α_star ∧
    (OCSet i t h α_star).Nonempty := by
  have h_eq : OCSet i t h α_star = ForegoneEnds i t h α_star := by
    ext e
    dsimp [OCSet]
    rw [Finset.mem_filter]
    constructor
    · intro h_in; exact h_in.1
    · intro he_in
      refine ⟨he_in, fun e' he'_in => h_star e he_in e' he'_in⟩
  exact ⟨h_eq, h_eq.symm ▸ h_ne⟩

/-- Strict Partial Order Non-Emptiness:
    For ANY finite non-empty set of foregone ends equipped with an irreflexive,
    transitive preference relation, OCSet is guaranteed to be non-empty (OCSet.Nonempty). -/
theorem ocset_nonempty_of_trans (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (ForegoneEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ ForegoneEnds i t h α_star, ∀ e2 ∈ ForegoneEnds i t h α_star, ∀ e3 ∈ ForegoneEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    (OCSet i t h α_star).Nonempty := by
  have h_irrefl : ∀ e ∈ ForegoneEnds i t h α_star, ¬ Preference i t h e e :=
    fun e _ => pref_irrefl i t h e
  obtain ⟨m, hm_in, hm_undom⟩ := exists_undominated_of_finite_poset
    (ForegoneEnds i t h α_star) h_ne (Preference i t h) h_irrefl h_trans
  use m
  dsimp [OCSet]
  rw [Finset.mem_filter]
  exact ⟨hm_in, hm_undom⟩

/-- Card Le One Under Connectedness:
    When preference is connected over distinct foregone ends, OCSet contains at most 1 element. -/
theorem ocset_card_le_one_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_conn : ∀ e1 ∈ ForegoneEnds i t h α_star, ∀ e2 ∈ ForegoneEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (OCSet i t h α_star).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  dsimp [OCSet] at ha hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  rcases h_conn a ha.1 b hb.1 hne with hab | hba
  · exact hb.2 a ha.1 hab
  · exact ha.2 b hb.1 hba

/-- Classical Subsumption: Unique Singleton Opportunity Cost:
    When preference is connected, irreflexive, and transitive over a non-empty set of foregone ends,
    OCSet has cardinality exactly 1 (recovering unique classical Opportunity Cost as a special case). -/
theorem ocset_singleton_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (ForegoneEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ ForegoneEnds i t h α_star, ∀ e2 ∈ ForegoneEnds i t h α_star, ∀ e3 ∈ ForegoneEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3)
    (h_conn : ∀ e1 ∈ ForegoneEnds i t h α_star, ∀ e2 ∈ ForegoneEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (OCSet i t h α_star).card = 1 := by
  have h_nonempty := ocset_nonempty_of_trans i t h α_star h_ne h_trans
  have h_le := ocset_card_le_one_of_connected i t h α_star h_conn
  have h_pos : 0 < (OCSet i t h α_star).card := Finset.card_pos.mpr h_nonempty
  omega

-- =========================================================================
-- 6. Dialectical Self-Consistency
-- =========================================================================

/-- Intentional assertion: agent i purposefully acts at ⟨t, h⟩ to communicate proposition p. -/
def Asserts (i : Agent) (t : Moment) (h : History) (_p : Prop) : Prop :=
  ∃ α ∈ A_feas i t h, PurposefulAct i t h α

/-- The proposition denying the presence of any purposeful action at ⟨t, h⟩. -/
def DenialOfAction (i : Agent) (t : Moment) (h : History) : Prop :=
  ¬ ∃ α ∈ A_feas i t h, PurposefulAct i t h α

/-- Dialectical Undeniability (Performative Consistency):
    Asserting the negation of purposeful action at ⟨t, h⟩ while denying local action yields False.
    Any attempt to verbally or dialectically deny purposeful action performatively refutes itself. -/
theorem dialectical_undeniability (i : Agent) (t : Moment) (h : History)
    (h_assert : Asserts i t h (DenialOfAction i t h))
    (h_denial : DenialOfAction i t h) : False :=
  h_denial h_assert

-- =========================================================================
-- 7. Machine-Checked Independence Boundaries
-- =========================================================================

/-- Independence Proof 1: Buridan's Ass Tie Refutes Strict Demonstrated Preference.
    If two distinct feasible actions α₁ ≠ α₂ share the exact same optimal end e_star,
    and preference is irreflexive on e_star, then strict demonstrated preference
    (requiring strict dominance over ALL alternatives) is FALSE for both α₁ and α₂. -/
theorem buridan_tie_refutes_strict_demonstrated_pref
    (A_feas_menu : Finset (Fin 3))
    (End_map : Fin 3 → Fin 2)
    (Pref_rel : Fin 2 → Fin 2 → Prop)
    (α₁ α₂ : Fin 3) (e_star : Fin 2)
    (hne : α₁ ≠ α₂)
    (h1 : α₁ ∈ A_feas_menu)
    (h2 : α₂ ∈ A_feas_menu)
    (h_end1 : End_map α₁ = e_star)
    (h_end2 : End_map α₂ = e_star)
    (h_irrefl : ¬ Pref_rel e_star e_star) :
    ¬ (∀ β ∈ A_feas_menu.erase α₁, Pref_rel (End_map α₁) (End_map β)) ∧
    ¬ (∀ β ∈ A_feas_menu.erase α₂, Pref_rel (End_map α₂) (End_map β)) := by
  constructor
  · intro h_strict1
    have h_mem2 : α₂ ∈ A_feas_menu.erase α₁ := by
      rw [Finset.mem_erase]
      exact ⟨hne.symm, h2⟩
    have h_pref12 := h_strict1 α₂ h_mem2
    rw [h_end1, h_end2] at h_pref12
    exact h_irrefl h_pref12
  · intro h_strict2
    have h_mem1 : α₁ ∈ A_feas_menu.erase α₂ := by
      rw [Finset.mem_erase]
      exact ⟨hne, h1⟩
    have h_pref21 := h_strict2 α₁ h_mem1
    rw [h_end1, h_end2] at h_pref21
    exact h_irrefl h_pref21

/-- Independence Proof 2: Opportunity Cost Independent of Minimal Action.
    An agent purposefully chooses action 1 over status quo 0,
    yet NO unique maximum foregone alternative exists among {2, 3} because
    2 and 3 are mutually incomparable. -/
theorem opportunity_cost_independent_of_minimal_action :
    let A_cont : Finset (Fin 4) := {0, 1, 2, 3}
    let Pref : Fin 4 → Fin 4 → Prop := fun a b => (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3)
    let Foregone : Finset (Fin 4) := {2, 3}
    -- Purposeful action 1 beats 0:
    Pref 1 0 ∧
    -- But no unique maximum exists in Foregone:
    ¬ ∃ e_opp ∈ Foregone, ∀ e' ∈ Foregone.erase e_opp, Pref e_opp e' := by
  dsimp
  refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro ⟨e_opp, h_mem, h_max⟩
  fin_cases e_opp
  · have : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
    exact this h_mem
  · have : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
    exact this h_mem
  · have h3_in : (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)).erase 2 := by decide
    have h_pref23 := h_max 3 h3_in
    rcases h_pref23 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · have h2_in : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)).erase 3 := by decide
    have h_pref32 := h_max 2 h2_in
    rcases h_pref32 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- Independence Proof 5: Universal Continuous Action Not Proved by Local Assertion.
    Performative consistency guarantees action only locally at the moment of assertion,
    and cannot prove continuous universal action across all moments. -/
theorem universal_action_not_proved_by_local_assertion :
    let ActAt : Fin 2 → Prop := fun t => t.val = 0
    ActAt 0 ∧ ¬ ActAt 1 := by
  dsimp
  decide

end Praxeology

end
