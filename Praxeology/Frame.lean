module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Praxeology.Frame

Formalization of the ontological primitives and frame conditions for praxeology
and catallactics, following `spec/01_ontology_and_frames.md`.

## Contents
1. Multi-Sorted Signature: `Agent`, `Moment`, `Action`, `Means`, `Ends`.
2. Kripke-Tree Temporal Frame: strict precedence, backward linearity, forward branching, discrete successors.
3. History Bundles and Agency Partitions: STIT choice partitions and independence of agency.
4. Model-Theoretic Semantics: `Exec`, dynamic counterfactual box modality `DynamicBox`, and deliberative STIT `dstit`.
5. Bounded Doxastic State: epistemic information states, minimal plausibility, and DEL updates.
-/

@[expose] public section

namespace Praxeology

-- =========================================================================
-- 1. Multi-Sorted Signature (Σ_prx)
-- =========================================================================

/-- Agent sort: finite, non-empty set of discrete acting entities. -/
axiom Agent : Type
axiom instNonemptyAgent : Nonempty Agent
axiom instFintypeAgent : Fintype Agent
axiom instDecidableEqAgent : DecidableEq Agent
attribute [instance] instNonemptyAgent instFintypeAgent instDecidableEqAgent

/-- Moment sort: discrete points in time equipped with a strict order (<). -/
axiom Moment : Type
axiom instDecidableEqMoment : DecidableEq Moment
attribute [instance] instDecidableEqMoment

/-- Action sort: finite set of elementary intentional choices. -/
axiom Action : Type
axiom instNonemptyAction : Nonempty Action
axiom instFintypeAction : Fintype Action
axiom instDecidableEqAction : DecidableEq Action
attribute [instance] instNonemptyAction instFintypeAction instDecidableEqAction

/-- Distinguished passive/inertial baseline action α₀. -/
axiom alpha_zero : Action
notation "α₀" => alpha_zero

/-- Means sort: discrete physical goods/resources measured in units of ℕ₀. -/
axiom Means : Type
axiom instDecidableEqMeans : DecidableEq Means
attribute [instance] instDecidableEqMeans

/-- Ends sort: discrete teleological goals/states of affairs. -/
axiom Ends : Type
axiom instDecidableEqEnds : DecidableEq Ends
attribute [instance] instDecidableEqEnds

-- =========================================================================
-- 2. Kripke-Tree Temporal Frame (CTL* Branching Time)
-- =========================================================================

/-- Temporal precedence relation (<) on Moment. -/
axiom Precedence : Moment → Moment → Prop

instance : LT Moment where
  lt := Precedence

/-- Precedence is irreflexive. -/
axiom moment_lt_irrefl (t : Moment) : ¬(t < t)

/-- Precedence is transitive. -/
axiom moment_lt_trans {t1 t2 t3 : Moment} : t1 < t2 → t2 < t3 → t1 < t3

/-- Precedence is asymmetric (derived from irreflexivity and transitivity). -/
theorem moment_lt_asymm {t1 t2 : Moment} (h1 : t1 < t2) (h2 : t2 < t1) : False :=
  moment_lt_irrefl t1 (moment_lt_trans h1 h2)

/-- Backward Linearity (Historical Determinism / Fixed Past):
    The past of any moment is strictly linear. -/
axiom backward_linearity (t t1 t2 : Moment) :
  t1 < t → t2 < t → (t1 < t2 ∨ t1 = t2 ∨ t2 < t1)

/-- Forward Branching (Open Future):
    Every moment has at least two distinct future branches. -/
axiom forward_branching (t : Moment) :
  ∃ t1 t2 : Moment, t < t1 ∧ t < t2 ∧ t1 ≠ t2

-- =========================================================================
-- 3. History and History Bundles
-- =========================================================================

/-- A set of moments is a linear chain if all pairs of elements are comparable under (<). -/
def IsLinearChain (s : Set Moment) : Prop :=
  ∀ ⦃t1 t2⦄, t1 ∈ s → t2 ∈ s → (t1 < t2 ∨ t1 = t2 ∨ t2 < t1)

/-- A history is a maximal linear chain in (Moment, <). -/
def IsMaximalLinearChain (s : Set Moment) : Prop :=
  IsLinearChain s ∧ ∀ s', IsLinearChain s' → s ⊆ s' → s = s'

/-- History sort: maximal linear chain of moments. -/
structure History where
  val : Set Moment
  property : IsMaximalLinearChain val

instance : Membership Moment History where
  mem h t := t ∈ h.val

/-- Extensionality for histories: two histories with the same moments are equal. -/
@[ext]
theorem History.ext (h1 h2 : History) (h : h1.val = h2.val) : h1 = h2 := by
  cases h1; cases h2; cases h; rfl

/-- Discrete Successors:
    Every moment in a history has an immediate unique discrete successor in that history. -/
axiom discrete_successors (t : Moment) (h : History) (ht : t ∈ h) :
  ∃! t_succ : Moment, t_succ ∈ h ∧ t < t_succ ∧ ¬∃ τ ∈ h, t < τ ∧ τ < t_succ

/-- Every moment belongs to at least one maximal history. -/
axiom moment_in_history (t : Moment) : ∃ h : History, t ∈ h

/-- The history bundle passing through moment t: H(t) := { h : History | t ∈ h }. -/
def HistoryBundle (t : Moment) : Type :=
  { h : History // t ∈ h }

-- =========================================================================
-- 4. Agency and Choice Partitions (STIT / PDL)
-- =========================================================================

/-- Feasible menu of actions for agent i at ⟨t, h⟩. -/
axiom A_feas (i : Agent) (t : Moment) (h : History) : Finset Action

/-- Feasible menu is historically settled at t: it is invariant across all histories in H(t). -/
axiom A_feas_bundle_invariant (i : Agent) (t : Moment) (h1 h2 : History)
    (h1_t : t ∈ h1) (h2_t : t ∈ h2) :
    A_feas i t h1 = A_feas i t h2

/-- The passive/inertial baseline action α₀ is always feasible. -/
axiom alpha_zero_feasible (i : Agent) (t : Moment) (h : History) :
  α₀ ∈ A_feas i t h

/-- Feasible menu is always non-empty. -/
theorem A_feas_nonempty (i : Agent) (t : Moment) (h : History) :
    (A_feas i t h).Nonempty :=
  ⟨α₀, alpha_zero_feasible i t h⟩

/-- Choice partition cell π_i(t, α) for agent i and action α at moment t. -/
axiom ChoicePartition (i : Agent) (t : Moment) (α : Action) : Set History

/-- Every history in the choice partition cell passes through moment t: π_i(t, α) ⊆ H(t). -/
axiom choice_partition_subset_bundle (i : Agent) (t : Moment) (α : Action) :
  ∀ h ∈ ChoicePartition i t α, t ∈ h

/-- Partition covers the history bundle H(t):
    every history in H(t) realizes some feasible action. -/
axiom choice_partition_cover (i : Agent) (t : Moment) (h : History) (ht : t ∈ h) :
  ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α

/-- Partition cells are mutually disjoint for distinct feasible actions. -/
axiom choice_partition_disjoint (i : Agent) (t : Moment) (h : History)
    {α β : Action} (hα : α ∈ A_feas i t h) (hβ : β ∈ A_feas i t h) (hne : α ≠ β) :
    Disjoint (ChoicePartition i t α) (ChoicePartition i t β)

/-- Partition cells are non-empty for all feasible actions. -/
axiom choice_partition_nonempty (i : Agent) (t : Moment) (h : History)
    {α : Action} (hα : α ∈ A_feas i t h) :
    ∃ h' : History, h' ∈ ChoicePartition i t α

/-- Independence of Agency:
    Simultaneous choices across all acting entities have a non-empty joint intersection in H(t). -/
axiom independence_of_agency (t : Moment) (h : History) (choice : Agent → Action)
    (h_feas : ∀ i : Agent, choice i ∈ A_feas i t h) :
    ∃ h' : History, t ∈ h' ∧ ∀ i : Agent, h' ∈ ChoicePartition i t (choice i)

-- =========================================================================
-- 5. Model-Theoretic Truth Conditions (Exec, DynamicBox, dstit)
-- =========================================================================

/-- Execution Predicate:
    M, ⟨t, h⟩ ⊨ Exec(α) iff h ∈ π_i(t, α). -/
def Exec (i : Agent) (t : Moment) (α : Action) : History → Prop :=
  fun h => h ∈ ChoicePartition i t α

/-- Dynamic Counterfactual Modality [α] ψ at moment t:
    ψ holds on all histories in the choice partition cell of α.
    Non-vacuous counterfactual jumping even if the actual history h ∉ π_i(t, α). -/
def DynamicBox (i : Agent) (t : Moment) (α : Action) (ψ : History → Prop) : Prop :=
  ∀ h' : History, h' ∈ ChoicePartition i t α → ψ h'

/-- Choice Cell Π_i(t, h):
    The unique cell of the agency partition containing history h. -/
def ChoiceCell (i : Agent) (t : Moment) (h : History) : Set History :=
  { h' : History | ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α ∧ h' ∈ ChoicePartition i t α }

/-- Deliberative STIT (dstit):
    M, ⟨t, h⟩ ⊨ [ :i dstit: ] ψ iff
    1. Positive condition: ψ holds on all histories in agent i's choice cell at ⟨t, h⟩.
    2. Negative (deliberative) condition: ψ fails on at least one counterfactual history in H(t). -/
def dstit (i : Agent) (t : Moment) (ψ : History → Prop) (h : History) : Prop :=
  (∀ h' ∈ ChoiceCell i t h, ψ h') ∧
  (∃ h'' : History, t ∈ h'' ∧ ¬ ψ h'')

/-- If h is in the choice partition cell of α, then every history in ChoiceCell i t h
    is also in ChoicePartition i t α. -/
theorem choiceCell_subset_partition (i : Agent) (t : Moment) (h : History)
    {α : Action} (hα : α ∈ A_feas i t h) (hh : h ∈ ChoicePartition i t α) :
    ChoiceCell i t h ⊆ ChoicePartition i t α := by
  intro h' hh'
  rcases hh' with ⟨β, hβ, hh_β, hh'_β⟩
  by_cases h_eq : β = α
  · subst h_eq; exact hh'_β
  · have h_disj := choice_partition_disjoint i t h hβ hα h_eq
    exact False.elim (Set.disjoint_left.mp h_disj hh_β hh)

/-- Deliberative STIT execution implies that the actual history realizes the action. -/
theorem dstit_exec_mem (i : Agent) (t : Moment) (h : History) (α : Action)
    (_h_feas : α ∈ A_feas i t h) (ht : t ∈ h) (h_dstit : dstit i t (Exec i t α) h) :
    Exec i t α h := by
  obtain ⟨β, hβ, hhβ⟩ := choice_partition_cover i t h ht
  have h_in_cell : h ∈ ChoiceCell i t h := ⟨β, hβ, hhβ, hhβ⟩
  have h_pos := h_dstit.1 h h_in_cell
  exact h_pos

-- =========================================================================
-- 6. Doxastic Epistemic Logic (DEL)
-- =========================================================================

/-- Minimal plausibility worlds for agent i at moment t. -/
axiom MinPlausible (i : Agent) (t : Moment) : Set History

/-- Minimal plausibility worlds passing through moment t. -/
axiom min_plausible_subset_bundle (i : Agent) (t : Moment) :
  ∀ h ∈ MinPlausible i t, t ∈ h

/-- Minimal plausibility set is non-empty. -/
axiom min_plausible_nonempty (i : Agent) (t : Moment) :
  (MinPlausible i t).Nonempty

/-- Minimal plausibility worlds localized to ⟨t, h⟩. -/
axiom MinPlausibleAt (i : Agent) (t : Moment) (h : History) : Set History

axiom min_plausible_at_nonempty (i : Agent) (t : Moment) (h : History) :
  (MinPlausibleAt i t h).Nonempty

/-- Subjective Belief B_i ψ at moment t:
    ψ holds on all minimally plausible worlds of agent i at moment t. -/
def Belief (i : Agent) (t : Moment) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ MinPlausible i t, ψ h'

/-- Localized Subjective Belief B_i(t, h) ψ. -/
def BeliefAt (i : Agent) (t : Moment) (h : History) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ MinPlausibleAt i t h, ψ h'

/-- Dynamic Epistemic Event Update:
    Restricts minimal plausibility worlds to those satisfying event ε. -/
def DELUpdate (i : Agent) (t : Moment) (ε : History → Prop) : Set History :=
  { h' ∈ MinPlausible i t | ε h' }

/-- Belief after dynamic epistemic event update [!ε] ψ. -/
def BeliefAfterUpdate (i : Agent) (t : Moment) (ε : History → Prop) (ψ : History → Prop) : Prop :=
  ∀ h' ∈ DELUpdate i t ε, ψ h'

end Praxeology

end
